/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.M3Interfaces
public import Computational.Proofs.E2E.Dsl.PqxdhSimTypes
public import Computational.Proofs.E2E.Dsl.SmReachInv
import Computational.Proofs.E2E.Dsl.ClampsLossless

/-!
# Auxiliary pure expressions for session start and promoted routing

Defines tag-3 PreKey wire-parser equivalences, bounded list and header helpers over the
driver-state types, initial `sessionSchemeFixedSpk` party and game state constructors, and the
pure promotion guard and instance-creation expressions.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.StartAndExtSmAux

open ReductionDsl (Ty Ops Var Expr Env bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.SM (Pos Record GameState initState)
open CryptoGames.LibsignalSession (Crypto KeyPair PublicKey IdentityKey InitKeys Params
  GhostState SessionState SenderChain ReceiverChain ChainKey MessageKeyGenerator
  currentVersion versionByte initializeInitiatorSession initializeRecipientSession)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes wirePrekey PreKeyMessageFields
  SampledSessionKey initKeysOfSampled paramsIdsWithSpqr
  sessionSchemeFixedSpk BHPrefixCtx BHE2ESmResp ModelDriverBase ModelDriverInstanceMeta
  BHModelInst BHE2EDrvState bhIdKeyOf bhBytesWord bhKeySOf bhDrvSessionInitPrin? bhInitRegId
  bhBaseOpkOk bhE2EGuard bhE2EDrvInstClean bhE2EDrvWon bhE2EInstIkACorr bhE2EFinishStartSpk
  bhPackSmResp bhUnpackSmResp
  bhReadProstVarint bhParseOptPreKeyId bhParseUint32Field bhParseDjbKeyField
  bhParseInnerMsgFieldWithRest bhParseKyberCtField bhDecodePreKeyMsgERaw bhDecodePreKeyMsgE
  bhHdrOfPreKeyMsg bhExpectedPreKeyMsg bhPartneredInnerBytes)
open CryptoVerification.E2E.Costed (e2eSig B PB PU32 U8 U32 U64 BV256 BV512 FinT PK IdKey
  PlainT BinStT GhostStT drKeyT drKeyV drKeyOfV bundleT bundleV bundleOfV hdrT hdrV hdrOfV
  sidT sidV sidOfV keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec prefixCtxT
  ghostPartsT ghostJoinEval recvResultT recvResultEnc recvResultDec
  partyToBool boolToParty smQT smQenc smRT smRdec
  e2eReadProstVarint e2eParseOptPreKeyId e2eParseUint32Field e2eParseDjbKeyField
  e2eParseInnerMsgField e2eParseKyberCtField e2eDecodePreKeyRaw e2eDecodePreKeyMsg
  e2eHdrOfPreKeyMsg e2eExpectedPreKeyMsg e2ePartneredInnerBytes
  E2EPureOp e2ePureOps E2ECryptoOp e2eCryptoOps e2eOps)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  e2eCryptoOp eval_e2eCryptoOp cost_e2eCryptoOp
  drKeyOfV_drKeyV bundleOfV_bundleV bundleV_bundleOfV hdrOfV_hdrV hdrV_hdrOfV
  sidOfV_sidV sidV_sidOfV keyIndQdec_keyIndQenc keyIndRdec_keyIndRenc
  recvResultDec_recvResultEnc recvResultEnc_recvResultDec)
open Computational.Proofs.E2E.Dsl.ClampsLossless (spqrV1InitOp_eval_lossless
  e2ePartneredInnerBytes_lossless e2ePureOps_eval_parsePreKeyWire_lossless)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v cost_v
  eLet eCaseOpt eCaseSum eFind eAny
  orE eval_orE isSomeE eval_isSomeE optMapE eval_optMapE
  bndIkB bndSpkB bndOpkB bndPqB hdrIkA hdrEkA hdrSpkId hdrOpkId hdrPqId hdrKemCt
  e2eKeyIndStateTy e2eKeyIndStateToVal e2eValToKeyIndState
  e2eValToKeyIndState_toVal e2eKeyIndStateToVal_ofVal)
open Computational.Proofs.E2E.Dsl.SmReachInv (GameReachInv SmReachBounded DrvSmReachInv
  dedupComp gameReachInv_initState smReachBounded_initState drvSmReachInv_finishStartSpk)
open Computational.Proofs.E2E.Dsl.M2Interfaces (smQdec smRenc smRdec_smRenc_id
  smRenc_id_eq_bhPackSmResp e2eGsTy e2eGsEnc e2eGsDec)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eMirrorPrinEntryTy e2eMirrorBundleEntryTy
  e2eMirrorOpkEntryTy e2eMirrorSendEntryTy e2eMirrorSendEnc e2eMirrorSendDec
  e2eMirrorBaseTy e2eMirrorBaseEnc e2eMirrorBaseDec
  e2eInstMetaTy e2eInstMetaEnc e2eInstMetaDec
  e2eModelInstTy e2eModelInstEnc e2eModelInstDec
  e2eDrvStateTy e2eDrvStateEnc e2eDrvStateDec
  drvStE drvBitE drvPausedE drvSetStE drvSetBitE
  prefixCtxEnc prefixCtxDec packSmRespEnc unpackSmRespDec
  e2eGameQT e2eGameRT mkTestSessionE mkRevealSpkSkE defaultPrefixCtxE
  DrvMirrorBounded DrvQueryBounded DrvMetaAligned DrvSessionsBounded KeyIndReachBounded)

/-! ## Tag-3 PreKey wire parser equivalences -/

section WireEquiv

theorem e2eReadProstVarint_eq : ∀ bs : List (BitVec 8),
    e2eReadProstVarint bs = bhReadProstVarint bs
  | [] => rfl
  | b :: rest => by
    simp only [e2eReadProstVarint, bhReadProstVarint]
    split_ifs
    · rfl
    · rw [e2eReadProstVarint_eq rest]

theorem e2eParseOptPreKeyId_eq (bs : List (BitVec 8)) :
    e2eParseOptPreKeyId bs = bhParseOptPreKeyId bs := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    simp only [e2eParseOptPreKeyId, bhParseOptPreKeyId, e2eReadProstVarint_eq]

theorem e2eParseUint32Field_eq (k : BitVec 8) (bs : List (BitVec 8)) :
    e2eParseUint32Field k bs = bhParseUint32Field k bs := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    simp only [e2eParseUint32Field, bhParseUint32Field, e2eReadProstVarint_eq]

theorem e2eParseDjbKeyField_eq (k : BitVec 8) (bs : List (BitVec 8)) :
    e2eParseDjbKeyField k bs = bhParseDjbKeyField k bs := by
  unfold e2eParseDjbKeyField bhParseDjbKeyField
  rfl

theorem e2eParseInnerMsgField_eq (bs : List (BitVec 8)) :
    e2eParseInnerMsgField bs = bhParseInnerMsgFieldWithRest bs := by
  rcases bs with _ | ⟨b, rest⟩
  · rfl
  · unfold e2eParseInnerMsgField bhParseInnerMsgFieldWithRest
    by_cases hb : b = 0x22#8
    · subst hb
      simp [e2eReadProstVarint_eq]
    · split <;> simp_all

theorem e2eParseKyberCtField_eq (bs : List (BitVec 8)) :
    e2eParseKyberCtField bs = bhParseKyberCtField bs := by
  unfold e2eParseKyberCtField bhParseKyberCtField
  rfl

theorem e2eDecodePreKeyRaw_eq (c : Bytes) :
    e2eDecodePreKeyRaw c = bhDecodePreKeyMsgERaw c := by
  unfold e2eDecodePreKeyRaw bhDecodePreKeyMsgERaw
  rcases c with _ | ⟨t, _ | ⟨ver, proto⟩⟩
  · rfl
  · rfl
  · simp only [e2eParseOptPreKeyId_eq, e2eParseDjbKeyField_eq, e2eParseInnerMsgField_eq,
      e2eParseUint32Field_eq, e2eParseKyberCtField_eq]

@[simp] theorem e2eDecodePreKeyMsg_eq (c : Bytes) :
    e2eDecodePreKeyMsg c = bhDecodePreKeyMsgE c := by
  unfold e2eDecodePreKeyMsg bhDecodePreKeyMsgE
  rw [e2eDecodePreKeyRaw_eq]
  cases bhDecodePreKeyMsgERaw c <;> rfl

@[simp] theorem e2eHdrOfPreKeyMsg_eq (m : PreKeyMessageFields) :
    e2eHdrOfPreKeyMsg m = bhHdrOfPreKeyMsg m := rfl

@[simp] theorem e2eExpectedPreKeyMsg_eq (regIdA : BitVec 32)
    (hdr : SignalPqxdh.HandshakeHdr) (inner : Bytes) :
    e2eExpectedPreKeyMsg regIdA hdr inner = bhExpectedPreKeyMsg regIdA hdr inner := rfl

theorem e2ePartneredInnerBytes_false_eq (regIdA : BitVec 32)
    (hdr : SignalPqxdh.HandshakeHdr) (c : Bytes) :
    e2ePartneredInnerBytes false regIdA hdr c = bhPartneredInnerBytes false regIdA hdr c := by
  rw [e2ePartneredInnerBytes_lossless]
  unfold bhPartneredInnerBytes
  simp only [Bool.not_false, ↓reduceIte, e2eDecodePreKeyMsg_eq, e2eExpectedPreKeyMsg_eq]
  cases bhDecodePreKeyMsgE c <;> rfl

end WireEquiv

/-! ## Field projections, bounded list helpers, and header equality -/

section ListAndHdrHelpers

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "E2EExpr" => Expr (e2eOps ℓ P C K decT encT)

def mbPrins {O : Ops (e2eSig ℓ)} {Γ} (ds : Expr O Γ (e2eMirrorBaseTy S ℓ)) :
    Expr O Γ (.list (e2eMirrorPrinEntryTy S)) := .fst ds
def mbBundles {O : Ops (e2eSig ℓ)} {Γ} (ds : Expr O Γ (e2eMirrorBaseTy S ℓ)) :
    Expr O Γ (.list (e2eMirrorBundleEntryTy S)) := .fst (.snd ds)
def mbOpks {O : Ops (e2eSig ℓ)} {Γ} (ds : Expr O Γ (e2eMirrorBaseTy S ℓ)) :
    Expr O Γ (.list (e2eMirrorOpkEntryTy S)) := .fst (.snd (.snd ds))
def mbSends {O : Ops (e2eSig ℓ)} {Γ} (ds : Expr O Γ (e2eMirrorBaseTy S ℓ)) :
    Expr O Γ (.list (e2eMirrorSendEntryTy S ℓ)) := .snd (.snd (.snd ds))

def imBobAccepted {O : Ops (e2eSig ℓ)} {Γ} (im : Expr O Γ (e2eInstMetaTy S ℓ)) :
    Expr O Γ .bool := .fst im
def imIkACorr {O : Ops (e2eSig ℓ)} {Γ} (im : Expr O Γ (e2eInstMetaTy S ℓ)) :
    Expr O Γ .bool := .fst (.snd im)

def miSid {O : Ops (e2eSig ℓ)} {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) :
    Expr O Γ (sidT S) := .fst d
def miHdr {O : Ops (e2eSig ℓ)} {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) :
    Expr O Γ hdrT := .fst (.snd d)
def miIdA {O : Ops (e2eSig ℓ)} {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) :
    Expr O Γ IdKey := .fst (.snd (.snd d))
def miIdB {O : Ops (e2eSig ℓ)} {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) :
    Expr O Γ IdKey := .fst (.snd (.snd (.snd d)))
def miSpkCoins {O : Ops (e2eSig ℓ)} {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) :
    Expr O Γ BV256 := .fst (.snd (.snd (.snd (.snd d))))
def miGs {O : Ops (e2eSig ℓ)} {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) :
    Expr O Γ (.opt (e2eGsTy ℓ)) := .snd (.snd (.snd (.snd (.snd d))))

def miSetGsE {O : Ops (e2eSig ℓ)} {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ))
    (gs? : Expr O Γ (.opt (e2eGsTy ℓ))) : Expr O Γ (e2eModelInstTy S ℓ) :=
  eLet (.pair d gs?) fun p =>
    .pair (miSid (.fst (v p))) (.pair (miHdr (.fst (v p))) (.pair (miIdA (.fst (v p)))
      (.pair (miIdB (.fst (v p))) (.pair (miSpkCoins (.fst (v p))) (.snd (v p))))))

def drvBase {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (e2eMirrorBaseTy S ℓ) := .fst σ
def drvCorrPrins {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (.list (FinT S.N_id)) := .fst (.snd σ)
def drvRevSpks {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (.list (.prod (FinT S.N_id) (FinT S.N_recv))) := .fst (.snd (.snd σ))
def drvInsts {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (.list (e2eModelInstTy S ℓ)) := .fst (.snd (.snd (.snd σ)))
def drvInstMeta {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (.list (e2eInstMetaTy S ℓ)) := .fst (.snd (.snd (.snd (.snd σ))))
def drvSt {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) := .fst (.snd (.snd (.snd (.snd (.snd σ)))))
def drvB {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd σ))))))
def drvPaused {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ .bool := .snd (.snd (.snd (.snd (.snd (.snd (.snd σ))))))

def drvSetInstsAndMetaE {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ))
    (insts : Expr O Γ (.list (e2eModelInstTy S ℓ)))
    (metaL : Expr O Γ (.list (e2eInstMetaTy S ℓ))) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σ (.pair insts metaL)) fun p =>
    .pair (drvBase (.fst (v p))) (.pair (drvCorrPrins (.fst (v p)))
      (.pair (drvRevSpks (.fst (v p)))
        (.pair (.fst (.snd (v p)))
          (.pair (.snd (.snd (v p)))
            (.snd (.snd (.snd (.snd (.snd (.fst (v p)))))))))))

def drvSetInstMetaE {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ))
    (metaL : Expr O Γ (.list (e2eInstMetaTy S ℓ))) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σ metaL) fun p =>
    .pair (drvBase (.fst (v p))) (.pair (drvCorrPrins (.fst (v p)))
      (.pair (drvRevSpks (.fst (v p)))
        (.pair (drvInsts (.fst (v p)))
          (.pair (.snd (v p))
            (.snd (.snd (.snd (.snd (.snd (.fst (v p)))))))))))

def drvSetInstsAndPausedE {O : Ops (e2eSig ℓ)} {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ))
    (insts : Expr O Γ (.list (e2eModelInstTy S ℓ)))
    (pausedE : Expr O Γ .bool) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σ (.pair insts pausedE)) fun p =>
    .pair (drvBase (.fst (v p))) (.pair (drvCorrPrins (.fst (v p)))
      (.pair (drvRevSpks (.fst (v p)))
        (.pair (.fst (.snd (v p)))
          (.pair (drvInstMeta (.fst (v p)))
            (.pair (drvSt (.fst (v p)))
              (.pair (drvB (.fst (v p))) (.snd (.snd (v p)))))))))

@[simp] theorem eval_miSetGsE {O : Ops (e2eSig ℓ)} {Γ}
    (dE : Expr O Γ (e2eModelInstTy S ℓ)) (gsE : Expr O Γ (.opt (e2eGsTy ℓ))) (ρ : Env Γ)
    {d : BHModelInst S ℓ} {gs? : Option (GameState (GhostState Bytes) (Plain ℓ) Bytes)}
    (hd : dE.eval ρ = e2eModelInstEnc d) (hgs : gsE.eval ρ = gs?.map e2eGsEnc) :
    (miSetGsE dE gsE).eval ρ = e2eModelInstEnc { d with gs := gs? } := by
  simp only [miSetGsE, miSid, miHdr, miIdA, miIdB, miSpkCoins, eLet, v, Ext.wk,
    Expr.eval, Env.get, hd, hgs, e2eModelInstEnc]

@[simp] theorem eval_drvSetInstMetaE {O : Ops (e2eSig ℓ)} {Γ}
    (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (metaE : Expr O Γ (.list (e2eInstMetaTy S ℓ))) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {ms : List (ModelDriverInstanceMeta S)}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hm : metaE.eval ρ = ms.map e2eInstMetaEnc) :
    (drvSetInstMetaE σE metaE).eval ρ = e2eDrvStateEnc { σ with instMeta := ms } := by
  simp only [drvSetInstMetaE, drvBase, drvCorrPrins, drvRevSpks, drvInsts,
    eLet, v, Ext.wk, Expr.eval, Env.get, hσ, hm, e2eDrvStateEnc]

@[simp] theorem eval_drvSetInstsAndPausedE {O : Ops (e2eSig ℓ)} {Γ}
    (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (instsE : Expr O Γ (.list (e2eModelInstTy S ℓ)))
    (pausedE : Expr O Γ .bool) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {ds : List (BHModelInst S ℓ)}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hds : instsE.eval ρ = ds.map e2eModelInstEnc) :
    (drvSetInstsAndPausedE σE instsE pausedE).eval ρ =
      e2eDrvStateEnc { σ with insts := ds, paused := pausedE.eval ρ } := by
  simp only [drvSetInstsAndPausedE, drvBase, drvCorrPrins, drvRevSpks,
    drvInstMeta, drvSt, drvB, eLet, v, Ext.wk, Expr.eval, Env.get, hσ, hds, e2eDrvStateEnc]

def listSnocE (K : ℕ) {O : Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (xs : Expr O Γ (.list τ)) (x : Expr O Γ τ) : Expr O Γ (.list τ) :=
  .appendL (K + 1) xs (.cons x .nil)

@[simp] theorem eval_listSnocE (K : ℕ) {O : Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (xs : Expr O Γ (.list τ)) (x : Expr O Γ τ) (ρ : Env Γ)
    (hlen : (xs.eval ρ).length ≤ K) :
    (listSnocE K xs x).eval ρ = xs.eval ρ ++ [x.eval ρ] := by
  have h1 : (xs.eval ρ ++ [x.eval ρ]).length ≤ K + 1 := by simp; omega
  simp only [listSnocE, Expr.eval, List.take_of_length_le h1]

private def foldGetStep {α : Type} (idx total : ℕ) (x : α) (acc : ℕ × Option α) : ℕ × Option α :=
  (acc.1 + 1, if idx + (acc.1 + 1) = total then some x else acc.2)

private theorem foldr_foldGetStep_fst {α : Type} (idx total : ℕ) :
    ∀ (l : List α), (l.foldr (foldGetStep idx total) (0, none)).1 = l.length
  | [] => rfl
  | _ :: xs => by simp [List.foldr, foldGetStep, foldr_foldGetStep_fst idx total xs]

private theorem foldr_foldGetStep_snd {α : Type} :
    ∀ (l : List α) (idx off : ℕ),
      (l.foldr (foldGetStep (idx + off) (l.length + off)) (0, none)).2 = l[idx]?
  | [], _, _ => by simp
  | x :: xs, 0, off => by
    simp only [List.foldr, foldGetStep, foldr_foldGetStep_fst, List.length_cons, Nat.zero_add]
    have heq : off + (xs.length + 1) = xs.length + 1 + off := by omega
    simp [heq]
  | _ :: xs, idx + 1, off => by
    simp only [List.foldr, foldGetStep, foldr_foldGetStep_fst, List.length_cons]
    have hne : idx + 1 + off + (xs.length + 1) ≠ xs.length + 1 + off := by omega
    simp only [hne, ↓reduceIte]
    rw [show idx + 1 + off = idx + (off + 1) by omega,
        show xs.length + 1 + off = xs.length + (off + 1) by omega]
    exact foldr_foldGetStep_snd xs idx (off + 1)

def listGetOptE (K : ℕ) {O : Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) : Expr O Γ (.opt τ) :=
  eLet (.pair l (.pair idx (.len l))) fun p =>
    .snd (.foldrB K (.fst (v p)) (.pair (.nat 0) .none)
      (.pair (.add (.fst .v1) (.nat 1))
        (.ite (.eqN (.add (.fst (.snd .v2)) (.add (.fst .v1) (.nat 1))) (.snd (.snd .v2)))
          (.some .v0) (.snd .v1))))

@[simp] theorem eval_listGetOptE (K : ℕ) {O : Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (listGetOptE K l idx).eval ρ = (l.eval ρ)[idx.eval ρ]? := by
  simp only [listGetOptE, eLet, v, Ext.wk, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get, List.take_of_length_le hlen]
  have hstep :
      (List.foldr
        (fun x acc =>
          (acc.1 + 1,
            if decide (idx.eval ρ + (acc.1 + 1) = (l.eval ρ).length) = true then some x
            else acc.2))
        (0, none) (l.eval ρ)) =
      (l.eval ρ).foldr (foldGetStep (idx.eval ρ) (l.eval ρ).length) (0, none) := by
    congr 1; funext x acc; simp [foldGetStep]
  rw [hstep]
  simpa using foldr_foldGetStep_snd (l.eval ρ) (idx.eval ρ) 0

theorem cost_listGetOptE (K : ℕ) {O : Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) :
    (listGetOptE K l idx).cost ≤ 2 * l.cost + idx.cost + 32 * K + 20 := by
  simp only [listGetOptE, eLet, Expr.cost, cost_v, Expr.v0, Expr.v1, Expr.v2, bits,
    show Nat.log 2 0 = 0 from rfl, show Nat.log 2 1 = 0 from rfl, Nat.reduceAdd,
    show max 2 2 = 2 from rfl]
  omega

attribute [local irreducible] listGetOptE

private def foldSetStep {α : Type} (idx total : ℕ) (val x : α) (acc : ℕ × List α) : ℕ × List α :=
  (acc.1 + 1, (if idx + (acc.1 + 1) = total then val else x) :: acc.2)

private theorem foldr_foldSetStep_fst {α : Type} (idx total : ℕ) (val : α) :
    ∀ (l : List α), (l.foldr (foldSetStep idx total val) (0, [])).1 = l.length
  | [] => rfl
  | _ :: xs => by simp [List.foldr, foldSetStep, foldr_foldSetStep_fst idx total val xs]

private theorem foldr_foldSetStep_id {α : Type} (val : α) :
    ∀ (l : List α) (idx total : ℕ), l.length < total → total ≤ idx + total →
      (∀ k < l.length, idx + (k + 1) ≠ total) →
      (l.foldr (foldSetStep idx total val) (0, [])).2 = l
  | [], _, _, _, _, _ => rfl
  | x :: xs, idx, total, hlt, hge, hne => by
    simp only [List.foldr, foldSetStep, foldr_foldSetStep_fst]
    have h0 : idx + (xs.length + 1) ≠ total := hne xs.length (by simp)
    simp only [h0, ↓reduceIte]
    congr 1
    exact foldr_foldSetStep_id val xs idx total
      (by simp at hlt; omega) hge (fun k hk => hne k (by simp; omega))

private theorem foldr_foldSetStep_snd {α : Type} (val : α) :
    ∀ (l : List α) (idx off : ℕ),
      (l.foldr (foldSetStep (idx + off) (l.length + off) val) (0, [])).2 = l.set idx val
  | [], _, _ => rfl
  | _ :: xs, 0, off => by
    simp only [List.foldr, foldSetStep, foldr_foldSetStep_fst, List.length_cons, Nat.zero_add,
      List.set_cons_zero]
    have heq : off + (xs.length + 1) = xs.length + 1 + off := by omega
    simp only [heq, ↓reduceIte]
    congr 1
    exact foldr_foldSetStep_id val xs off (xs.length + 1 + off)
      (by omega) (by omega) (fun _ _ => by omega)
  | x :: xs, idx + 1, off => by
    simp only [List.foldr, foldSetStep, foldr_foldSetStep_fst, List.length_cons, List.set_cons_succ]
    have hne : idx + 1 + off + (xs.length + 1) ≠ xs.length + 1 + off := by omega
    simp only [hne, ↓reduceIte]
    congr 1
    rw [show idx + 1 + off = idx + (off + 1) by omega,
        show xs.length + 1 + off = xs.length + (off + 1) by omega]
    exact foldr_foldSetStep_snd val xs idx (off + 1)

def listSetE (K : ℕ) {O : Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (val : Expr O Γ τ) : Expr O Γ (.list τ) :=
  eLet (.pair l (.pair idx (.pair val (.len l)))) fun p =>
    .snd (.foldrB K (.fst (v p)) (.pair (.nat 0) .nil)
      (.pair (.add (.fst .v1) (.nat 1))
        (.cons
          (.ite (.eqN (.add (.fst (.snd .v2)) (.add (.fst .v1) (.nat 1)))
                      (.snd (.snd (.snd .v2))))
            (.fst (.snd (.snd .v2))) .v0)
          (.snd .v1))))

@[simp] theorem eval_listSetE (K : ℕ) {O : Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (val : Expr O Γ τ) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (listSetE K l idx val).eval ρ = (l.eval ρ).set (idx.eval ρ) (val.eval ρ) := by
  simp only [listSetE, eLet, v, Ext.wk, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get, List.take_of_length_le hlen]
  have hstep :
      (List.foldr
        (fun x acc =>
          (acc.1 + 1,
            (if decide (idx.eval ρ + (acc.1 + 1) = (l.eval ρ).length) = true then val.eval ρ
             else x) :: acc.2))
        (0, []) (l.eval ρ)) =
      (l.eval ρ).foldr (foldSetStep (idx.eval ρ) (l.eval ρ).length (val.eval ρ)) (0, []) := by
    congr 1; funext x acc; simp [foldSetStep]
  rw [hstep]
  simpa using foldr_foldSetStep_snd (val.eval ρ) (l.eval ρ) (idx.eval ρ) 0

theorem cost_listSetE (K : ℕ) {O : Ops (e2eSig ℓ)} {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (val : Expr O Γ τ) :
    (listSetE K l idx val).cost ≤ 2 * l.cost + idx.cost + val.cost + 36 * K + 24 := by
  simp only [listSetE, eLet, Expr.cost, cost_v, Expr.v0, Expr.v1, Expr.v2, bits,
    show Nat.log 2 0 = 0 from rfl, show Nat.log 2 1 = 0 from rfl, Nat.reduceAdd,
    show max 4 1 = 4 from rfl]
  omega

attribute [local irreducible] listSetE

def e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) : E2EExpr Γ .bool :=
  eLet (.pair a b) fun p =>
    eCaseSum (.fst (v p))
      (fun a1 => eCaseSum (.snd (v p))
        (fun b1 => .and
          (e2ePureOp (.finEq S.N_id) (.pair (.fst (v a1)) (.fst (v b1))))
          (e2ePureOp (.finEq S.N_send_opk) (.pair (.snd (v a1)) (.snd (v b1)))))
        (fun _ => .bool false))
      (fun ar => eCaseSum (.snd (v p))
        (fun _ => .bool false)
        (fun br => eCaseSum (v ar)
          (fun a2 => eCaseSum (v br)
            (fun b2 => .and
              (e2ePureOp (.finEq S.N_id) (.pair (.fst (v a2)) (.fst (v b2))))
              (e2ePureOp (.finEq S.N_send_no_opk) (.pair (.snd (v a2)) (.snd (v b2)))))
            (fun _ => .bool false))
          (fun ar2 => eCaseSum (v br)
            (fun _ => .bool false)
            (fun br2 => eCaseSum (v ar2)
              (fun a3 => eCaseSum (v br2)
                (fun b3 => .and
                  (e2ePureOp (.finEq S.N_id) (.pair (.fst (v a3)) (.fst (v b3))))
                  (.and
                    (e2ePureOp (.finEq S.N_recv) (.pair (.fst (.snd (v a3))) (.fst (.snd (v b3)))))
                    (e2ePureOp (.finEq S.N_opk) (.pair (.snd (.snd (v a3))) (.snd (.snd (v b3)))))))
                (fun _ => .bool false))
              (fun a4 => eCaseSum (v br2)
                (fun _ => .bool false)
                (fun b4 => .and
                  (e2ePureOp (.finEq S.N_id) (.pair (.fst (v a4)) (.fst (v b4))))
                  (.and
                    (e2ePureOp (.finEq S.N_recv) (.pair (.fst (.snd (v a4))) (.fst (.snd (v b4)))))
                    (e2ePureOp (.finEq S.N_no_opk)
                      (.pair (.snd (.snd (v a4))) (.snd (.snd (v b4))))))))))))

@[simp] theorem eval_e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) (ρ : Env Γ) :
    (e2eSidEqE a b).eval ρ = (sidOfV (a.eval ρ) == sidOfV (b.eval ρ)) := by
  rcases ha : a.eval ρ with ⟨u1, i1⟩ | ⟨u1, i1⟩ | ⟨k1, j1, o1⟩ | ⟨k1, j1, l1⟩ <;>
  rcases hb : b.eval ρ with ⟨u2, i2⟩ | ⟨u2, i2⟩ | ⟨k2, j2, o2⟩ | ⟨k2, j2, l2⟩ <;>
  simp only [e2eSidEqE, sidOfV, eLet, eCaseSum, v, Ext.wk,
    Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get, ha, hb]
  · rw [Bool.eq_iff_iff]; simp [beq_iff_eq]
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [Bool.eq_iff_iff]; simp [beq_iff_eq]
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [Bool.eq_iff_iff]; simp [beq_iff_eq]
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [Bool.eq_iff_iff]; simp [beq_iff_eq]

theorem cost_e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) :
    (e2eSidEqE a b).cost ≤ a.cost + b.cost + 80 := by
  simp only [e2eSidEqE, eLet, eCaseSum, Expr.cost, cost_v, cost_e2ePureOp, E2EPureOp.cost]
  omega

attribute [local irreducible] e2eSidEqE

def optPu32EqE {Γ} (a b : E2EExpr Γ (.opt PU32)) : E2EExpr Γ .bool :=
  eLet (.pair a b) fun p =>
    eCaseOpt (.fst (v p))
      (eCaseOpt (.snd (v p)) (.bool true) (fun _ => .bool false))
      (fun x => eCaseOpt (.snd (v p)) (.bool false)
        (fun y => e2ePureOp .pu32Eq (.pair (v x) (v y))))

@[simp] theorem eval_optPu32EqE {Γ} (a b : E2EExpr Γ (.opt PU32)) (ρ : Env Γ) :
    (optPu32EqE a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  rcases ha : a.eval ρ with _ | x <;> rcases hb : b.eval ρ with _ | y <;>
    simp only [optPu32EqE, eLet, eCaseOpt, v, Ext.wk,
      Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get, ha, hb]
  · rfl
  · rfl
  · rfl
  · rw [Bool.eq_iff_iff]; simp [beq_iff_eq]

def hdrEqE {Γ} (a b : E2EExpr Γ hdrT) : E2EExpr Γ .bool :=
  eLet (.pair a b) fun p =>
    .and
      (.and
        (e2ePureOp (.pbytesEq 32 32) (.pair (hdrIkA (.fst (v p))) (hdrIkA (.snd (v p)))))
        (e2ePureOp (.pbytesEq 32 32) (.pair (hdrEkA (.fst (v p))) (hdrEkA (.snd (v p))))))
      (.and
        (.and
          (e2ePureOp .pu32Eq (.pair (hdrSpkId (.fst (v p))) (hdrSpkId (.snd (v p)))))
          (optPu32EqE (hdrOpkId (.fst (v p))) (hdrOpkId (.snd (v p)))))
        (.and
          (e2ePureOp .pu32Eq (.pair (hdrPqId (.fst (v p))) (hdrPqId (.snd (v p)))))
          (e2ePureOp (.pbytesEq 1568 1568) (.pair (hdrKemCt (.fst (v p))) (hdrKemCt (.snd (v p)))))))

@[simp] theorem eval_hdrEqE {Γ} (a b : E2EExpr Γ hdrT) (ρ : Env Γ) :
    (hdrEqE a b).eval ρ = (hdrOfV (a.eval ρ) == hdrOfV (b.eval ρ)) := by
  rcases ha : a.eval ρ with ⟨ik1, ek1, s1, o1, p1, k1⟩
  rcases hb : b.eval ρ with ⟨ik2, ek2, s2, o2, p2, k2⟩
  simp only [hdrEqE, hdrOfV, hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
    eLet, v, Ext.wk, Expr.eval, eval_optPu32EqE,
    eval_e2ePureOp, E2EPureOp.eval, Env.get, ha, hb]
  rw [Bool.eq_iff_iff]
  simp [beq_iff_eq, SignalPqxdh.HandshakeHdr.mk.injEq, and_assoc]

theorem cost_hdrEqE {Γ} (a b : E2EExpr Γ hdrT) :
    (hdrEqE a b).cost ≤ a.cost + b.cost + 3400 := by
  simp only [hdrEqE, optPu32EqE, hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
    eLet, eCaseOpt, Expr.cost, cost_v, cost_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat]
  omega

attribute [local irreducible] hdrEqE

def bhDrvSessionInitPrinE {Γ} (sidE : E2EExpr Γ (sidT S)) : E2EExpr Γ (.opt (FinT S.N_id)) :=
  eCaseSum sidE
    (fun ui => .some (.fst (v ui)))
    (fun r => eCaseSum (v r) (fun ui => .some (.fst (v ui))) (fun _ => .none))

@[simp] theorem eval_bhDrvSessionInitPrinE {Γ} (sidE : E2EExpr Γ (sidT S)) (ρ : Env Γ) :
    (bhDrvSessionInitPrinE sidE).eval ρ = bhDrvSessionInitPrin? (sidOfV (sidE.eval ρ)) := by
  rcases h : sidE.eval ρ with ⟨u, _⟩ | ⟨u, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    simp only [bhDrvSessionInitPrinE, bhDrvSessionInitPrin?, sidOfV, eCaseSum,
      v, Ext.wk, Expr.eval, Env.get, h]

def bhInitRegIdE {Γ} (sidE : E2EExpr Γ (sidT S)) : E2EExpr Γ U32 :=
  eCaseOpt (bhDrvSessionInitPrinE sidE)
    (e2ePureOp (.u32Lit 0#32) .unit)
    (fun u => e2ePureOp .u32OfNat (e2ePureOp (.finVal S.N_id) (v u)))

@[simp] theorem eval_bhInitRegIdE {Γ} (sidE : E2EExpr Γ (sidT S)) (ρ : Env Γ) :
    (bhInitRegIdE sidE).eval ρ = bhInitRegId (sidOfV (sidE.eval ρ)) := by
  simp only [bhInitRegIdE, bhInitRegId, eCaseOpt, Expr.eval, eval_bhDrvSessionInitPrinE]
  rcases bhDrvSessionInitPrin? (sidOfV (sidE.eval ρ)) with _ | u <;>
    simp only [v, Ext.wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get]

end ListAndHdrHelpers

/-! ## Initial `sessionSchemeFixedSpk` party and game state expressions -/

section SessionInit

variable {ℓ : ℕ} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "E2EExpr" => Expr (e2eOps ℓ P C K decT encT)

private theorem keyVec_roundtrip (vec : List.Vector (BitVec 8) 32) :
    keyToBytesVec32 (bytesToKey32 vec.toList) = vec :=
  Computational.Proofs.E2E.Dsl.DrSessionSimHooks.keyVec_bytesToKey32_vec vec

private theorem spqrV1InitOp_eval_eq (isAlice : Bool) (pqrKey : BitVec 256) :
    E2ECryptoOp.eval ℓ P C K .spqrV1InitOp (isAlice, pqrKey) =
      spqrV1Init C.F K (if isAlice then .a2b else .b2a) pqrKey :=
  spqrV1InitOp_eval_lossless ℓ P C K isAlice pqrKey

/-- Construct Bob's initial `GhostState Bytes` for `sessionSchemeFixedSpk` from
`((idA, idB), (spkCoins, ((rk, ck), pqrKey)))`. -/
def initFixedSpkBobE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (keysE : E2EExpr Γ (.prod BV256 (.prod (.prod BV256 BV256) BV256))) :
    E2EExpr Γ GhostStT :=
  eLet (.pair idsE keysE) fun p =>
    eLet (e2eCryptoOp .sessionKeyPairGen (.fst (.snd (v p)))) fun kpB =>
      eLet (e2eCryptoOp .spqrV1InitOp
          (.pair (.bool false) (.snd (.snd (.snd (v p)))))) fun pqSt =>
        e2ePureOp .ghostStateJoin
          (.pair (.bool true)
            (.pair (e2ePureOp (.u32Lit (BitVec.ofNat 32 currentVersion.toNat)) .unit)
              (.pair (.snd (.fst (v p)))
                (.pair (.some (.fst (.fst (v p))))
                  (.pair (.fst (.fst (.snd (.snd (v p)))))
                    (.pair (e2ePureOp (.u32Lit 0#32) .unit)
                      (.pair (.bool false)
                        (.pair (.nat 0)
                          (.pair .nil
                            (.pair (.some (.pair (v kpB)
                                      (.pair (.snd (.fst (.snd (.snd (v p)))))
                                        (e2ePureOp (.u32Lit 0#32) .unit))))
                              (.pair .nil (v pqSt))))))))))))

@[simp] theorem eval_initFixedSpkBobE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (keysE : E2EExpr Γ (.prod BV256 (.prod (.prod BV256 BV256) BV256)))
    (ρ : Env Γ) (ac : BitVec 256) :
    let (idA, idB) := idsE.eval ρ
    let (spkCoins, ((rk, ck), pqrKey)) := keysE.eval ρ
    (initFixedSpkBobE idsE keysE).eval ρ =
      (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).initB
        ((rk, ck), (ac, pqrKey)) := by
  rcases hids : idsE.eval ρ with ⟨idA, idB⟩
  rcases hkeys : keysE.eval ρ with ⟨spkCoins, ⟨⟨rk, ck⟩, pqrKey⟩⟩
  simp only [initFixedSpkBobE, eLet, v, Ext.wk, Expr.eval, Env.get,
    hids, hkeys, eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval]
  rw [spqrV1InitOp_eval_eq]
  dsimp only [E2ECryptoOp.eval, ghostJoinEval, Option.map, List.take, List.map, boolToParty,
    sessionSchemeFixedSpk, paramsIdsWithSpqr, Params.initB, initKeysOfSampled,
    initializeRecipientSession, SessionState.setSenderChain, SessionState.new,
    spqrV1SessionUniformCoins]
  have hkp : KeyPair.mk (KeyPair.generate C spkCoins).publicKey
      ⟨keyToBytesVec32
        (bytesToKey32 (KeyPair.generate C spkCoins).privateKey.bytes.toList)⟩ =
      KeyPair.generate C spkCoins := by
    cases hgen : KeyPair.generate C spkCoins with
    | mk pub priv =>
      cases priv with
      | mk bs => simp [keyVec_roundtrip]
  rw [hkp]
  rfl

theorem cost_initFixedSpkBobE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (keysE : E2EExpr Γ (.prod BV256 (.prod (.prod BV256 BV256) BV256))) :
    (initFixedSpkBobE idsE keysE).cost ≤ idsE.cost + keysE.cost + 31300 := by
  simp only [initFixedSpkBobE, eLet, Expr.cost, cost_v,
    cost_e2eCryptoOp, E2ECryptoOp.cost, cost_e2ePureOp, E2EPureOp.cost,
    bits, show Nat.log 2 0 = 0 from rfl]
  omega

attribute [local irreducible] initFixedSpkBobE

/-- Construct Alice's initial `GhostState Bytes` for `sessionSchemeFixedSpk` from
`((idA, idB), (spkCoins, (((rk, ck), (ac, pqrKey)))))`. -/
def initFixedSpkAliceE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (keysE : E2EExpr Γ (.prod BV256 (.prod (.prod BV256 BV256) (.prod BV256 BV256)))) :
    E2EExpr Γ GhostStT :=
  eLet (.pair idsE keysE) fun p =>
    eLet (.pair
        (.fst (e2eCryptoOp .sessionKeyPairGen (.fst (.snd (v p)))))
        (.pair
          (e2eCryptoOp .sessionKeyPairGen (.fst (.snd (.snd (.snd (v p))))))
          (e2eCryptoOp .spqrV1InitOp
            (.pair (.bool true) (.snd (.snd (.snd (.snd (v p))))))))) fun mid =>
      eCaseOpt
        (e2eCryptoOp .sessionRootCreateChain
          (.pair (.fst (.fst (.snd (.snd (v p)))))
            (.pair (.fst (v mid)) (.snd (.fst (.snd (v mid)))))))
        (e2ePureOp .ghostStateJoin
          (.pair (.bool false)
            (.pair (e2ePureOp (.u32Lit (BitVec.ofNat 32 currentVersion.toNat)) .unit)
              (.pair (.fst (.fst (v p)))
                (.pair (.some (.snd (.fst (v p))))
                  (.pair (.fst (.fst (.snd (.snd (v p)))))
                    (.pair (e2ePureOp (.u32Lit 0#32) .unit)
                      (.pair (.bool true)
                        (.pair (.nat 0)
                          (.pair (.cons (.nat 0) .nil)
                            (.pair .none
                              (.pair
                                (.cons
                                  (.pair (.fst (v mid))
                                    (.pair
                                      (.some (.pair (.snd (.fst (.snd (.snd (v p)))))
                                        (e2ePureOp (.u32Lit 0#32) .unit)))
                                      .nil))
                                  .nil)
                                (.snd (.snd (v mid)))))))))))))))
        (fun rc =>
          e2ePureOp .ghostStateJoin
            (.pair (.bool false)
              (.pair (e2ePureOp (.u32Lit (BitVec.ofNat 32 currentVersion.toNat)) .unit)
                (.pair (.fst (.fst (v p)))
                  (.pair (.some (.snd (.fst (v p))))
                    (.pair (.fst (v rc))
                      (.pair (e2ePureOp (.u32Lit 0#32) .unit)
                        (.pair (.bool true)
                          (.pair (.nat 0)
                            (.pair (.cons (.nat 0) .nil)
                              (.pair (.some (.pair (.fst (.snd (v mid)))
                                        (.pair (.snd (v rc))
                                          (e2ePureOp (.u32Lit 0#32) .unit))))
                                (.pair
                                  (.cons
                                    (.pair (.fst (v mid))
                                      (.pair
                                        (.some (.pair (.snd (.fst (.snd (.snd (v p)))))
                                          (e2ePureOp (.u32Lit 0#32) .unit)))
                                        .nil))
                                    .nil)
                                  (.snd (.snd (v mid)))))))))))))))

@[simp] theorem eval_initFixedSpkAliceE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (keysE : E2EExpr Γ (.prod BV256 (.prod (.prod BV256 BV256) (.prod BV256 BV256))))
    (ρ : Env Γ) :
    let (idA, idB) := idsE.eval ρ
    let (spkCoins, kS) := keysE.eval ρ
    (initFixedSpkAliceE idsE keysE).eval ρ =
      (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).initA kS := by
  rcases hids : idsE.eval ρ with ⟨idA, idB⟩
  rcases hkeys : keysE.eval ρ with ⟨spkCoins, ⟨⟨rk, ck⟩, ⟨ac, pqrKey⟩⟩⟩
  simp only [initFixedSpkAliceE, eLet, eCaseOpt, v, Ext.wk,
    Expr.eval, Env.get, hids, hkeys, eval_e2eCryptoOp, eval_e2ePureOp, E2EPureOp.eval]
  rw [spqrV1InitOp_eval_eq]
  dsimp only [E2ECryptoOp.eval, sessionSchemeFixedSpk, paramsIdsWithSpqr, Params.initA,
    initKeysOfSampled, initializeInitiatorSession, spqrV1SessionUniformCoins]
  have hpriv : CryptoGames.LibsignalSession.PrivateKey.mk (keyToBytesVec32
      (bytesToKey32 (KeyPair.generate C ac).privateKey.bytes.toList)) =
      (KeyPair.generate C ac).privateKey := by
    cases h : (KeyPair.generate C ac).privateKey with
    | mk bs => simp [keyVec_roundtrip]
  rw [hpriv]
  have h5 : ¬ (CryptoGames.LibsignalSession.maxReceiverChains < 1) := by
    decide
  cases hrc : CryptoGames.LibsignalSession.rootCreateChain C rk
      (KeyPair.generate C spkCoins).publicKey (KeyPair.generate C ac).privateKey with
  | error e =>
    dsimp only [Except.bind]
    simp [ghostJoinEval, boolToParty, SessionState.new, SessionState.addReceiverChain,
      SessionState.setUnacknowledgedPreKeyMessage, h5]
  | ok pair =>
    rcases pair with ⟨rk', ckSend⟩
    cases ckSend with
    | mk ckSendKey ckSendIdx =>
      have hidx : ckSendIdx = 0#32 := by
        unfold CryptoGames.LibsignalSession.rootCreateChain at hrc
        split at hrc <;> simp_all
      subst hidx
      dsimp only [Except.bind, Pure.pure, Except.pure]
      simp [ghostJoinEval, boolToParty, SessionState.new, SessionState.addReceiverChain,
        SessionState.setSenderChain, SessionState.setUnacknowledgedPreKeyMessage, h5]

theorem cost_initFixedSpkAliceE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (keysE : E2EExpr Γ (.prod BV256 (.prod (.prod BV256 BV256) (.prod BV256 BV256)))) :
    (initFixedSpkAliceE idsE keysE).cost ≤ idsE.cost + keysE.cost + 62500 := by
  simp only [initFixedSpkAliceE, eLet, eCaseOpt, Expr.cost, cost_v,
    cost_e2eCryptoOp, E2ECryptoOp.cost, cost_e2ePureOp, E2EPureOp.cost,
    bits, show Nat.log 2 0 = 0 from rfl]
  omega

attribute [local irreducible] initFixedSpkAliceE

/-- Construct the initial encoded `SM.GameState` (`e2eGsTy ℓ`) for `sessionSchemeFixedSpk` from
`((idA, idB), (spkCoins, (kS, b)))`. -/
def initFixedSpkGsE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (argE : E2EExpr Γ (.prod BV256
      (.prod (.prod (.prod BV256 BV256) (.prod BV256 BV256)) .bool))) :
    E2EExpr Γ (e2eGsTy ℓ) :=
  eLet (.pair idsE argE) fun p =>
    .pair
      (.pair
        (initFixedSpkAliceE (.fst (v p))
          (.pair (.fst (.snd (v p))) (.fst (.snd (.snd (v p))))))
        (initFixedSpkBobE (.fst (v p))
          (.pair (.fst (.snd (v p)))
            (.pair (.fst (.fst (.snd (.snd (v p)))))
              (.snd (.snd (.fst (.snd (.snd (v p))))))))))
      (.pair (.snd (.snd (.snd (v p))))
        (.pair (.bool false)
          (.pair (.pair (.nat 0) (.nat 0))
            (.pair (.pair (.nat 0) (.nat 0))
              (.pair .none
                (.pair .nil
                  (.pair .nil
                    (.pair .nil
                      (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0)))
                        (.pair .nil .nil))))))))))

@[simp] theorem eval_initFixedSpkGsE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (argE : E2EExpr Γ (.prod BV256
      (.prod (.prod (.prod BV256 BV256) (.prod BV256 BV256)) .bool)))
    (ρ : Env Γ) :
    let (idA, idB) := idsE.eval ρ
    let (spkCoins, (kS, b)) := argE.eval ρ
    (initFixedSpkGsE idsE argE).eval ρ =
      e2eGsEnc (initState
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).sendPart
        kS b) := by
  rcases hids : idsE.eval ρ with ⟨idA, idB⟩
  rcases harg : argE.eval ρ with ⟨spkCoins, ⟨⟨⟨rk, ck⟩, ⟨ac, pqrKey⟩⟩, b⟩⟩
  simp only [initFixedSpkGsE, eLet, v, Ext.wk, Expr.eval, Env.get, hids, harg]
  have ha := eval_initFixedSpkAliceE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst (.var .zero)) (.pair (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))))
    (.cons ((idA, idB), (spkCoins, (((rk, ck), (ac, pqrKey)), b))) ρ)
  have hb := eval_initFixedSpkBobE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst (.var .zero))
    (.pair (.fst (.snd (.var .zero)))
      (.pair (.fst (.fst (.snd (.snd (.var .zero)))))
        (.snd (.snd (.fst (.snd (.snd (.var .zero))))))))
    (.cons ((idA, idB), (spkCoins, (((rk, ck), (ac, pqrKey)), b))) ρ) ac
  dsimp only [Expr.eval, Env.get] at ha hb
  rw [ha, hb]
  rfl

theorem cost_initFixedSpkGsE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (argE : E2EExpr Γ (.prod BV256
      (.prod (.prod (.prod BV256 BV256) (.prod BV256 BV256)) .bool))) :
    (initFixedSpkGsE idsE argE).cost ≤ idsE.cost + argE.cost + 93900 := by
  let τ0 : Ty (e2eSig ℓ) :=
    .prod (.prod IdKey IdKey)
      (.prod BV256 (.prod (.prod (.prod BV256 BV256) (.prod BV256 BV256)) .bool))
  have ha := cost_initFixedSpkAliceE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τ0 :: Γ)
    (.fst (.var .zero))
    (.pair (.fst (.snd (.var .zero))) (.fst (.snd (.snd (.var .zero)))))
  have hb := cost_initFixedSpkBobE (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τ0 :: Γ)
    (.fst (.var .zero))
    (.pair (.fst (.snd (.var .zero)))
      (.pair (.fst (.fst (.snd (.snd (.var .zero)))))
        (.snd (.snd (.fst (.snd (.snd (.var .zero))))))))
  unfold initFixedSpkGsE
  dsimp only [v, Ext.wk]
  simp only [eLet, Expr.cost, bits, show Nat.log 2 0 = 0 from rfl] at ha hb ⊢
  omega

theorem smReachBounded_initFixedSpkGsE {Γ}
    (idsE : E2EExpr Γ (.prod IdKey IdKey))
    (argE : E2EExpr Γ (.prod BV256
      (.prod (.prod (.prod BV256 BV256) (.prod BV256 BV256)) .bool)))
    (ρ : Env Γ) :
    SmReachBounded C K 0 (e2eGsDec ((initFixedSpkGsE idsE argE).eval ρ)) := by
  rcases hids : idsE.eval ρ with ⟨idA, idB⟩
  rcases harg : argE.eval ρ with ⟨spkCoins, ⟨kS, b⟩⟩
  have hev := eval_initFixedSpkGsE idsE argE ρ
  simp only [hids, harg] at hev
  rw [hev]
  have hdec :
      e2eGsDec (e2eGsEnc (initState
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).sendPart
        kS b)) =
      initState
        (sessionSchemeFixedSpk
          (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).sendPart
        kS b := by
    dsimp only [initState, e2eGsEnc, e2eGsDec, dedupComp, List.map]
    congr 1 <;> first | rfl | (funext p; cases p <;> rfl)
  rw [hdec]
  exact smReachBounded_initState C K idA idB ℓ spkCoins kS b

attribute [local irreducible] initFixedSpkGsE

end SessionInit

/-! ## Promotion guard and pure `finishStartSpk` combinators -/

section StartPure

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "E2EExpr" => Expr (e2eOps ℓ P C K decT encT)

def bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (uE : E2EExpr Γ (FinT S.N_id)) (jE : E2EExpr Γ (FinT S.N_recv))
    (bndE : E2EExpr Γ bundleT) : E2EExpr Γ .bool :=
  eLet (.pair dsE (.pair uE (.pair jE bndE))) fun p =>
    eCaseOpt (bndOpkB (.snd (.snd (.snd (v p)))))
      (.bool true)
      (fun opkPair =>
        eAny nOpks (mbOpks (.fst (v p))) fun e =>
          .and
            (.and
              (e2ePureOp (.finEq S.N_id)
                (.pair (.fst (.fst (v e))) (.fst (.snd (v p)))))
              (e2ePureOp (.finEq S.N_recv)
                (.pair (.fst (.snd (.fst (v e)))) (.fst (.snd (.snd (v p)))))))
            (.and
              (.and
                (e2ePureOp .pu32Eq
                  (.pair
                    (e2ePureOp .pu32OfNat
                      (e2ePureOp (.finVal S.N_opk) (.snd (.snd (.fst (v e))))))
                    (.fst (v opkPair))))
                (.eqN
                  (e2ePureOp (.finVal S.N_opk) (.snd (.snd (.fst (v e)))))
                  (e2ePureOp .pu32ToNat (.fst (v opkPair)))))
              (e2ePureOp (.pbytesEq 32 32)
                (.pair (.snd (v e)) (.snd (v opkPair))))))

@[simp] theorem eval_bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (uE : E2EExpr Γ (FinT S.N_id)) (jE : E2EExpr Γ (FinT S.N_recv))
    (bndE : E2EExpr Γ bundleT) (ρ : Env Γ) {ds : ModelDriverBase S}
    (hds : dsE.eval ρ = e2eMirrorBaseEnc ds) (hOpks : ds.opks.length ≤ nOpks) :
    (bhBaseOpkOkE nOpks dsE uE jE bndE).eval ρ =
      bhBaseOpkOk ds (uE.eval ρ) (jE.eval ρ) (bundleOfV (bndE.eval ρ)) := by
  rcases hbnd : bndE.eval ρ with ⟨ikB, spkId, spkB, spkSig, opkB?, pqspkId, pqspkB, pqspkSig⟩
  simp only [bhBaseOpkOkE, bhBaseOpkOk, bundleOfV, bndOpkB, mbOpks, e2eMirrorBaseEnc,
    eLet, eCaseOpt, eAny, v, Ext.wk, Expr.eval, Env.get, hds, hbnd]
  cases opkB? with
  | none => rfl
  | some pair =>
    rcases pair with ⟨opkId, opkPk⟩
    simp only [Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get, List.take_of_length_le hOpks]
    apply List.any_congr rfl
    rintro ⟨⟨u', j', o'⟩, pk⟩
    rw [Bool.eq_iff_iff]
    simp [beq_iff_eq, and_assoc]

theorem cost_bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (uE : E2EExpr Γ (FinT S.N_id)) (jE : E2EExpr Γ (FinT S.N_recv))
    (bndE : E2EExpr Γ bundleT) :
    (bhBaseOpkOkE nOpks dsE uE jE bndE).cost ≤
      dsE.cost + uE.cost + jE.cost + bndE.cost + 144 * nOpks + 32 := by
  simp only [bhBaseOpkOkE, bndOpkB, mbOpks, eLet, eCaseOpt, eAny,
    Expr.cost, cost_v, cost_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat]
  omega

attribute [local irreducible] bhBaseOpkOkE

def guardFindBundleE (nBundles : ℕ) {Γ}
    (bundlesE : E2EExpr Γ (.list (e2eMirrorBundleEntryTy S)))
    (bndE : E2EExpr Γ bundleT) (hdrE : E2EExpr Γ hdrT) :
    E2EExpr Γ (.opt (.prod (FinT S.N_id) (FinT S.N_recv))) :=
  eLet (.pair bundlesE (.pair bndE hdrE)) fun p =>
    optMapE
      (eFind nBundles (.fst (v p)) fun e =>
        .and
          (.and
            (e2ePureOp (.pbytesEq 32 32)
              (.pair (.fst (.snd (v e))) (bndSpkB (.fst (.snd (v p))))))
            (e2ePureOp (.pbytesEq 1568 1568)
              (.pair (.snd (.snd (v e))) (bndPqB (.fst (.snd (v p)))))))
          (.and
            (e2ePureOp .pu32Eq
              (.pair (hdrSpkId (.snd (.snd (v p))))
                     (e2ePureOp .pu32OfNat
                       (e2ePureOp (.finVal S.N_recv) (.snd (.fst (v e)))))))
            (e2ePureOp .pu32Eq
              (.pair (hdrPqId (.snd (.snd (v p))))
                     (e2ePureOp .pu32OfNat
                       (e2ePureOp (.finVal S.N_recv) (.snd (.fst (v e)))))))))
      (fun e => .fst (v e))

def guardCheckPrinOpkE (nPrins nOpks : ℕ) {Γ}
    (baseE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (ujE : E2EExpr Γ (.prod (FinT S.N_id) (FinT S.N_recv)))
    (bndE : E2EExpr Γ bundleT) : E2EExpr Γ .bool :=
  eLet (.pair baseE (.pair ujE bndE)) fun p =>
    .and
      (eAny nPrins (mbPrins (.fst (v p))) fun e =>
        .and
          (e2ePureOp (.finEq S.N_id) (.pair (.fst (v e)) (.fst (.fst (.snd (v p))))))
          (e2ePureOp (.pbytesEq 32 32) (.pair (.snd (v e)) (bndIkB (.snd (.snd (v p)))))))
      (bhBaseOpkOkE nOpks (.fst (v p))
        (.fst (.fst (.snd (v p)))) (.snd (.fst (.snd (v p)))) (.snd (.snd (v p))))

theorem cost_guardFindBundleE (nBundles : ℕ) {Γ}
    (bundlesE : E2EExpr Γ (.list (e2eMirrorBundleEntryTy S)))
    (bndE : E2EExpr Γ bundleT) (hdrE : E2EExpr Γ hdrT) :
    (guardFindBundleE nBundles bundlesE bndE hdrE).cost ≤
      bundlesE.cost + bndE.cost + hdrE.cost + 3300 * nBundles + 20 := by
  unfold guardFindBundleE
  dsimp only [v, Ext.wk]
  simp only [bndSpkB, bndPqB, hdrSpkId, hdrPqId, optMapE, eLet, eCaseOpt, eFind,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat]
  omega

theorem cost_guardCheckPrinOpkE (nPrins nOpks : ℕ) {Γ}
    (baseE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (ujE : E2EExpr Γ (.prod (FinT S.N_id) (FinT S.N_recv)))
    (bndE : E2EExpr Γ bundleT) :
    (guardCheckPrinOpkE nPrins nOpks baseE ujE bndE).cost ≤
      baseE.cost + ujE.cost + bndE.cost + 84 * nPrins + 144 * nOpks + 60 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (e2eMirrorBaseTy S ℓ) (.prod (.prod (FinT S.N_id) (FinT S.N_recv)) bundleT)
  have hopk := cost_bhBaseOpkOkE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nOpks (Γ := τp :: Γ)
    (.fst (.var .zero)) (.fst (.fst (.snd (.var .zero))))
    (.snd (.fst (.snd (.var .zero)))) (.snd (.snd (.var .zero)))
  dsimp only [τp] at hopk
  unfold guardCheckPrinOpkE
  dsimp only [v, Ext.wk]
  simp only [mbPrins, bndIkB, eLet, eAny, Expr.cost, cost_e2ePureOp,
    E2EPureOp.cost, PNat.val_ofNat] at hopk ⊢
  omega

def guardCorrOkE (nCorr : ℕ) {Γ}
    (corrE : E2EExpr Γ (.list (FinT S.N_id))) (uE : E2EExpr Γ (FinT S.N_id))
    (bndE : E2EExpr Γ bundleT) : E2EExpr Γ .bool :=
  eLet (.pair corrE (.pair uE (bndOpkB bndE))) fun p =>
    eCaseOpt (.snd (.snd (v p)))
      (.not (eAny nCorr (.fst (v p)) fun c =>
        e2ePureOp (.finEq S.N_id) (.pair (.fst (.snd (v p))) (v c))))
      (fun _ => .bool true)

theorem eval_guardCorrOkE (nCorr : ℕ) {Γ}
    (corrE : E2EExpr Γ (.list (FinT S.N_id))) (uE : E2EExpr Γ (FinT S.N_id))
    (bndE : E2EExpr Γ bundleT) (ρ : Env Γ)
    {corr : List (Fin S.N_id)} {u : Fin S.N_id} {bnd : SignalPqxdh.PreKeyBundleInput}
    (hc : corrE.eval ρ = corr) (hu : uE.eval ρ = u) (hbnd : bndE.eval ρ = bundleV bnd)
    (hlen : corr.length ≤ nCorr) :
    (guardCorrOkE nCorr corrE uE bndE).eval ρ = (bnd.opkB?.isSome || !corr.contains u) := by
  simp only [guardCorrOkE, eLet, eCaseOpt, eAny, bndOpkB, bundleV,
    v, Ext.wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get, hc, hu, hbnd]
  rw [List.take_of_length_le hlen, List.contains_eq_any_beq]
  rcases bnd.opkB? with _ | ⟨_, _⟩ <;> rfl

theorem cost_guardCorrOkE (nCorr : ℕ) {Γ}
    (corrE : E2EExpr Γ (.list (FinT S.N_id))) (uE : E2EExpr Γ (FinT S.N_id))
    (bndE : E2EExpr Γ bundleT) :
    (guardCorrOkE nCorr corrE uE bndE).cost ≤
      corrE.cost + uE.cost + bndE.cost + 16 * nCorr + 32 := by
  unfold guardCorrOkE
  dsimp only [v, Ext.wk]
  simp only [bndOpkB, eLet, eCaseOpt, eAny, Expr.cost, cost_e2ePureOp, E2EPureOp.cost]
  omega

private theorem find_congr_all {α : Type} (l : List α) {p : α → Bool} (q : α → Bool)
    (h : ∀ x, p x = q x) : l.find? p = l.find? q := by
  congr 1; funext x; exact h x

private theorem any_congr_all {α : Type} (l : List α) {p : α → Bool} (q : α → Bool)
    (h : ∀ x, p x = q x) : l.any p = l.any q := by
  congr 1; funext x; exact h x

/-- Promotion guard `bhE2EGuard` over `e2eDrvStateTy S ℓ`. -/
def bhE2EGuardE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    E2EExpr Γ (.opt (.prod hdrT (.prod bundleT (.prod (FinT S.N_id) (FinT S.N_recv))))) :=
  eLet (.pair σE sidE) fun ps =>
    .ite (eAny qStart (drvInsts (.fst (v ps))) fun d =>
            e2eSidEqE (miSid (v d)) (.snd (v ps)))
      .none
      (eCaseOpt
        (eFind nSends (mbSends (drvBase (.fst (v ps)))) fun sbh =>
          e2eSidEqE (.fst (v sbh)) (.snd (v ps)))
        .none
        (fun sbh =>
          .ite (eAny qStart (drvInsts (.fst (v ps))) fun d =>
                  e2ePureOp (.pbytesEq 32 32)
                    (.pair (hdrEkA (miHdr (v d))) (hdrEkA (.snd (.snd (v sbh))))))
            .none
            (eCaseOpt
              (guardFindBundleE nBundles (mbBundles (drvBase (.fst (v ps))))
                (.fst (.snd (v sbh))) (.snd (.snd (v sbh))))
              .none
              (fun uj =>
                .ite (.and (guardCheckPrinOpkE nPrins nOpks (drvBase (.fst (v ps)))
                        (v uj) (.fst (.snd (v sbh))))
                      (guardCorrOkE nPrins (drvCorrPrins (.fst (v ps))) (.fst (v uj))
                        (.fst (.snd (v sbh)))))
                  (.some (.pair (.snd (.snd (v sbh))) (.pair (.fst (.snd (v sbh))) (v uj))))
                  .none))))

@[simp] theorem eval_bhE2EGuardE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart) (hPrins : σ.prins.length ≤ nPrins)
    (hBundles : σ.bundles.length ≤ nBundles) (hOpks : σ.opks.length ≤ nOpks)
    (hSends : σ.sends.length ≤ nSends) (hCorr : σ.corrPrins.length ≤ nPrins) :
    (bhE2EGuardE qStart nPrins nBundles nOpks nSends σE sidE).eval ρ =
      (bhE2EGuard σ (sidOfV (sidE.eval ρ))).map
        (fun (hdr, bnd, uj) => (hdrV hdr, (bundleV bnd, uj))) := by
  set sid := sidOfV (sidE.eval ρ)
  have hInsts' : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by simp [hInsts]
  have hSends' : (σ.sends.map (e2eMirrorSendEnc (ℓ := ℓ))).length ≤ nSends := by simp [hSends]
  have hDrvInsts : (e2eDrvStateEnc σ).2.2.2.1 = σ.insts.map e2eModelInstEnc := rfl
  have hDrvBase : (e2eDrvStateEnc σ).1 = e2eMirrorBaseEnc σ.toModelDriverBase := rfl
  have hMbSends :
      (e2eMirrorBaseEnc (ℓ := ℓ) σ.toModelDriverBase).2.2.2 =
        σ.sends.map e2eMirrorSendEnc := rfl
  simp only [bhE2EGuardE, bhE2EGuard, eLet, eCaseOpt, eAny, eFind, drvInsts, drvBase,
    mbSends, mbBundles, v, Ext.wk, Expr.eval, Env.get, hσ, hDrvInsts, hDrvBase, hMbSends,
    List.take_of_length_le hInsts', List.take_of_length_le hSends',
    List.any_map, List.find?_map, Function.comp_def]
  conv_lhs =>
    rw [any_congr_all σ.insts (fun d => d.sid == sid) (fun d => by
      simp only [eval_e2eSidEqE, miSid, e2eModelInstEnc, Expr.eval, Env.get, sidOfV_sidV, sid])]
  cases hdup : σ.insts.any (fun d => d.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    conv_lhs =>
      rw [find_congr_all σ.sends (fun x => x.1 == sid) (fun ⟨s, bnd, hdr⟩ => by
        simp only [eval_e2eSidEqE, e2eMirrorSendEnc, Expr.eval, Env.get, sidOfV_sidV, sid])]
    conv_rhs =>
      rw [find_congr_all σ.sends (fun x => x.1 == sid) (fun ⟨_, _, _⟩ => rfl)]
    rcases hs : σ.sends.find? (fun x => x.1 == sid) with _ | ⟨s0, bnd, hdr⟩
    · rw [hs]; rfl
    · rw [hs]; dsimp only [Option.map]
      conv_lhs =>
        rw [any_congr_all σ.insts (fun d => d.hdr.ekAPk == hdr.ekAPk) (fun d => by
          simp only [miHdr, hdrEkA, hdrV, e2eModelInstEnc, e2eMirrorSendEnc,
            eval_e2ePureOp, E2EPureOp.eval, Expr.eval, Env.get])]
      cases hek : σ.insts.any (fun d => d.hdr.ekAPk == hdr.ekAPk)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hTakeBnd : List.take nBundles (e2eDrvStateEnc σ).1.2.1 = σ.bundles := by
          simp [e2eDrvStateEnc, e2eMirrorBaseEnc, List.take_of_length_le hBundles]
        simp only [guardFindBundleE, eLet, eval_optMapE, eFind, bndSpkB, bndPqB,
          hdrSpkId, hdrPqId, v, Ext.wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get,
          hTakeBnd]
        let pBnd :
            ((Fin S.N_id × Fin S.N_recv) × (SignalPqxdh.Bytes × SignalPqxdh.Bytes)) → Bool :=
          fun x =>
            x.2.1 == bnd.spkB && x.2.2 == bnd.pqspkB &&
            hdr.spkId == UInt32.ofNat x.1.2.val &&
            hdr.pqspkId == UInt32.ofNat x.1.2.val
        conv_lhs =>
          rw [find_congr_all σ.bundles pBnd (fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => by
            simp only [pBnd, e2eMirrorSendEnc, bundleV, hdrV, Bool.and_assoc])]
        conv_rhs =>
          rw [find_congr_all σ.bundles pBnd (fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => by
            simp only [pBnd, Bool.and_assoc])]
        rcases hb : σ.bundles.find? pBnd with _ | ⟨⟨u, j⟩, _⟩
        · rfl
        · dsimp only [Option.map]
          have hChk :
              (guardCheckPrinOpkE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
                nPrins nOpks
                (Expr.var Var.zero.succ.succ).fst.fst (Expr.var Var.zero)
                (Expr.var Var.zero.succ).snd.fst).eval
                (Env.cons (u, j)
                  (Env.cons (e2eMirrorSendEnc (s0, bnd, hdr))
                    (Env.cons (e2eDrvStateEnc σ, sidE.eval ρ) ρ))) =
              (σ.prins.any (fun x => x.1 == u && x.2 == bnd.ikB) &&
                bhBaseOpkOk σ.toModelDriverBase u j bnd) := by
            simp only [guardCheckPrinOpkE, eLet, eAny, mbPrins, bndIkB,
              hDrvBase, e2eMirrorBaseEnc, e2eMirrorSendEnc,
              v, Ext.wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get,
              List.take_of_length_le hPrins]
            conv_lhs =>
              rw [any_congr_all σ.prins (fun x => x.1 == u && x.2 == bnd.ikB)
                (fun ⟨_, _⟩ => by simp only [bundleV])]
            rw [eval_bhBaseOpkOkE nOpks _ _ _ _ _
              (by simp only [Expr.eval, Env.get, e2eMirrorBaseEnc]) hOpks]
            simp only [Expr.eval, Env.get, bundleOfV_bundleV]
          rw [hChk, eval_guardCorrOkE (corr := σ.corrPrins) (u := u) (bnd := bnd)
            (Γ := (FinT S.N_id).prod (FinT S.N_recv) :: e2eMirrorSendEntryTy S ℓ ::
              (e2eDrvStateTy S ℓ).prod (sidT S) :: Γ)
            nPrins (drvCorrPrins (Expr.var Var.zero.succ.succ).fst) (Expr.var Var.zero).fst
            (Expr.var Var.zero.succ).snd.fst
            (Env.cons (u, j)
              (Env.cons (e2eMirrorSendEnc (s0, bnd, hdr))
                (Env.cons (e2eDrvStateEnc σ, sidE.eval ρ) ρ)))
            rfl rfl rfl hCorr]
          conv_rhs =>
            rw [any_congr_all σ.prins (fun x => x.1 == u && x.2 == bnd.ikB)
              (fun ⟨_, _⟩ => rfl)]
          rw [Bool.and_assoc]
          cases (σ.prins.any (fun x => x.1 == u && x.2 == bnd.ikB) &&
            (bhBaseOpkOk σ.toModelDriverBase u j bnd &&
              (bnd.opkB?.isSome || !σ.corrPrins.contains u)))
          · rfl
          · simp only [↓reduceIte, e2eMirrorSendEnc]
      · rfl
  · rfl

theorem cost_bhE2EGuardE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    (bhE2EGuardE qStart nPrins nBundles nOpks nSends σE sidE).cost ≤
      σE.cost + sidE.cost + 170 * qStart + 96 * nSends + 3300 * nBundles +
        100 * nPrins + 144 * nOpks + 200 := by
  let τps : Ty (e2eSig ℓ) := .prod (e2eDrvStateTy S ℓ) (sidT S)
  let τsbh : Ty (e2eSig ℓ) := e2eMirrorSendEntryTy S ℓ
  let τuj : Ty (e2eSig ℓ) := .prod (FinT S.N_id) (FinT S.N_recv)
  have hs0 := cost_e2eSidEqE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := e2eModelInstTy S ℓ :: τps :: Γ)
    (miSid (.var .zero)) (.snd (.var (.succ .zero)))
  have hs1 := cost_e2eSidEqE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τsbh :: τps :: Γ)
    (.fst (.var .zero)) (.snd (.var (.succ .zero)))
  have hfb := cost_guardFindBundleE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nBundles (Γ := τsbh :: τps :: Γ)
    (mbBundles (drvBase (.fst (.var (.succ .zero)))))
    (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  have hcp := cost_guardCheckPrinOpkE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nPrins nOpks (Γ := τuj :: τsbh :: τps :: Γ)
    (drvBase (.fst (.var (.succ (.succ .zero)))))
    (.var .zero) (.fst (.snd (.var (.succ .zero))))
  have hcc := cost_guardCorrOkE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nPrins (Γ := τuj :: τsbh :: τps :: Γ)
    (drvCorrPrins (.fst (.var (.succ (.succ .zero))))) (.fst (.var .zero))
    (.fst (.snd (.var (.succ .zero))))
  unfold bhE2EGuardE
  dsimp only [v, Ext.wk, τps, τsbh, τuj, e2eMirrorSendEntryTy, e2eModelInstTy,
    e2eMirrorBaseTy, e2eDrvStateTy] at hs0 hs1 hfb hcp hcc ⊢
  simp only [drvInsts, drvBase, drvCorrPrins, mbSends, mbBundles, miSid, miHdr, hdrEkA,
    eLet, eCaseOpt, eAny, eFind, Expr.cost, cost_e2ePureOp, E2EPureOp.cost,
    PNat.val_ofNat] at hs0 hs1 hfb hcp hcc ⊢
  have hq := Nat.mul_le_mul_left qStart (Nat.add_le_add_right hs0 1)
  have hns := Nat.mul_le_mul_left nSends (Nat.add_le_add_right hs1 1)
  omega

attribute [local irreducible] bhE2EGuardE

def prepStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    E2EExpr Γ (.opt (.prod (FinT S.N_id) (FinT S.N_recv))) :=
  optMapE (bhE2EGuardE qStart nPrins nBundles nOpks nSends σE sidE)
    (fun x => .snd (.snd (v x)))

@[simp] theorem eval_prepStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart) (hPrins : σ.prins.length ≤ nPrins)
    (hBundles : σ.bundles.length ≤ nBundles) (hOpks : σ.opks.length ≤ nOpks)
    (hSends : σ.sends.length ≤ nSends) (hCorr : σ.corrPrins.length ≤ nPrins) :
    (prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE).eval ρ =
      (bhE2EGuard σ (sidOfV (sidE.eval ρ))).map (fun (_, _, uj) => uj) := by
  simp only [prepStartSpkE, eval_optMapE,
    eval_bhE2EGuardE qStart nPrins nBundles nOpks nSends σE sidE ρ hσ
      hInsts hPrins hBundles hOpks hSends hCorr]
  rcases bhE2EGuard σ (sidOfV (sidE.eval ρ)) with _ | ⟨_, _, uj⟩ <;>
    simp only [Option.map, v, Ext.wk, Expr.eval, Env.get]

theorem cost_prepStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    (prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE).cost ≤
      σE.cost + sidE.cost + 170 * qStart + 96 * nSends + 3300 * nBundles +
        100 * nPrins + 144 * nOpks + 208 := by
  have hg := cost_bhE2EGuardE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends σE sidE
  simp only [prepStartSpkE, optMapE, eCaseOpt, Expr.cost, cost_v]
  omega

attribute [local irreducible] prepStartSpkE

def extractDrKey32E {Γ} (krE : E2EExpr Γ keyIndRT) :
    E2EExpr Γ (.opt (.prod (.prod BV256 BV256) BV256)) :=
  eCaseSum krE (fun _ => .none) fun r1 =>
  eCaseSum (v r1) (fun _ => .none) fun r2 =>
  eCaseSum (v r2) (fun _ => .none) fun r3 =>
  eCaseSum (v r3) (fun _ => .none) fun r4 =>
  eCaseSum (v r4) (fun _ => .none) fun r5 =>
  eCaseSum (v r5) (fun _ => .none) fun r6 =>
  eCaseSum (v r6) (fun _ => .none) fun r7 =>
  eCaseSum (v r7) (fun _ => .none) fun r8 =>
  eCaseSum (v r8)
    (fun dk =>
      .ite (.and
              (.and
                (.eqN (e2ePureOp (.pbytesLen 32) (.fst (v dk))) (.nat 32))
                (.eqN (e2ePureOp (.pbytesLen 32) (.fst (.snd (v dk)))) (.nat 32)))
              (.eqN (e2ePureOp (.pbytesLen 32) (.snd (.snd (v dk)))) (.nat 32)))
        (.some (.pair
          (.pair
            (e2ePureOp .pbytesToBv256 (.fst (v dk)))
            (e2ePureOp .pbytesToBv256 (.fst (.snd (v dk)))))
          (e2ePureOp .pbytesToBv256 (.snd (.snd (v dk))))))
        .none)
    (fun _ => .none)

@[simp] theorem eval_extractDrKey32E {Γ} (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ) :
    (extractDrKey32E krE).eval ρ =
      match keyIndRdec (krE.eval ρ) with
      | .drKeyResp dk =>
        if dk.rootKey.length == 32 && dk.chainKey.length == 32 && dk.pqrKey.length == 32 then
          some ((bhBytesWord dk.rootKey, bhBytesWord dk.chainKey), bhBytesWord dk.pqrKey)
        else none
      | _ => none := by
  rcases h : krE.eval ρ with _ | ⟨_, _⟩ | _ | ⟨_, _⟩ | _ | _ | ⟨_, _⟩ | _ |
      ⟨rk, ck, pqk⟩ | ⟨_, _, _, _⟩ | _ <;>
    simp only [extractDrKey32E, keyIndRdec, drKeyOfV, bhBytesWord, eCaseSum,
      v, Ext.wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get, h]
  by_cases h1 : rk.length = 32 <;> by_cases h2 : ck.length = 32 <;>
    by_cases h3 : pqk.length = 32 <;> simp [BEq.beq, h1, h2, h3]

theorem cost_extractDrKey32E {Γ} (krE : E2EExpr Γ keyIndRT) :
    (extractDrKey32E krE).cost ≤ krE.cost + 180 := by
  simp only [extractDrKey32E, eCaseSum, Expr.cost, cost_v,
    cost_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat, bits, show Nat.log 2 32 = 5 from rfl]
  omega

attribute [local irreducible] extractDrKey32E

def extractSpkSk32E {Γ} (krE : E2EExpr Γ keyIndRT) : E2EExpr Γ (.opt BV256) :=
  eCaseSum krE (fun _ => .none) fun r1 =>
  eCaseSum (v r1) (fun _ => .none) fun r2 =>
  eCaseSum (v r2) (fun _ => .none) fun r3 =>
  eCaseSum (v r3) (fun _ => .none) fun r4 =>
  eCaseSum (v r4) (fun _ => .none) fun r5 =>
  eCaseSum (v r5) (fun _ => .none) fun r6 =>
  eCaseSum (v r6) (fun _ => .none) fun r7 =>
  eCaseSum (v r7) (fun _ => .none) fun r8 =>
  eCaseSum (v r8) (fun _ => .none) fun r9 =>
  eCaseSum (v r9) (fun _ => .none) fun sk =>
    .ite (.eqN (e2ePureOp (.pbytesLen 32) (v sk)) (.nat 32))
      (.some (e2ePureOp .pbytesToBv256 (v sk)))
      .none

@[simp] theorem eval_extractSpkSk32E {Γ} (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ) :
    (extractSpkSk32E krE).eval ρ =
      match keyIndRdec (krE.eval ρ) with
      | .spkSkResp spkSk =>
        if spkSk.length == 32 then some (bhBytesWord spkSk) else none
      | _ => none := by
  rcases h : krE.eval ρ with _ | ⟨_, _⟩ | _ | ⟨_, _⟩ | _ | _ | ⟨_, _⟩ | _ | _ | ⟨_, _, _, _⟩ | sk <;>
    simp only [extractSpkSk32E, keyIndRdec, bhBytesWord, eCaseSum,
      v, Ext.wk, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get, h]
  by_cases hs : sk.length = 32 <;> simp [BEq.beq, hs]

theorem cost_extractSpkSk32E {Γ} (krE : E2EExpr Γ keyIndRT) :
    (extractSpkSk32E krE).cost ≤ krE.cost + 80 := by
  simp only [extractSpkSk32E, eCaseSum, Expr.cost, cost_v,
    cost_e2ePureOp, E2EPureOp.cost, PNat.val_ofNat, bits, show Nat.log 2 32 = 5 from rfl]
  omega

attribute [local irreducible] extractSpkSk32E

/-- Standalone slot-level builder: given `(sid, (hdr, (bnd, (u, j))))` and `(kr1, (kr2, (ac, bMode?)))`,
constructs `Option (e2eModelInstTy S ℓ × e2eInstMetaTy S ℓ)`. -/
def finishStartSlotE {Γ}
    (guardHitE : E2EExpr Γ (.prod (sidT S)
      (.prod hdrT (.prod bundleT (.prod (FinT S.N_id) (FinT S.N_recv))))))
    (argsE : E2EExpr Γ (.prod keyIndRT
      (.prod keyIndRT (.prod BV256 (.opt .bool))))) :
    E2EExpr Γ (.opt (.prod (e2eModelInstTy S ℓ) (e2eInstMetaTy S ℓ))) :=
  eLet (.pair guardHitE argsE) fun p =>
    eCaseOpt (extractDrKey32E (.fst (.snd (v p)))) .none fun dkWords =>
      eCaseOpt (extractSpkSk32E (.fst (.snd (.snd (v p))))) .none fun spkCoins =>
        eLet (.pair
            (.pair
              (e2ePureOp .idKeyOfPbytes (hdrIkA (.fst (.snd (.fst (v p))))))
              (e2ePureOp .idKeyOfPbytes (bndIkB (.fst (.snd (.snd (.fst (v p))))))))
            (.pair (v spkCoins)
              (.pair (.fst (v dkWords))
                (.pair (.fst (.snd (.snd (.snd (v p))))) (.snd (v dkWords)))))) fun initIn =>
          .some (.pair
            (.pair (.fst (.fst (v p)))
              (.pair (.fst (.snd (.fst (v p))))
                (.pair (.fst (.fst (v initIn)))
                  (.pair (.snd (.fst (v initIn)))
                    (.pair (.fst (.snd (v initIn)))
                      (eCaseOpt (.snd (.snd (.snd (.snd (v p)))))
                        .none
                        (fun bBit =>
                          .some (initFixedSpkGsE (.fst (v initIn))
                            (.pair (.fst (.snd (v initIn)))
                              (.pair (.snd (.snd (v initIn))) (v bBit)))))))))))
            (.pair (.bool false)
              (.pair (.bool false)
                (.pair (.some (.fst (.snd (.snd (.snd (.fst (v p)))))))
                  (.pair (.some (.snd (.snd (.snd (.snd (.fst (v p)))))))
                    (hdrOpkId (.fst (.snd (.fst (v p))))))))))

@[simp] theorem eval_finishStartSlotE {Γ}
    (guardHitE : E2EExpr Γ (.prod (sidT S)
      (.prod hdrT (.prod bundleT (.prod (FinT S.N_id) (FinT S.N_recv))))))
    (argsE : E2EExpr Γ (.prod keyIndRT
      (.prod keyIndRT (.prod BV256 (.opt .bool)))))
    (ρ : Env Γ) :
    let (sidVal, (hdrVal, (bndVal, (u, j)))) := guardHitE.eval ρ
    let (kr1Val, (kr2Val, (ac, bMode?))) := argsE.eval ρ
    let hdr := hdrOfV hdrVal
    let bnd := bundleOfV bndVal
    (finishStartSlotE guardHitE argsE).eval ρ =
      match keyIndRdec kr1Val, keyIndRdec kr2Val with
      | .drKeyResp dk, .spkSkResp spkSk =>
        if dk.rootKey.length == 32 && dk.chainKey.length == 32 &&
           dk.pqrKey.length == 32 && spkSk.length == 32 then
          let idA := bhIdKeyOf hdr.ikAPk
          let idB := bhIdKeyOf bnd.ikB
          let spkCoins := bhBytesWord spkSk
          let kS : SampledSessionKey := bhKeySOf dk ac
          let sch := sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
          let gs := bMode?.map (fun b => initState sch.sendPart kS b)
          some (e2eModelInstEnc { sid := sidOfV sidVal, hdr, idA, idB, spkCoins, gs },
                e2eInstMetaEnc { respPrin := some u, respSpkIdx := some j,
                                 instOpkId? := hdr.opkId? })
        else none
      | _, _ => none := by
  rcases hgh : guardHitE.eval ρ with ⟨sidVal, ⟨hdrVal, ⟨bndVal, ⟨u, j⟩⟩⟩⟩
  rcases hargs : argsE.eval ρ with ⟨kr1Val, ⟨kr2Val, ⟨ac, bMode?⟩⟩⟩
  simp only [finishStartSlotE, eLet, eCaseOpt, v, Ext.wk,
    Expr.eval, Env.get, hgh, hargs, eval_extractDrKey32E, eval_extractSpkSk32E]
  rcases keyIndRdec kr1Val with _ | _ | _ | _ | _ | _ | _ | _ | dk | _ | _ <;>
    try rfl
  rcases keyIndRdec kr2Val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | spkSk
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only; cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;> rfl
  · dsimp only
    cases (List.length dk.rootKey == 32) <;>
      cases (List.length dk.chainKey == 32) <;>
      cases (List.length dk.pqrKey == 32) <;>
      cases (List.length spkSk == 32) <;> try rfl
    simp only [Bool.true_and, ↓reduceIte]
    rcases hdrVal with ⟨ikAPk, ekAPk, spkId, opkId?, pqspkId, kemCt⟩
    rcases bndVal with ⟨ikB, bSpkId, spkB, spkSig, opkB?, bPqId, pqspkB, pqspkSig⟩
    cases bMode? with
    | none =>
      simp only [Option.map, Expr.eval, Env.get, hdrIkA, bndIkB, hdrOpkId,
        e2eModelInstEnc, e2eInstMetaEnc, hdrOfV, bundleOfV, hdrV, bhIdKeyOf,
        eval_e2ePureOp, E2EPureOp.eval, sidV_sidOfV]
    | some b =>
      simp only [Option.map, Expr.eval, Env.get, hdrIkA, bndIkB, hdrOpkId,
        e2eModelInstEnc, e2eInstMetaEnc,
        hdrOfV, bundleOfV, hdrV, bhIdKeyOf, bhKeySOf,
        eval_e2ePureOp, E2EPureOp.eval, sidV_sidOfV]
      rw [eval_initFixedSpkGsE]
      simp only [Expr.eval, Env.get]

theorem cost_finishStartSlotE {Γ}
    (guardHitE : E2EExpr Γ (.prod (sidT S)
      (.prod hdrT (.prod bundleT (.prod (FinT S.N_id) (FinT S.N_recv))))))
    (argsE : E2EExpr Γ (.prod keyIndRT
      (.prod keyIndRT (.prod BV256 (.opt .bool))))) :
    (finishStartSlotE guardHitE argsE).cost ≤
      guardHitE.cost + argsE.cost + 94500 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (.prod (sidT S) (.prod hdrT (.prod bundleT (.prod (FinT S.N_id) (FinT S.N_recv)))))
          (.prod keyIndRT (.prod keyIndRT (.prod BV256 (.opt .bool))))
  let τdk : Ty (e2eSig ℓ) := .prod (.prod BV256 BV256) BV256
  let τin : Ty (e2eSig ℓ) :=
    .prod (.prod IdKey IdKey) (.prod BV256 (.prod (.prod BV256 BV256) (.prod BV256 BV256)))
  have hdr := cost_extractDrKey32E (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τp :: Γ) (.fst (.snd (.var .zero)))
  have hsk := cost_extractSpkSk32E (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τdk :: τp :: Γ)
    (.fst (.snd (.snd (.var (.succ .zero)))))
  have hgs := cost_initFixedSpkGsE (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := .bool :: τin :: BV256 :: τdk :: τp :: Γ)
    (.fst (.var (.succ .zero)))
    (.pair (.fst (.snd (.var (.succ .zero))))
      (.pair (.snd (.snd (.var (.succ .zero)))) (.var .zero)))
  unfold finishStartSlotE
  dsimp only [v, Ext.wk]
  simp only [hdrIkA, bndIkB, hdrOpkId, eLet, eCaseOpt,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost] at hdr hsk hgs ⊢
  omega

attribute [local irreducible] finishStartSlotE

/-- General `bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac` over `e2eDrvStateTy S ℓ`. -/
def finishStartSpkGenE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (argsE : E2EExpr Γ (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256)))) :
    E2EExpr Γ (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  eLet (.pair (.pair bModeE σE) argsE) fun p =>
    eCaseOpt
      (bhE2EGuardE qStart nPrins nBundles nOpks nSends
        (.snd (.fst (v p))) (.fst (.snd (v p))))
      (.pair .none (.snd (.fst (v p))))
      (fun gHit =>
        eCaseOpt
          (finishStartSlotE
            (.pair (.fst (.snd (v p))) (v gHit))
            (.pair (.fst (.snd (.snd (v p))))
              (.pair (.fst (.snd (.snd (.snd (v p)))))
                (.pair (.snd (.snd (.snd (.snd (v p)))))
                  (.fst (.fst (v p)))))))
          (.pair .none (.snd (.fst (v p))))
          (fun slotPair =>
            .pair
              (.some (.len (drvInsts (.snd (.fst (v p))))))
              (drvSetInstsAndMetaE (.snd (.fst (v p)))
                (listSnocE qStart (drvInsts (.snd (.fst (v p)))) (.fst (v slotPair)))
                (listSnocE qStart (drvInstMeta (.snd (.fst (v p)))) (.snd (v slotPair))))))

@[simp] theorem eval_finishStartSpkGenE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (argsE : E2EExpr Γ (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256))))
    (ρ : Env Γ) {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hbnd : DrvMirrorBounded nPrins nBundles nOpks nSends 0 qStart σ ∨
      (σ.insts.length ≤ qStart ∧ σ.instMeta.length ≤ qStart ∧ σ.prins.length ≤ nPrins ∧
       σ.bundles.length ≤ nBundles ∧ σ.opks.length ≤ nOpks ∧ σ.sends.length ≤ nSends ∧
       σ.corrPrins.length ≤ nPrins)) :
    let (sidVal, (kr1Val, (kr2Val, ac))) := argsE.eval ρ
    let res := bhE2EFinishStartSpk C K (bModeE.eval ρ) σ
      (sidOfV sidVal) (keyIndRdec kr1Val) (keyIndRdec kr2Val) ac
    (finishStartSpkGenE qStart nPrins nBundles nOpks nSends bModeE σE argsE).eval ρ =
      (res.1, e2eDrvStateEnc res.2) := by
  have ⟨hInsts, hMeta, hPrins, hBundles, hOpks, hSends, hCorr⟩ :
      σ.insts.length ≤ qStart ∧ σ.instMeta.length ≤ qStart ∧ σ.prins.length ≤ nPrins ∧
      σ.bundles.length ≤ nBundles ∧ σ.opks.length ≤ nOpks ∧ σ.sends.length ≤ nSends ∧
      σ.corrPrins.length ≤ nPrins := by
    rcases hbnd with h | h
    · exact ⟨h.insts_le, h.instMeta_le, h.prins_le, h.bundles_le, h.opks_le, h.sends_le,
        h.corrPrins_le.trans (Nat.zero_le _)⟩
    · exact h
  rcases hargs : argsE.eval ρ with ⟨sidVal, ⟨kr1Val, ⟨kr2Val, ac⟩⟩⟩
  simp only [finishStartSpkGenE, eLet, eCaseOpt, v, Ext.wk,
    Expr.eval, Env.get, hσ, hargs]
  rw [eval_bhE2EGuardE qStart nPrins nBundles nOpks nSends _ _ _
    (by simp only [Expr.eval, Env.get]) hInsts hPrins hBundles hOpks hSends hCorr]
  simp only [Expr.eval, Env.get, bhE2EFinishStartSpk]
  rcases hg : bhE2EGuard σ (sidOfV sidVal) with _ | ⟨hdr, bnd, ⟨u, j⟩⟩
  · rfl
  · dsimp only [Option.map]
    rw [eval_finishStartSlotE]
    simp only [Expr.eval, Env.get, hdrOfV_hdrV, bundleOfV_bundleV]
    rcases keyIndRdec kr1Val with _ | _ | _ | _ | _ | _ | _ | _ | dk | _ | _ <;>
      try rfl
    rcases keyIndRdec kr2Val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | spkSk <;>
      try rfl
    dsimp only
    cases hlen : (List.length dk.rootKey == 32 && List.length dk.chainKey == 32 &&
        List.length dk.pqrKey == 32 && List.length spkSk == 32)
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      dsimp only [Expr.eval, Env.get, drvInsts, drvInstMeta,
        drvSetInstsAndMetaE, drvBase, drvCorrPrins, drvRevSpks, eLet, v, Ext.wk]
      rw [eval_listSnocE qStart _ _ _
            (by simp only [Expr.eval, Env.get, e2eDrvStateEnc, List.length_map]; exact hInsts),
          eval_listSnocE qStart _ _ _
            (by simp only [Expr.eval, Env.get, e2eDrvStateEnc, List.length_map]; exact hMeta)]
      simp only [Expr.eval, Env.get, e2eDrvStateEnc,
        List.length_map, List.map_append, List.map_cons, List.map_nil]
      cases bModeE.eval ρ <;> rfl

theorem cost_finishStartSpkGenE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (bModeE : E2EExpr Γ (.opt .bool))
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (argsE : E2EExpr Γ (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256)))) :
    (finishStartSpkGenE qStart nPrins nBundles nOpks nSends bModeE σE argsE).cost ≤
      bModeE.cost + σE.cost + argsE.cost +
        180 * qStart + 96 * nSends + 3300 * nBundles + 100 * nPrins + 144 * nOpks + 94840 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (.prod (.opt .bool) (e2eDrvStateTy S ℓ))
          (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256)))
  let τg : Ty (e2eSig ℓ) :=
    .prod hdrT (.prod bundleT (.prod (FinT S.N_id) (FinT S.N_recv)))
  have hg := cost_bhE2EGuardE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends (Γ := τp :: Γ)
    (.snd (.fst (.var .zero))) (.fst (.snd (.var .zero)))
  have hsl := cost_finishStartSlotE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := τg :: τp :: Γ)
    (.pair (.fst (.snd (.var (.succ .zero)))) (.var .zero))
    (.pair (.fst (.snd (.snd (.var (.succ .zero)))))
      (.pair (.fst (.snd (.snd (.snd (.var (.succ .zero))))))
        (.pair (.snd (.snd (.snd (.snd (.var (.succ .zero))))))
          (.fst (.fst (.var (.succ .zero)))))))
  dsimp only [τp, τg] at hg hsl
  unfold finishStartSpkGenE
  dsimp only [v, Ext.wk]
  simp only [drvSetInstsAndMetaE, drvBase, drvCorrPrins, drvRevSpks,
    drvInsts, drvInstMeta, listSnocE, eLet, eCaseOpt, Expr.cost, cost_v] at hg hsl ⊢
  omega

attribute [local irreducible] finishStartSpkGenE

def finishStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (argsE : E2EExpr Γ (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256)))) :
    E2EExpr Γ (.prod (.opt .nat) (e2eDrvStateTy S ℓ)) :=
  eLet (.pair σE argsE) fun p =>
    finishStartSpkGenE qStart nPrins nBundles nOpks nSends
      (.some (drvB (.fst (v p)))) (.fst (v p)) (.snd (v p))

@[simp] theorem eval_finishStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (argsE : E2EExpr Γ (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256))))
    (ρ : Env Γ) {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart) (hMeta : σ.instMeta.length ≤ qStart)
    (hPrins : σ.prins.length ≤ nPrins) (hBundles : σ.bundles.length ≤ nBundles)
    (hOpks : σ.opks.length ≤ nOpks) (hSends : σ.sends.length ≤ nSends)
    (hCorr : σ.corrPrins.length ≤ nPrins) :
    let (sidVal, (kr1Val, (kr2Val, ac))) := argsE.eval ρ
    let res := bhE2EFinishStartSpk C K (some σ.b) σ
      (sidOfV sidVal) (keyIndRdec kr1Val) (keyIndRdec kr2Val) ac
    (finishStartSpkE qStart nPrins nBundles nOpks nSends σE argsE).eval ρ =
      (res.1, e2eDrvStateEnc res.2) := by
  simp only [finishStartSpkE, eLet, Expr.eval, hσ]
  rw [eval_finishStartSpkGenE qStart nPrins nBundles nOpks nSends _ _ _ _
    (by simp only [v, Ext.wk, Expr.eval, Env.get])
    (Or.inr ⟨hInsts, hMeta, hPrins, hBundles, hOpks, hSends, hCorr⟩)]
  simp only [drvB, v, Ext.wk, Expr.eval, Env.get, e2eDrvStateEnc]

theorem cost_finishStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (argsE : E2EExpr Γ (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256)))) :
    (finishStartSpkE qStart nPrins nBundles nOpks nSends σE argsE).cost ≤
      σE.cost + argsE.cost +
        180 * qStart + 96 * nSends + 3300 * nBundles + 100 * nPrins + 144 * nOpks + 94860 := by
  let τp : Ty (e2eSig ℓ) :=
    .prod (e2eDrvStateTy S ℓ) (.prod (sidT S) (.prod keyIndRT (.prod keyIndRT BV256)))
  have hg := cost_finishStartSpkGenE (ℓ := ℓ) (S := S) (Pt := Pt) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends
    (Γ := τp :: Γ)
    (.some (drvB (.fst (.var .zero)))) (.fst (.var .zero)) (.snd (.var .zero))
  dsimp only [τp] at hg
  unfold finishStartSpkE
  dsimp only [v, Ext.wk]
  simp only [drvB, eLet, Expr.cost] at hg ⊢
  omega

attribute [local irreducible] finishStartSpkE

end StartPure

end Computational.Proofs.E2E.Dsl.StartAndExtSmAux
