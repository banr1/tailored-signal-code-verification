/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSimHooks
import Computational.Proofs.E2E.ComposedBinaryLinkV1

/-!
# Double Ratchet + SPQR V1 Receive Simulator

Constructs the `ReductionDsl` receive subprogram `drReceiveC` over `e2eOps` (parameterized by
`SpqrDslHooks`), bounds its query count and static cost, and proves `Comp.eval` agreement with
`Params.receive` and `sessionSchemeFixedSpk.receive` under `PartyReachInv`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.DrSessionSimRecv

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.Ratchet (keyToBytesVec32 padOrTruncatePlain)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey IdentityKey KeyPair ChainKey
  MessageKeyGenerator SenderChain ReceiverChain RatchetState TripleRatchet SessionState GhostState
  MessageType SignalProtocolError SignalMessage maxReceiverChains maxForwardJumps rootCreateChain
  aesCbcDecrypt liftE Mut)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.E2E (Bytes serializedPartyAddresses paramsIdsWithSpqr
  sessionSchemeFixedSpk keyToBytes32_bytesToKey32)
open CryptoVerification.E2E.Costed (e2eSig B U8 U32 BV128 BV256 IdKey PK PlainT GhostStT
  drSenderChainT drRecvChainT ghostPartsT signalHdrT signalParsedT E2EPureOp E2ECryptoOp
  e2ePureOps e2eCryptoOps e2eOps ghostSplitEval ghostJoinEval partyToBool boolToParty)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp eval_e2ePureOp
  cost_e2ePureOp eval_e2eCryptoOp cost_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2ePureOps_eval_signalMsgParse_lossless)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (SpqrDslHooks encodeChainKey decodeChainKey
  encodeMsgKey decodeMsgKey decodeMsgKey_encodeMsgKey encodeSenderChain decodeSenderChain
  decodeSenderChain_encodeSenderChain encodeRecvChain decodeRecvChain
  decodeRecvChains_encodeRecvChains privateKey_roundtrip salt_roundtrip boolToParty_partyToBool_eq
  chainKey_messageKeys_seed_len ghostSplitEval_eq_of_le ghostJoinEval_eq_of_le gpIsB gpVer gpLocId
  gpRemId gpRk gpPrevCtr gpPend gpEp gpCEps gpSc gpRcs gpPqSt gpMk expectedAddrsE
  eval_expectedAddrsE cost_expectedAddrsE_le sessionVersionEffE eval_sessionVersionEffE
  cost_sessionVersionEffE pushEvict5E eval_pushEvict5E cost_pushEvict5E_le getDZero5E
  eval_getDZero5E cost_getDZero5E_le findChainWithIdx5E eval_findChainWithIdx5E
  cost_findChainWithIdx5E_le replaceFirstChain5E eval_replaceFirstChain5E
  cost_replaceFirstChain5E_le takeSkippedFromListE eval_takeSkippedFromListE
  cost_takeSkippedFromListE_le advanceSingleChainC advanceSingleChainC_queries
  advanceSingleChainC_cost_le advanceSingleChainC_eval_iterate chainAdvStepFn_iterate_eq_advanceChain
  storeSkipped_trim_eq_take2000)

section RecvProgram

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "S" => e2eSig ℓ
local notation "OO" => e2eOps ℓ P C K decT encT

/-! ## Stages of `drReceiveC` -/

@[reducible] def drRecvOutT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .opt (.prod GhostStT (.prod .nat (.prod .nat PlainT)))

@[reducible] def drRecvMsgT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod PK (.prod U32 (.prod (B 32) (B 32)))

@[reducible] def drRecvPreT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .opt (.prod ghostPartsT (.prod IdKey (drRecvMsgT ℓ)))

@[reducible] def drRatchetMidT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod BV256 (.prod U32 (.prod (.opt drSenderChainT)
    (.prod (.list drRecvChainT) (.prod .nat (.prod .nat (.list .nat))))))

@[reducible] def drChainActiveT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (.prod BV256 U32) (.list (.prod BV256 U32))

@[reducible] def drRecvSetupOutT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .opt (.prod (drRatchetMidT ℓ) (drChainActiveT ℓ))

@[reducible] def drRecvConsumeOutT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .opt (.prod (.prod BV256 U32) (.list drRecvChainT))

def drRecvPreE {Γ : List (Ty S)} (gE : Expr OO Γ GhostStT) (cE : Expr OO Γ (B 32)) :
    Expr OO Γ (drRecvPreT ℓ) :=
  .letE (.pair gE cE)
    (.caseOpt (e2ePureOp .signalMsgParse (.snd .v0))
      .none
      (.letE (e2ePureOp .ghostStateSplit (.fst .v1))
        (let parts : Expr OO _ ghostPartsT := .v0
         let parsed : Expr OO _ signalParsedT := .v1
         let msgVer : Expr OO _ U8 := .fst (.fst parsed)
         .ite (.eqN (e2ePureOp .u32ToNat (sessionVersionEffE (gpVer parts)))
                    (e2ePureOp .u8ToNat msgVer))
           (.caseOpt (gpRemId parts)
             .none
             (.some (.pair .v1
               (.pair .v0
                 (.pair (.fst (.snd (.fst .v2)))
                   (.pair (.fst (.snd (.snd (.fst .v2))))
                     (.pair (.fst (.snd .v2)) (.fst (.snd (.snd .v2))))))))))
           .none)))

theorem cost_drRecvPreE_le {Γ : List (Ty S)} (gE : Expr OO Γ GhostStT) (cE : Expr OO Γ (B 32)) :
    (drRecvPreE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) gE cE).cost ≤
      gE.cost + cE.cost + 200 + (ℓ / 32 + 1) := by
  simp only [drRecvPreE, gpVer, gpRemId, cost_sessionVersionEffE, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, cost_e2ePureOp, E2EPureOp.cost]
  omega

def drRecvDhStepE {Γ : List (Ty S)}
    (partsE : Expr OO Γ ghostPartsT)
    (theirE : Expr OO Γ PK)
    (rcCoinsE : Expr OO Γ BV256) :
    Expr OO Γ (drRecvSetupOutT ℓ) :=
  .letE (.pair partsE (.pair theirE rcCoinsE))
    (.caseOpt (gpSc (.fst .v0))
      .none
      (.caseOpt
        (e2eCryptoOp .sessionRootCreateChain
          (.pair (gpRk (.fst .v1)) (.pair (.fst (.snd .v1)) (.snd (.fst .v0)))))
        .none
        (.letE (e2eCryptoOp .sessionKeyPairGen (.snd (.snd .v2)))
          (.caseOpt
            (e2eCryptoOp .sessionRootCreateChain
              (.pair (.fst .v1) (.pair (.fst (.snd .v3)) (.snd .v0))))
            .none
            (let p2 : Expr OO _ (.prod BV256 BV256) := .v0
             let newKp : Expr OO _ (.prod PK BV256) := .v1
             let p1 : Expr OO _ (.prod BV256 BV256) := .v2
             let sc : Expr OO _ drSenderChainT := .v3
             let top : Expr OO _ (.prod ghostPartsT (.prod PK BV256)) :=
               .var (.succ (.succ (.succ (.succ .zero))))
             let parts : Expr OO _ ghostPartsT := .fst top
             let their : Expr OO _ PK := .fst (.snd top)
             let scIdx : Expr OO _ U32 := .snd (.snd sc)
             let zero32 : Expr OO _ U32 := e2ePureOp (.u32Lit 0#32) .unit
             let one32 : Expr OO _ U32 := e2ePureOp (.u32Lit 1#32) .unit
             let prevCtr' : Expr OO _ U32 :=
               .ite (e2ePureOp .u32Eq (.pair scIdx zero32))
                 zero32
                 (e2ePureOp .u32Sub (.pair scIdx one32))
             let recvCk : Expr OO _ (.prod BV256 U32) := .pair (.snd p1) zero32
             let sendCk : Expr OO _ (.prod BV256 U32) := .pair (.snd p2) zero32
             let newRc : Expr OO _ drRecvChainT := .pair their (.pair (.some recvCk) .nil)
             let rcs1 : Expr OO _ (.list drRecvChainT) := pushEvict5E (gpRcs parts) newRc
             let sc?' : Expr OO _ (.opt drSenderChainT) := .some (.pair newKp sendCk)
             let ep1 : Expr OO _ .nat := .add (gpEp parts) (.nat 1)
             let cEps' : Expr OO _ (.list .nat) := pushEvict5E (gpCEps parts) ep1
             let mid : Expr OO _ (drRatchetMidT ℓ) :=
               .pair (.fst p2) (.pair prevCtr' (.pair sc?' (.pair rcs1 (.pair ep1 (.pair ep1 cEps')))))
             let active : Expr OO _ (drChainActiveT ℓ) := .pair recvCk .nil
             .some (.pair mid active))))))

theorem cost_drRecvDhStepE_le {Γ : List (Ty S)}
    (partsE : Expr OO Γ ghostPartsT)
    (theirE : Expr OO Γ PK)
    (rcCoinsE : Expr OO Γ BV256) :
    (drRecvDhStepE partsE theirE rcCoinsE).cost ≤
      partsE.cost + theirE.cost + rcCoinsE.cost + 550 := by
  let Γinner : List (Ty S) :=
    .prod BV256 BV256 ::
    .prod PK BV256 ::
    .prod BV256 BV256 ::
    drSenderChainT ::
    .prod ghostPartsT (.prod PK BV256) :: Γ
  let topI : Expr OO Γinner (.prod ghostPartsT (.prod PK BV256)) :=
    .var (.succ (.succ (.succ (.succ .zero))))
  let zeroI : Expr OO Γinner U32 := e2ePureOp (.u32Lit 0#32) .unit
  have hp1 := cost_pushEvict5E_le
    (gpRcs (.fst topI))
    (.pair (.fst (.snd topI)) (.pair (.some (.pair (.snd .v2) zeroI)) .nil))
  have hp2 := cost_pushEvict5E_le
    (gpCEps (.fst topI))
    (.add (gpEp (.fst topI)) (.nat 1))
  have hb1 : bits 1 = 1 := by decide
  simp only [drRecvDhStepE, topI, zeroI, gpSc, gpRk, gpRcs, gpEp, gpCEps, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, cost_e2ePureOp, cost_e2eCryptoOp,
    E2EPureOp.cost, E2ECryptoOp.cost, hb1] at hp1 hp2 ⊢
  omega

def drRecvChainSetupE {Γ : List (Ty S)}
    (partsE : Expr OO Γ ghostPartsT)
    (theirE : Expr OO Γ PK)
    (rcCoinsE : Expr OO Γ BV256) :
    Expr OO Γ (drRecvSetupOutT ℓ) :=
  .letE (.pair partsE (.pair theirE rcCoinsE))
    (.letE (findChainWithIdx5E (gpRcs (.fst .v0)) (.fst (.snd .v0)))
      (.caseOpt (.snd .v0)
        (drRecvDhStepE (.fst .v1) (.fst (.snd .v1)) (.snd (.snd .v1)))
        (.caseOpt (.fst (.snd .v0))
          .none
          (let ckEnc : Expr OO _ (.prod BV256 U32) := .v0
           let rcEnc : Expr OO _ drRecvChainT := .v1
           let found : Expr OO _ (.prod .nat (.opt drRecvChainT)) := .v2
           let top : Expr OO _ (.prod ghostPartsT (.prod PK BV256)) := .v3
           let parts : Expr OO _ ghostPartsT := .fst top
           let tOut : Expr OO _ .nat := getDZero5E (gpCEps parts) (.fst found)
           let mid : Expr OO _ (drRatchetMidT ℓ) :=
             .pair (gpRk parts)
               (.pair (gpPrevCtr parts)
                 (.pair (gpSc parts)
                   (.pair (gpRcs parts)
                     (.pair (gpEp parts)
                       (.pair tOut (gpCEps parts))))))
           let active : Expr OO _ (drChainActiveT ℓ) := .pair ckEnc (.snd (.snd rcEnc))
           .some (.pair mid active)))))

theorem cost_drRecvChainSetupE_le {Γ : List (Ty S)}
    (partsE : Expr OO Γ ghostPartsT)
    (theirE : Expr OO Γ PK)
    (rcCoinsE : Expr OO Γ BV256) :
    (drRecvChainSetupE partsE theirE rcCoinsE).cost ≤
      partsE.cost + theirE.cost + rcCoinsE.cost + 800 := by
  have hfind := cost_findChainWithIdx5E_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (gpRcs (.fst .v0) : Expr OO (.prod ghostPartsT (.prod PK BV256) :: Γ) (.list drRecvChainT))
    (.fst (.snd .v0))
  have hdh := cost_drRecvDhStepE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst .v1 : Expr OO (.prod .nat (.opt drRecvChainT) ::
      .prod ghostPartsT (.prod PK BV256) :: Γ) ghostPartsT)
    (.fst (.snd .v1)) (.snd (.snd .v1))
  have hget := cost_getDZero5E_le
    (gpCEps (.fst .v3) : Expr OO (.prod BV256 U32 :: drRecvChainT ::
      .prod .nat (.opt drRecvChainT) ::
      .prod ghostPartsT (.prod PK BV256) :: Γ) (.list .nat))
    (.fst .v2)
  simp only [drRecvChainSetupE, gpRk, gpPrevCtr, gpSc, gpRcs, gpEp, gpCEps, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hfind hdh hget ⊢
  omega

def drRecvTakeSkippedE {Γ : List (Ty S)}
    (theirE : Expr OO Γ PK)
    (msgCtrE : Expr OO Γ U32)
    (rcs1E : Expr OO Γ (.list drRecvChainT))
    (activeE : Expr OO Γ (drChainActiveT ℓ)) :
    Expr OO Γ (drRecvConsumeOutT ℓ) :=
  .letE (.pair (.pair theirE msgCtrE) (.pair rcs1E activeE))
    (.letE (takeSkippedFromListE (.snd (.snd (.snd .v0))) (.snd (.fst .v0)))
      (.caseOpt (.fst .v0)
        .none
        (let keyEnc : Expr OO _ (.prod BV256 U32) := .v0
         let remMks : Expr OO _ (.list (.prod BV256 U32)) := .snd .v1
         let top : Expr OO _ (.prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ))) :=
           .v2
         let their : Expr OO _ PK := .fst (.fst top)
         let rcs1 : Expr OO _ (.list drRecvChainT) := .fst (.snd top)
         let chainCk : Expr OO _ (.prod BV256 U32) := .fst (.snd (.snd top))
         let newRc : Expr OO _ drRecvChainT := .pair their (.pair (.some chainCk) remMks)
         .some (.pair keyEnc (replaceFirstChain5E rcs1 their newRc)))))

theorem cost_drRecvTakeSkippedE_le {Γ : List (Ty S)}
    (theirE : Expr OO Γ PK)
    (msgCtrE : Expr OO Γ U32)
    (rcs1E : Expr OO Γ (.list drRecvChainT))
    (activeE : Expr OO Γ (drChainActiveT ℓ)) :
    (drRecvTakeSkippedE theirE msgCtrE rcs1E activeE).cost ≤
      theirE.cost + msgCtrE.cost + rcs1E.cost + activeE.cost + 44300 := by
  have htake := cost_takeSkippedFromListE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.snd (.snd (.snd .v0)) :
      Expr OO (.prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ)) :: Γ)
        (.list (.prod BV256 U32)))
    (.snd (.fst .v0))
  have hrep := cost_replaceFirstChain5E_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst (.snd .v2) :
      Expr OO (.prod BV256 U32 ::
        .prod (.opt (.prod BV256 U32)) (.list (.prod BV256 U32)) ::
        .prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ)) :: Γ)
        (.list drRecvChainT))
    (.fst (.fst .v2))
    (.pair (.fst (.fst .v2)) (.pair (.some (.fst (.snd (.snd .v2)))) (.snd .v1)))
  simp only [drRecvTakeSkippedE, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at htake hrep ⊢
  omega

def drRecvAfterAdvE {Γ : List (Ty S)}
    (theirE : Expr OO Γ PK)
    (rcs1E : Expr OO Γ (.list drRecvChainT))
    (advPairE : Expr OO Γ (drChainActiveT ℓ)) :
    Expr OO Γ (drRecvConsumeOutT ℓ) :=
  .letE (.pair theirE (.pair rcs1E advPairE))
    (.caseOpt (e2eCryptoOp .chainStep (.fst (.snd (.snd .v0))))
      .none
      (let stepOut : Expr OO _ (.prod (.prod BV256 U32) BV256) := .v0
       let top : Expr OO _ (.prod PK (.prod (.list drRecvChainT) (drChainActiveT ℓ))) := .v1
       let their : Expr OO _ PK := .fst top
       let rcs1 : Expr OO _ (.list drRecvChainT) := .fst (.snd top)
       let ckOut : Expr OO _ (.prod BV256 U32) := .fst (.snd (.snd top))
       let mksAfter : Expr OO _ (.list (.prod BV256 U32)) := .snd (.snd (.snd top))
       let ckNext : Expr OO _ (.prod BV256 U32) := .fst stepOut
       let mkGenEnc : Expr OO _ (.prod BV256 U32) := .pair (.snd stepOut) (.snd ckOut)
       let newRc : Expr OO _ drRecvChainT := .pair their (.pair (.some ckNext) mksAfter)
       .some (.pair mkGenEnc (replaceFirstChain5E rcs1 their newRc))))

theorem cost_drRecvAfterAdvE_le {Γ : List (Ty S)}
    (theirE : Expr OO Γ PK)
    (rcs1E : Expr OO Γ (.list drRecvChainT))
    (advPairE : Expr OO Γ (drChainActiveT ℓ)) :
    (drRecvAfterAdvE theirE rcs1E advPairE).cost ≤
      theirE.cost + rcs1E.cost + advPairE.cost + 220 := by
  have hrep := cost_replaceFirstChain5E_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst (.snd .v1) :
      Expr OO (.prod (.prod BV256 U32) BV256 ::
        .prod PK (.prod (.list drRecvChainT) (drChainActiveT ℓ)) :: Γ)
        (.list drRecvChainT))
    (.fst .v1)
    (.pair (.fst .v1) (.pair (.some (.fst .v0)) (.snd (.snd (.snd .v1)))))
  simp only [drRecvAfterAdvE, Expr.cost, Expr.v0, Expr.v1, cost_e2eCryptoOp,
    E2ECryptoOp.cost] at hrep ⊢
  omega

def drRecvConsumeC {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (theirE : Expr OO Γ PK)
    (msgCtrE : Expr OO Γ U32)
    (rcs1E : Expr OO Γ (.list drRecvChainT))
    (activeE : Expr OO Γ (drChainActiveT ℓ)) :
    Comp OO I Γ (drRecvConsumeOutT ℓ) :=
  .bind (.ret (.pair (.pair theirE msgCtrE) (.pair rcs1E activeE)))
    (.ite (e2ePureOp .u32Lt (.pair (.snd (.fst .v0)) (.snd (.fst (.snd (.snd .v0))))))
      (.ret (drRecvTakeSkippedE
        (.fst (.fst .v0)) (.snd (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))))
      (.ite
        (.lt (.nat 25000)
          (e2ePureOp .u32ToNat
            (e2ePureOp .u32Sub (.pair (.snd (.fst .v0)) (.snd (.fst (.snd (.snd .v0))))))))
        (.ret .none)
        (.bind
          (advanceSingleChainC I
            (.fst (.snd (.snd .v0)))
            (.snd (.snd (.snd .v0)))
            (.snd (.fst .v0)))
          (.caseOpt .v0
            (.ret .none)
            (.ret (drRecvAfterAdvE
              (.fst (.fst .v2))
              (.fst (.snd .v2))
              .v0))))))

theorem drRecvConsumeC_queries {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (theirE : Expr OO Γ PK)
    (msgCtrE : Expr OO Γ U32)
    (rcs1E : Expr OO Γ (.list drRecvChainT))
    (activeE : Expr OO Γ (drChainActiveT ℓ))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (drRecvConsumeC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I theirE msgCtrE rcs1E activeE).queries w ws = 0 := by
  simp [drRecvConsumeC, Comp.queries, advanceSingleChainC_queries]

theorem drRecvConsumeC_cost_le {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (theirE : Expr OO Γ PK)
    (msgCtrE : Expr OO Γ U32)
    (rcs1E : Expr OO Γ (.list drRecvChainT))
    (activeE : Expr OO Γ (drChainActiveT ℓ)) :
    (drRecvConsumeC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I theirE msgCtrE rcs1E activeE).cost ≤
      theirE.cost + msgCtrE.cost + rcs1E.cost + activeE.cost + 1000500 := by
  have hskip := cost_drRecvTakeSkippedE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst (.fst .v0) :
      Expr OO (.prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ)) :: Γ) PK)
    (.snd (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hadv := advanceSingleChainC_cost_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I
    (.fst (.snd (.snd .v0)) :
      Expr OO (.prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ)) :: Γ)
        (.prod BV256 U32))
    (.snd (.snd (.snd .v0))) (.snd (.fst .v0))
  have hafter := cost_drRecvAfterAdvE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst (.fst .v2) :
      Expr OO (drChainActiveT ℓ :: .opt (drChainActiveT ℓ) ::
        .prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ)) :: Γ) PK)
    (.fst (.snd .v2)) .v0
  have hb : bits 25000 = 15 := by decide
  simp only [drRecvConsumeC, Comp.cost, Expr.cost, Expr.v0, Expr.v2, cost_e2ePureOp,
    E2EPureOp.cost, hb] at hskip hadv hafter ⊢
  omega

def drRecvFinishE {Γ : List (Ty S)}
    (cE : Expr OO Γ (B 32))
    (partsE : Expr OO Γ ghostPartsT)
    (remIdE : Expr OO Γ IdKey)
    (msgCtrE : Expr OO Γ U32)
    (msgCtE : Expr OO Γ (B 32))
    (midE : Expr OO Γ (drRatchetMidT ℓ))
    (consOutE : Expr OO Γ (.prod (.prod BV256 U32) (.list drRecvChainT)))
    (pqOutE : Expr OO Γ (.prod (B 32) (.opt BV256))) :
    Expr OO Γ (drRecvOutT ℓ) :=
  .letE (.pair (.pair cE partsE)
          (.pair (.pair remIdE (.pair msgCtrE msgCtE))
            (.pair midE (.pair consOutE pqOutE))))
    (let top0 := .v0
     let mkGen0 : Expr OO _ (.prod BV256 U32) := .fst (.fst (.snd (.snd (.snd top0))))
     let pq0 : Expr OO _ (.prod (B 32) (.opt BV256)) := .snd (.snd (.snd (.snd top0)))
     .letE (e2eCryptoOp .deriveMsgKeys (.pair (.fst mkGen0) (.pair (.snd mkGen0) (.snd pq0))))
       (let mks : Expr OO _ (.prod BV256 (.prod BV256 (.prod BV128 U32))) := .v0
        let top1 := .v1
        let c1 : Expr OO _ (B 32) := .fst (.fst top1)
        let parts1 : Expr OO _ ghostPartsT := .snd (.fst top1)
        let rem1 : Expr OO _ IdKey := .fst (.fst (.snd top1))
        let msgCt1 : Expr OO _ (B 32) := .snd (.snd (.fst (.snd top1)))
        let cipherKey : Expr OO _ BV256 := .fst mks
        let macKey : Expr OO _ BV256 := .fst (.snd mks)
        let iv : Expr OO _ BV128 := .fst (.snd (.snd mks))
        let macOk : Expr OO _ .bool :=
          e2eCryptoOp .signalMsgVerifyMac
            (.pair c1 (.pair (expectedAddrsE (gpIsB parts1))
              (.pair rem1 (.pair (gpLocId parts1) macKey))))
        .ite macOk
          (.caseOpt (e2eCryptoOp .aes256CbcDec (.pair cipherKey (.pair iv msgCt1)))
            .none
            (let pt : Expr OO _ PlainT := .v0
             let top2 := .v2
             let parts2 : Expr OO _ ghostPartsT := .snd (.fst top2)
             let msgCtr2 : Expr OO _ U32 := .fst (.snd (.fst (.snd top2)))
             let mid2 : Expr OO _ (drRatchetMidT ℓ) := .fst (.snd (.snd top2))
             let rcs2 : Expr OO _ (.list drRecvChainT) := .snd (.fst (.snd (.snd (.snd top2))))
             let newPq2 : Expr OO _ (B 32) := .fst (.snd (.snd (.snd (.snd top2))))
             let rk' : Expr OO _ BV256 := .fst mid2
             let prevCtr' : Expr OO _ U32 := .fst (.snd mid2)
             let sc?' : Expr OO _ (.opt drSenderChainT) := .fst (.snd (.snd mid2))
             let cur' : Expr OO _ .nat := .fst (.snd (.snd (.snd (.snd mid2))))
             let tOut : Expr OO _ .nat := .fst (.snd (.snd (.snd (.snd (.snd mid2)))))
             let cEps' : Expr OO _ (.list .nat) := .snd (.snd (.snd (.snd (.snd (.snd mid2)))))
             let g' : Expr OO _ GhostStT :=
               e2ePureOp .ghostStateJoin
                 (gpMk (gpIsB parts2) (gpVer parts2) (gpLocId parts2) (gpRemId parts2)
                   rk' prevCtr' (.bool false) cur' cEps' sc?' rcs2 newPq2)
             let idxOut : Expr OO _ .nat := .add (e2ePureOp .u32ToNat msgCtr2) (.nat 1)
             .some (.pair g' (.pair tOut (.pair idxOut pt)))))
          .none))

theorem cost_drRecvFinishE_le {Γ : List (Ty S)}
    (cE : Expr OO Γ (B 32))
    (partsE : Expr OO Γ ghostPartsT)
    (remIdE : Expr OO Γ IdKey)
    (msgCtrE : Expr OO Γ U32)
    (msgCtE : Expr OO Γ (B 32))
    (midE : Expr OO Γ (drRatchetMidT ℓ))
    (consOutE : Expr OO Γ (.prod (.prod BV256 U32) (.list drRecvChainT)))
    (pqOutE : Expr OO Γ (.prod (B 32) (.opt BV256))) :
    (drRecvFinishE cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE).cost ≤
      cE.cost + partsE.cost + remIdE.cost + msgCtrE.cost + msgCtE.cost +
        midE.cost + consOutE.cost + pqOutE.cost + 550 + 7 * (ℓ / 32 + 1) := by
  have hexp := cost_expectedAddrsE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (gpIsB (.snd (.fst .v1)) :
      Expr OO (.prod BV256 (.prod BV256 (.prod BV128 U32)) ::
        .prod (.prod (B 32) ghostPartsT)
          (.prod (.prod IdKey (.prod U32 (B 32)))
            (.prod (drRatchetMidT ℓ)
              (.prod (.prod (.prod BV256 U32) (.list drRecvChainT))
                (.prod (B 32) (.opt BV256))))) :: Γ) .bool)
  have hb1 : bits 1 = 1 := by decide
  simp only [drRecvFinishE, gpIsB, gpVer, gpLocId, gpRemId, gpMk, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, cost_e2ePureOp, cost_e2eCryptoOp,
    E2EPureOp.cost, E2ECryptoOp.cost, hb1] at hexp ⊢
  omega

/-- `ReductionDsl` simulator for `Params.receive` and `sessionSchemeFixedSpk.receive`. -/
def drReceiveC (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod (B 32) BV256))) :
    Comp OO I Γ (drRecvOutT ℓ) :=
  .bind (.ret e)
    (.caseOpt (drRecvPreE (.fst .v0) (.fst (.snd .v0)))
      (.ret .none)
      (.caseOpt
        (drRecvChainSetupE
          (.fst .v0)
          (.fst (.snd (.snd .v0)))
          (.snd (.snd .v1)))
        (.ret .none)
        (.bind
          (drRecvConsumeC I
            (.fst (.snd (.snd .v1)))
            (.fst (.snd (.snd (.snd .v1))))
            (.fst (.snd (.snd (.snd (.fst .v0)))))
            (.snd .v0))
          (.caseOpt .v0
            (.ret .none)
            (.bind
              (hooks.recvC I
                (.pair
                  (gpPqSt (.fst .v3))
                  (.snd (.snd (.snd (.snd (.snd .v3)))))))
              (.caseOpt .v0
                (.ret .none)
                (.ret (drRecvFinishE
                  (.fst (.snd (.var (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
                  (.fst (.snd (.var (.succ (.succ (.succ (.succ (.succ .zero))))))))
                  (.fst (.snd (.snd (.snd (.var (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                  (.fst (.snd (.snd (.snd (.snd (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
                  (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
                  .v2
                  .v0))))))))

theorem drReceiveC_queries (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod (B 32) BV256)))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (drReceiveC hooks I e).queries w ws = 0 := by
  simp [drReceiveC, Comp.queries, drRecvConsumeC_queries, hooks.recvC_queries]

theorem drReceiveC_cost (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveC hooks I e).cost ≤ e.cost + 5104000 + 8 * (ℓ / 32 + 1) := by
  let tIn : Ty S := .prod GhostStT (.prod (B 32) BV256)
  let tPreVal : Ty S := .prod ghostPartsT (.prod IdKey (drRecvMsgT ℓ))
  let tSetVal : Ty S := .prod (drRatchetMidT ℓ) (drChainActiveT ℓ)
  let tConsVal : Ty S := .prod (.prod BV256 U32) (.list drRecvChainT)
  let tPqVal : Ty S := .prod (B 32) (.opt BV256)
  have hpre := cost_drRecvPreE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst .v0 : Expr OO (tIn :: Γ) GhostStT) (.fst (.snd .v0))
  have hset := cost_drRecvChainSetupE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst .v0 : Expr OO (tPreVal :: tIn :: Γ) ghostPartsT)
    (.fst (.snd (.snd .v0))) (.snd (.snd .v1))
  have hcons := drRecvConsumeC_cost_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) I
    (.fst (.snd (.snd .v1)) : Expr OO (tSetVal :: tPreVal :: tIn :: Γ) PK)
    (.fst (.snd (.snd (.snd .v1))))
    (.fst (.snd (.snd (.snd (.fst .v0)))))
    (.snd .v0)
  have hpq := hooks.recvC_cost I
    (.pair (gpPqSt (.fst .v3)) (.snd (.snd (.snd (.snd (.snd .v3))))) :
      Expr OO (tConsVal :: drRecvConsumeOutT ℓ :: tSetVal :: tPreVal :: tIn :: Γ)
        (.prod (B 32) (B 32)))
  let Γfin : List (Ty S) :=
    tPqVal :: .opt tPqVal :: tConsVal :: drRecvConsumeOutT ℓ :: tSetVal :: tPreVal :: tIn :: Γ
  have hfin := cost_drRecvFinishE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (.fst (.snd (.var (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))) : Expr OO Γfin (B 32))
    (.fst (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))
    (.fst (.snd (.var (.succ (.succ (.succ (.succ (.succ .zero))))))))
    (.fst (.snd (.snd (.snd (.var (.succ (.succ (.succ (.succ (.succ .zero))))))))))
    (.fst (.snd (.snd (.snd (.snd (.var (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
    (.fst (.var (.succ (.succ (.succ (.succ .zero))))))
    .v2 .v0
  simp only [drReceiveC, gpPqSt, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hpre hset hcons hpq hfin ⊢
  omega

/-! ## Model `Mut.exec` and ratchet structural lemmas -/

private theorem mut_exec_bind_m {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    (m >>= f).exec s =
      match m.exec s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => (f a).exec s' := by
  unfold Mut.exec
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases StateT.run (ExceptT.run m) s with ⟨err | val, s'⟩ <;> rfl

private theorem mut_exec_zoom_m {σ τ α : Type} (proj : σ → τ) (inj : σ → τ → σ)
    (m : Mut τ α) (s : σ) :
    (CryptoGames.LibsignalSession.zoom proj inj m).exec s =
      match m.exec (proj s) with
      | (.error e, t') => (.error e, inj s t')
      | (.ok a, t') => (.ok a, inj s t') := by
  unfold CryptoGames.LibsignalSession.zoom
  rw [mut_exec_bind_m]
  have hg : (get : Mut σ σ).exec s = (.ok s, s) := rfl
  rw [hg]
  dsimp only
  rcases hm : m.exec (proj s) with ⟨err | val, t'⟩ <;> rfl

private theorem tripleFromSessionState_exec {PQ : Type} [Inhabited PQ] (s : SessionState PQ) :
    TripleRatchet.fromSessionState.exec s =
      match s.remoteIdentity with
      | none =>
        (.error (.invalidSessionStructure .missingRemoteIdentity),
         { s with receiverChains := [], pqRatchetState := default })
      | some rem =>
        (.ok ⟨⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩,
              s.pqRatchetState, s.localIdentity, rem⟩,
         { s with receiverChains := [], pqRatchetState := default }) := by
  rcases s with ⟨sv, lid, _ | rem, rk, pc, sc, rcs, ppk, pqs⟩ <;> rfl

private theorem rootCreateChain_index_zero (C' : Crypto) (rk : BitVec 256) (their : PublicKey)
    (our : CryptoGames.LibsignalSession.PrivateKey) {rk' : BitVec 256} {ck : ChainKey}
    (h : rootCreateChain C' rk their our = .ok (rk', ck)) :
    ck.index = 0 := by
  unfold rootCreateChain at h
  cases hcc : CryptoGames.Ratchet.createChain C'.F C'.X rk their.bytes our.bytes with
  | none =>
    rw [hcc] at h
    cases h
  | some p =>
    rw [hcc] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    rfl

private theorem dhRatchetStep_exec (C' : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) :
    (RatchetState.dhRatchetStep C' their coins).exec r =
      match r.senderChain with
      | none => (.error (.invalidSessionStructure .missingSenderChain), r)
      | some sc =>
        match rootCreateChain C' r.rootKey their sc.ratchetKey.privateKey with
        | .error e => (.error e, { r with rootKey := 0 })
        | .ok (rk1, rck) =>
          let newKp := KeyPair.generate C' coins
          match rootCreateChain C' rk1 their newKp.privateKey with
          | .error e => (.error e, { r with rootKey := 0 })
          | .ok (rk2, sck) =>
            (.ok rck,
             { r with
               previousCounter := if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
               rootKey := rk2
               receiverChains :=
                 RatchetState.evictReceiverChains (r.receiverChains ++ [⟨their, some rck, []⟩])
               senderChain := some ⟨newKp, sck⟩ }) := by
  rcases r with ⟨rk, _ | sc, rcs, pc, mfj⟩
  · rfl
  · unfold RatchetState.dhRatchetStep
    rw [mut_exec_bind_m]
    have hg : (get : Mut RatchetState RatchetState).exec ⟨rk, some sc, rcs, pc, mfj⟩ =
        (.ok ⟨rk, some sc, rcs, pc, mfj⟩, ⟨rk, some sc, rcs, pc, mfj⟩) := rfl
    rw [hg]
    dsimp only
    rw [mut_exec_bind_m]
    have htake : RatchetState.takeRootKey.exec ⟨rk, some sc, rcs, pc, mfj⟩ =
        (.ok rk, ⟨0, some sc, rcs, pc, mfj⟩) := rfl
    rw [htake]
    dsimp only
    rw [mut_exec_bind_m]
    rcases h1 : rootCreateChain C' rk their sc.ratchetKey.privateKey with e1 | ⟨rk1, rck⟩
    · rfl
    · dsimp only [liftE]
      have hp1 : (pure (rk1, rck) : Mut RatchetState _).exec ⟨0, some sc, rcs, pc, mfj⟩ =
          (.ok (rk1, rck), ⟨0, some sc, rcs, pc, mfj⟩) := rfl
      rw [hp1]
      dsimp only
      rw [mut_exec_bind_m]
      rcases h2 : rootCreateChain C' rk1 their (KeyPair.generate C' coins).privateKey with
        e2 | ⟨rk2, sck⟩ <;> rfl

private theorem ensureReceiverChain_exec (C' : Crypto) (their : PublicKey) (coins : BitVec 256)
    (r : RatchetState) :
    (RatchetState.ensureReceiverChain C' their coins).exec r =
      match r.findReceiverChainIndex their with
      | some idx =>
        match r.receiverChains[idx]? with
        | none => (.error .panic, r)
        | some c =>
          match c.chainKey with
          | none => (.error (.invalidSessionStructure .missingReceiverChainKey), r)
          | some ck => (.ok ck, r)
      | none => (RatchetState.dhRatchetStep C' their coins).exec r := by
  unfold RatchetState.ensureReceiverChain
  rw [mut_exec_bind_m]
  have hg : (get : Mut RatchetState RatchetState).exec r = (.ok r, r) := rfl
  rw [hg]
  dsimp only
  rw [mut_exec_bind_m]
  dsimp only [RatchetState.findReceiverChainKey]
  cases hf : r.findReceiverChainIndex their with
  | none => rfl
  | some idx =>
    dsimp only
    cases hget : r.receiverChains[idx]? with
    | none => rfl
    | some c =>
      dsimp only
      cases c.chainKey <;> rfl

private theorem takeSkippedKey_exec (their : PublicKey) (ctr : BitVec 32) (r : RatchetState) :
    (RatchetState.takeSkippedKey their ctr).exec r =
      match r.findReceiverChainIndex their with
      | none => (.ok none, r)
      | some idx =>
        match r.receiverChains[idx]? with
        | none => (.error .panic, r)
        | some c =>
          match c.messageKeys.findIdx? (fun mk => mk.counter == ctr) with
          | none => (.ok none, r)
          | some pos =>
            match c.messageKeys[pos]? with
            | none => (.error .panic, r)
            | some key =>
              (.ok (some key),
               { r with receiverChains :=
                   r.receiverChains.set idx { c with messageKeys := c.messageKeys.eraseIdx pos } }) := by
  unfold RatchetState.takeSkippedKey
  rw [mut_exec_bind_m]
  have hg : (get : Mut RatchetState RatchetState).exec r = (.ok r, r) := rfl
  rw [hg]
  dsimp only
  cases r.findReceiverChainIndex their with
  | none => rfl
  | some idx =>
    dsimp only
    cases r.receiverChains[idx]? with
    | none => rfl
    | some c =>
      dsimp only
      cases c.messageKeys.findIdx? (fun mk => mk.counter == ctr) with
      | none => rfl
      | some pos =>
        dsimp only
        cases c.messageKeys[pos]? <;> rfl

private theorem consumeMessageKey_exec (F : ShaCompress) (their : PublicKey) (ck : ChainKey)
    (ctr : BitVec 32) (mt : MessageType) (r : RatchetState) :
    (RatchetState.consumeMessageKey F their ck ctr mt).exec r =
      if ctr < ck.index then
        match (RatchetState.takeSkippedKey their ctr).exec r with
        | (.error e, r') => (.error e, r')
        | (.ok none, r') => (.error (.duplicatedMessage ck.index ctr), r')
        | (.ok (some k), r') => (.ok k, r')
      else
        let jump := (ctr - ck.index).toNat
        if r.maxForwardJumps < jump then
          (.error (.invalidMessage mt .tooFarInFuture), r)
        else
          match (RatchetState.advanceChain F their ctr jump ck).exec r with
          | (.error e, rOut) => (.error e, rOut)
          | (.ok ckOut, rOut) =>
            match ckOut.nextChainKey F with
            | .error e => (.error e, rOut)
            | .ok ckNext =>
              match (RatchetState.setReceiverChainKey their ckNext).exec rOut with
              | (.error e, r2) => (.error e, r2)
              | (.ok (), r2) => (.ok (ckOut.messageKeys F), r2) := by
  unfold RatchetState.consumeMessageKey
  by_cases hlt : ctr < ck.index
  · simp only [hlt, ↓reduceIte]
    rw [mut_exec_bind_m]
    rcases (RatchetState.takeSkippedKey their ctr).exec r with ⟨e | (_ | k), r'⟩ <;> rfl
  · simp only [hlt, ↓reduceIte]
    rw [mut_exec_bind_m]
    have hg : (get : Mut RatchetState RatchetState).exec r = (.ok r, r) := rfl
    rw [hg]
    dsimp only
    by_cases hj : r.maxForwardJumps < (ctr - ck.index).toNat
    · simp only [hj, ↓reduceIte]
      rfl
    · simp only [hj, ↓reduceIte]
      rw [mut_exec_bind_m]
      rcases (RatchetState.advanceChain F their ctr (ctr - ck.index).toNat ck).exec r with
        ⟨e1 | ckOut, rOut⟩
      · rfl
      · dsimp only
        rw [mut_exec_bind_m]
        rcases ckOut.nextChainKey F with e2 | ckNext
        · rfl
        · dsimp only [liftE]
          have hp2 : (pure ckNext : Mut RatchetState ChainKey).exec rOut = (.ok ckNext, rOut) := rfl
          rw [hp2]
          dsimp only
          rw [mut_exec_bind_m]
          rcases (RatchetState.setReceiverChainKey their ckNext).exec rOut with ⟨e3 | ⟨⟩, r2⟩ <;> rfl

private theorem tripleDecrypt_exec {PQ PQC : Type} (C' : Crypto)
    (spqr : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (expected : Option Bytes) (msg : SignalMessage) (mt : MessageType) (coins : BitVec 256)
    (tr : TripleRatchet PQ) :
    (TripleRatchet.decrypt C' spqr expected msg mt coins).exec tr =
      match (RatchetState.ensureReceiverChain C' msg.senderRatchetKey coins).exec tr.ratchet with
      | (.error e, r1) => (.error e, { tr with ratchet := r1 })
      | (.ok ck, r1) =>
        match (RatchetState.consumeMessageKey C'.F msg.senderRatchetKey ck msg.counter mt).exec r1 with
        | (.error e, r2) => (.error e, { tr with ratchet := r2 })
        | (.ok mkg, r2) =>
          if spqr.recvPanics tr.pqrState msg.pqRatchet then
            (.error .panic, { tr with ratchet := r2 })
          else
            match spqr.recv tr.pqrState msg.pqRatchet with
            | .error true => (.error .invalidState, { tr with ratchet := r2 })
            | .error false => (.error (.invalidMessage mt .pqRatchet), { tr with ratchet := r2 })
            | .ok (newPq, pqKey) =>
              let mks := mkg.generateKeys C'.F pqKey
              if !(msg.verifyMacWithAddresses C'.F expected tr.remoteIdentityKey
                    tr.localIdentityKey mks.macKey) then
                (.error (.invalidMessage mt .macFailed), { tr with ratchet := r2 })
              else
                match aesCbcDecrypt C'.D mks.cipherKey mks.iv msg.ciphertext with
                | none => (.error (.invalidMessage mt .badCiphertext), { tr with ratchet := r2 })
                | some pt => (.ok pt, { tr with ratchet := r2, pqrState := newPq }) := by
  unfold TripleRatchet.decrypt TripleRatchet.onRatchet
  rw [mut_exec_bind_m, mut_exec_zoom_m]
  rcases (RatchetState.ensureReceiverChain C' msg.senderRatchetKey coins).exec tr.ratchet with
    ⟨e1 | ck, r1⟩
  · rfl
  · dsimp only
    rw [mut_exec_bind_m, mut_exec_zoom_m]
    rcases (RatchetState.consumeMessageKey C'.F msg.senderRatchetKey ck msg.counter mt).exec r1 with
      ⟨e2 | mkg, r2⟩
    · rfl
    · dsimp only
      rw [mut_exec_bind_m]
      have hg : (get : Mut (TripleRatchet PQ) (TripleRatchet PQ)).exec { tr with ratchet := r2 } =
          (.ok { tr with ratchet := r2 }, { tr with ratchet := r2 }) := rfl
      rw [hg]
      dsimp only
      by_cases hpan : spqr.recvPanics tr.pqrState msg.pqRatchet
      · simp only [hpan, ↓reduceIte]
        rfl
      · simp only [hpan, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rcases spqr.recv tr.pqrState msg.pqRatchet with (_ | _) | ⟨newPq, pqKey⟩
        · rfl
        · rfl
        · dsimp only
          by_cases hmac : !(msg.verifyMacWithAddresses C'.F expected tr.remoteIdentityKey
              tr.localIdentityKey (mkg.generateKeys C'.F pqKey).macKey)
          · simp only [hmac, ↓reduceIte]
            rfl
          · simp only [hmac, Bool.false_eq_true, ↓reduceIte]
            rcases aesCbcDecrypt C'.D (mkg.generateKeys C'.F pqKey).cipherKey
                (mkg.generateKeys C'.F pqKey).iv msg.ciphertext with _ | pt <;> rfl

private theorem tryDecryptWithState_exec {PQ PQC : Type} [Inhabited PQ] (C' : Crypto)
    (spqr : CryptoGames.LibsignalSession.Spqr PQ PQC)
    (expected : Option Bytes) (msg : SignalMessage) (mt : MessageType) (coins : BitVec 256)
    (s : SessionState PQ) :
    (SessionState.tryDecryptWithState C' spqr expected msg mt coins).exec s =
      match TripleRatchet.fromSessionState.exec s with
      | (.error e, s1) => (.error e, s1)
      | (.ok tr0, s1) =>
        match (TripleRatchet.decrypt C' spqr expected msg mt coins).exec tr0 with
        | (.error e, _) => (.error e, s1)
        | (.ok pt, tr1) =>
          (.ok pt, (tr1.applyToSessionState s1).clearUnacknowledgedPreKeyMessage) := by
  unfold SessionState.tryDecryptWithState
  rw [mut_exec_bind_m]
  rcases TripleRatchet.fromSessionState.exec s with ⟨e1 | tr0, s1⟩
  · rfl
  · dsimp only
    rw [mut_exec_bind_m]
    rcases (TripleRatchet.decrypt C' spqr expected msg mt coins).exec tr0 with ⟨e2 | pt, tr1⟩
    · rfl
    · dsimp only [liftE]
      have hp : (pure pt : Mut (SessionState PQ) Bytes).exec s1 = (.ok pt, s1) := rfl
      rw [hp]
      dsimp only
      rw [mut_exec_bind_m]
      rfl

private theorem findIdx?_eq_some_get {α : Type} (p : α → Bool) :
    ∀ (l : List α) {i : ℕ}, l.findIdx? p = some i → ∃ x, l[i]? = some x ∧ p x = true
  | [], _, h => nomatch h
  | x :: xs, i, h => by
    simp only [List.findIdx?_cons] at h
    cases hp : p x
    · rw [hp] at h
      rcases Option.mem_map.mp h with ⟨j, hj, rfl⟩
      rcases findIdx?_eq_some_get p xs hj with ⟨y, hy, hpy⟩
      exact ⟨y, hy, hpy⟩
    · rw [hp] at h
      injection h with hi
      subst hi
      exact ⟨x, rfl, hp⟩

private theorem findIdx?_eq_none_forall {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.findIdx? p = none → ∀ x ∈ l, p x = false
  | [], _, _, hx => nomatch hx
  | a :: as, h, x, hx => by
    simp only [List.findIdx?_cons] at h
    cases hp : p a
    · rw [hp] at h
      have hnone : as.findIdx? p = none := by
        cases hf : as.findIdx? p with
        | none => rfl
        | some j => rw [hf] at h; cases h
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hp
      · exact findIdx?_eq_none_forall p as hnone x hmem
    · rw [hp] at h
      cases h

private theorem findIdx?_map_eq {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ (l : List α), (l.map f).findIdx? p = l.findIdx? (fun x => p (f x))
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.findIdx?_cons]
    cases p (f x) <;> simp [findIdx?_map_eq f p xs]

private theorem set_map_eq {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : ℕ) (v : α), (l.map f).set i (f v) = (l.set i v).map f
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: xs, i + 1, v => congrArg (f x :: ·) (set_map_eq f xs i v)

private theorem eraseIdx_map_eq {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : ℕ), (l.map f).eraseIdx i = (l.eraseIdx i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: xs, i + 1 => congrArg (f x :: ·) (eraseIdx_map_eq f xs i)

private theorem set_eq_self_of_getElem? {α : Type} :
    ∀ (l : List α) (i : ℕ) (x : α), l[i]? = some x → l.set i x = l
  | [], _, _, h => nomatch h
  | a :: as, 0, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl
  | a :: as, i + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    exact congrArg (a :: ·) (set_eq_self_of_getElem? as i x h)

private theorem mem_set_or_aux {α : Type} :
    ∀ (l : List α) (i : ℕ) (x y : α), y ∈ l.set i x → y = x ∨ y ∈ l
  | [], _, _, _, hy => nomatch hy
  | _ :: as, 0, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ hmem)
  | a :: as, i + 1, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inr List.mem_cons_self
    · rcases mem_set_or_aux as i x y hmem with rfl | hmem'
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a hmem')

private theorem mem_eraseIdx_aux {α : Type} :
    ∀ (l : List α) (i : ℕ) {y : α}, y ∈ l.eraseIdx i → y ∈ l
  | [], _, _, hy => nomatch hy
  | _ :: as, 0, _, hy => List.mem_cons_of_mem _ hy
  | a :: as, i + 1, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_eraseIdx_aux as i hmem)

private theorem mem_take_aux {α : Type} :
    ∀ (n : ℕ) (l : List α) {y : α}, y ∈ l.take n → y ∈ l
  | 0, _, _, hy => nomatch hy
  | _ + 1, [], _, hy => nomatch hy
  | n + 1, a :: as, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_take_aux n as hmem)

private theorem drop_append_of_le {α : Type} :
    ∀ (l r : List α) (k : ℕ), k ≤ l.length → (l ++ r).drop k = l.drop k ++ r
  | l, _, 0, _ => by simp
  | [], _, k + 1, hk => by simp at hk
  | _ :: xs, r, k + 1, hk =>
    drop_append_of_le xs r k (Nat.le_of_succ_le_succ hk)

private theorem mem_of_mem_drop_aux {α : Type} :
    ∀ (l : List α) (k : ℕ) {x : α}, x ∈ l.drop k → x ∈ l
  | _, 0, _, hx => hx
  | [], _ + 1, _, hx => nomatch hx
  | _ :: xs, k + 1, _, hx => List.mem_cons_of_mem _ (mem_of_mem_drop_aux xs k hx)

private theorem findIdx?_append_singleton_of_forall_false {α : Type} (p : α → Bool) (y : α)
    (hy : p y = true) :
    ∀ (l : List α), (∀ x ∈ l, p x = false) →
      (l ++ [y]).findIdx? p = some l.length ∧ (l ++ [y])[l.length]? = some y
  | [], _ => by simp [hy]
  | a :: as, hall => by
    have ha := hall a List.mem_cons_self
    obtain ⟨ih1, _⟩ := findIdx?_append_singleton_of_forall_false p y hy as
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp [List.findIdx?_cons, ha, ih1]

private theorem findIdx?_evict_pushed (rcs : List ReceiverChain) (their : PublicKey) (ck : ChainKey)
    (hlen : rcs.length ≤ 5)
    (hnone : rcs.findIdx? (fun c => c.senderRatchetKey == their) = none) :
    let rcNew : ReceiverChain := ⟨their, some ck, []⟩
    let rcs1 := RatchetState.evictReceiverChains (rcs ++ [rcNew])
    ∃ idx, rcs1.findIdx? (fun c => c.senderRatchetKey == their) = some idx ∧
      rcs1[idx]? = some rcNew := by
  intro rcNew rcs1
  have hk_le : (rcs.length + 1) - 5 ≤ rcs.length := by omega
  have hrcs1_eq : rcs1 = rcs.drop ((rcs.length + 1) - 5) ++ [rcNew] := by
    dsimp only [rcs1, RatchetState.evictReceiverChains, maxReceiverChains]
    simp only [List.length_append, List.length_singleton]
    exact drop_append_of_le rcs [rcNew] ((rcs.length + 1) - 5) hk_le
  have hall_false : ∀ c ∈ rcs.drop ((rcs.length + 1) - 5), (c.senderRatchetKey == their) = false :=
    fun c hc => findIdx?_eq_none_forall _ rcs hnone c (mem_of_mem_drop_aux rcs _ hc)
  have hrcNew : (rcNew.senderRatchetKey == their) = true := beq_self_eq_true their
  obtain ⟨h1, h2⟩ := findIdx?_append_singleton_of_forall_false
    (fun c : ReceiverChain => c.senderRatchetKey == their) rcNew hrcNew
    (rcs.drop ((rcs.length + 1) - 5)) hall_false
  exact ⟨(rcs.drop ((rcs.length + 1) - 5)).length, by rw [hrcs1_eq]; exact h1,
    by rw [hrcs1_eq]; exact h2⟩

private theorem findIdx?_set_same_srk (rcs : List ReceiverChain) (their : PublicKey)
    {i : ℕ} {rc : ReceiverChain} (rc' : ReceiverChain)
    (hfind : rcs.findIdx? (fun c => c.senderRatchetKey == their) = some i)
    (hget : rcs[i]? = some rc)
    (hsrk : rc'.senderRatchetKey = rc.senderRatchetKey) :
    (rcs.set i rc').findIdx? (fun c => c.senderRatchetKey == their) = some i := by
  induction rcs generalizing i with
  | nil => simp at hfind
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [List.set_cons_zero, List.findIdx?_cons, hsrk] at hfind ⊢
      cases hhd : hd.senderRatchetKey == their
      · rw [hhd] at hfind
        rcases Option.mem_map.mp hfind with ⟨j, _, hj⟩
        omega
      · rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.findIdx?_cons, List.set_cons_succ] at hfind ⊢
      cases hhd : hd.senderRatchetKey == their
      · rw [hhd] at hfind
        rcases Option.mem_map.mp hfind with ⟨k, hk, hk_eq⟩
        have hkj : k = j := by omega
        subst hkj
        rw [ih hk hget]
        simp
      · rw [hhd] at hfind
        cases hfind

private theorem advanceChain_preserves_slot (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) :
    ∀ (fuel : ℕ) (ck : ChainKey) (r : RatchetState) (chainIdx : ℕ) (rc : ReceiverChain),
      r.findReceiverChainIndex their = some chainIdx →
      r.receiverChains[chainIdx]? = some rc →
      rc.senderRatchetKey = their →
      rc.messageKeys.length ≤ 2000 →
      (∀ mk ∈ rc.messageKeys, mk.seed.length = 32) →
      ∀ {ckOut : ChainKey} {rOut : RatchetState},
        (RatchetState.advanceChain F their counter fuel ck).exec r = (.ok ckOut, rOut) →
        ∃ rcOut : ReceiverChain,
          rOut.findReceiverChainIndex their = some chainIdx ∧
          rOut.receiverChains[chainIdx]? = some rcOut ∧
          rcOut.senderRatchetKey = their ∧
          (∀ mk ∈ rcOut.messageKeys, mk.seed.length = 32) ∧
          rOut = { r with receiverChains := r.receiverChains.set chainIdx rcOut } := by
  intro fuel
  induction fuel with
  | zero =>
    intro ck r chainIdx rc hfind hget hsrk _ hseed ckOut rOut hexec
    change (Except.ok ck, r) = (Except.ok ckOut, rOut) at hexec
    injection hexec with _ hr
    subst hr
    exact ⟨rc, hfind, hget, hsrk, hseed,
      by simp [set_eq_self_of_getElem? r.receiverChains chainIdx rc hget]⟩
  | succ fuel ih =>
    intro ck r chainIdx rc hfind hget hsrk hmk_le hseed ckOut rOut hexec
    unfold RatchetState.advanceChain at hexec
    by_cases hlt : ck.index < counter
    · simp only [hlt, ↓reduceIte] at hexec
      let keys1 := (ck.messageKeys F :: rc.messageKeys).take 2000
      let rc1 : ReceiverChain := { rc with messageKeys := keys1 }
      let r1 : RatchetState := { r with receiverChains := r.receiverChains.set chainIdx rc1 }
      have hstore : (RatchetState.storeSkippedKey their (ck.messageKeys F)).exec r =
          (.ok (), r1) := by
        unfold RatchetState.storeSkippedKey
        rw [mut_exec_bind_m]
        have hg : (get : Mut RatchetState RatchetState).exec r = (.ok r, r) := rfl
        rw [hg]
        dsimp only
        rw [hfind]
        dsimp only
        rw [hget]
        dsimp only
        rw [storeSkipped_trim_eq_take2000 _ (by simp; omega)]
        rfl
      rw [mut_exec_bind_m, hstore] at hexec
      dsimp only at hexec
      rw [mut_exec_bind_m] at hexec
      rcases hnext : ck.nextChainKey F with err | ck'
      · rw [hnext] at hexec
        cases hexec
      · rw [hnext] at hexec
        dsimp only [liftE] at hexec
        have hp : (pure ck' : Mut RatchetState ChainKey).exec r1 = (.ok ck', r1) := rfl
        rw [hp] at hexec
        dsimp only at hexec
        have hlt_len : chainIdx < r.receiverChains.length :=
          (List.getElem?_eq_some_iff.mp hget).1
        have hget1 : r1.receiverChains[chainIdx]? = some rc1 :=
          List.getElem?_set_self hlt_len
        have hfind1 : r1.findReceiverChainIndex their = some chainIdx :=
          findIdx?_set_same_srk r.receiverChains their rc1 hfind hget rfl
        have hmk1_le : rc1.messageKeys.length ≤ 2000 :=
          List.length_take_le 2000 _
        have hseed1 : ∀ mk ∈ rc1.messageKeys, mk.seed.length = 32 := by
          intro mk hmk
          rcases List.mem_cons.mp (mem_take_aux 2000 _ hmk) with rfl | hmem
          · exact chainKey_messageKeys_seed_len F ck
          · exact hseed mk hmem
        obtain ⟨rcOut, hfO, hgO, hsO, hseedO, hrO⟩ :=
          ih ck' r1 chainIdx rc1 hfind1 hget1 hsrk hmk1_le hseed1 hexec
        refine ⟨rcOut, hfO, hgO, hsO, hseedO, ?_⟩
        rw [hrO]
        dsimp only [r1]
        simp [List.set_set]
    · simp only [hlt, ↓reduceIte] at hexec
      change (Except.ok ck, r) = (Except.ok ckOut, rOut) at hexec
      injection hexec with _ hr
      subst hr
      exact ⟨rc, hfind, hget, hsrk, hseed,
        by simp [set_eq_self_of_getElem? r.receiverChains chainIdx rc hget]⟩

/-! ## Evaluation agreement with `Params.receive` -/

@[reducible] private def envCons (t : Ty S) {Γ : List (Ty S)} (x : t.denote) (ρ : Env Γ) :
    Env (t :: Γ) :=
  Env.cons x ρ

private theorem eval_drRecvPreE {Γ : List (Ty S)}
    (gE : Expr OO Γ GhostStT) (cE : Expr OO Γ (B 32)) (ρ : Env Γ)
    (hg : PartyReachInv C K (gE.eval ρ)) :
    (drRecvPreE gE cE).eval ρ =
      match SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with
      | .error _ => none
      | .ok msg =>
        if (gE.eval ρ).session.version.toNat ≠ msg.messageVersion.toNat then none
        else
          match (gE.eval ρ).session.remoteIdentity with
          | none => none
          | some rem =>
            some (ghostSplitEval (ℓ := ℓ) (gE.eval ρ),
              (rem, (msg.senderRatchetKey, (msg.counter, (msg.ciphertext, msg.pqRatchet))))) := by
  have hparse := e2ePureOps_eval_signalMsgParse_lossless ℓ (cE.eval ρ)
  change E2EPureOp.eval ℓ .signalMsgParse (cE.eval ρ) = _ at hparse
  have hsplitOp :
      E2EPureOp.eval ℓ .ghostStateSplit (gE.eval ρ) =
        (partyToBool (gE.eval ρ).party,
         ((gE.eval ρ).session.sessionVersion,
          ((gE.eval ρ).session.localIdentity,
           ((gE.eval ρ).session.remoteIdentity,
            ((gE.eval ρ).session.rootKey,
             ((gE.eval ρ).session.previousCounter,
              ((gE.eval ρ).session.pendingPreKey,
               ((gE.eval ρ).epoch,
                ((gE.eval ρ).chainEpochs,
                 ((gE.eval ρ).session.senderChain.map (encodeSenderChain (ℓ := ℓ)),
                  ((gE.eval ρ).session.receiverChains.map (encodeRecvChain (ℓ := ℓ)),
                   (gE.eval ρ).session.pqRatchetState))))))))))) :=
    ghostSplitEval_eq_of_le (ℓ := ℓ) hg.receiverChains_le_five
  have hsplit := ghostSplitEval_eq_of_le (ℓ := ℓ) hg.receiverChains_le_five
  simp only [drRecvPreE, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, eval_e2ePureOp]
  rw [hparse]
  rcases SignalMessage.tryFrom protoSignalCodec (cE.eval ρ) with _ | msg
  · rfl
  · dsimp only
    rw [hsplitOp, hsplit]
    dsimp only [gpVer, gpRemId, SessionState.version]
    simp only [eval_sessionVersionEffE, E2EPureOp.eval, Expr.eval, Env.get,
      decide_eq_true_eq, ne_eq]
    by_cases hv :
        (if (gE.eval ρ).session.sessionVersion = 0 then (2 : BitVec 32)
         else (gE.eval ρ).session.sessionVersion).toNat = msg.messageVersion.toNat
    · simp only [hv, not_true_eq_false, ↓reduceIte]
      cases (gE.eval ρ).session.remoteIdentity <;> rfl
    · simp only [hv, not_false_eq_true, ↓reduceIte]

private theorem eval_drRecvChainSetupE {Γ : List (Ty S)}
    (partsE : Expr OO Γ ghostPartsT) (theirE : Expr OO Γ PK) (rcCoinsE : Expr OO Γ BV256)
    (ρ : Env Γ) {g : GhostState Bytes}
    (hg : PartyReachInv C K g)
    (hparts : partsE.eval ρ = ghostSplitEval (ℓ := ℓ) g) :
    let their := theirE.eval ρ
    let rc := rcCoinsE.eval ρ
    let r0 : RatchetState :=
      ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
       g.session.previousCounter, maxForwardJumps⟩
    match (RatchetState.ensureReceiverChain C their rc).exec r0 with
    | (.error _, _) => (drRecvChainSetupE partsE theirE rcCoinsE).eval ρ = none
    | (.ok ck, r1) =>
      ∃ (chainIdx : ℕ) (rcAct : ReceiverChain) (cur' tOut : ℕ) (cEps' : List ℕ),
        (drRecvChainSetupE partsE theirE rcCoinsE).eval ρ =
          some ((r1.rootKey,
                 (r1.previousCounter,
                  (r1.senderChain.map (encodeSenderChain (ℓ := ℓ)),
                   (r1.receiverChains.map (encodeRecvChain (ℓ := ℓ)),
                    (cur', (tOut, cEps')))))),
                ((ck.key, ck.index), rcAct.messageKeys.map encodeMsgKey)) ∧
        r1.findReceiverChainIndex their = some chainIdx ∧
        r1.receiverChains[chainIdx]? = some rcAct ∧
        rcAct.senderRatchetKey = their ∧
        rcAct.chainKey = some ck ∧
        rcAct.messageKeys.length ≤ 2000 ∧
        r1.receiverChains.length ≤ 5 ∧
        (∀ rc' ∈ r1.receiverChains, ∀ mk ∈ rc'.messageKeys, mk.seed.length = 32) ∧
        r1.maxForwardJumps = 25000 ∧
        (∀ len2 : ℕ, len2 = r1.receiverChains.length →
          let idx0 := g.session.receiverChains.findIdx? (·.senderRatchetKey == their)
          let (t0, epochs0, cur0) := match idx0 with
            | some i => (g.chainEpochs.getD i 0, g.chainEpochs, g.epoch)
            | none => (g.epoch + 1, g.chainEpochs ++ [g.epoch + 1], g.epoch + 1)
          cur' = cur0 ∧ tOut = t0 ∧ cEps' = epochs0.drop (epochs0.length - len2)) := by
  intro their rc r0
  have hrc5 := hg.receiverChains_le_five
  have hsplit := ghostSplitEval_eq_of_le (ℓ := ℓ) hrc5
  rw [ensureReceiverChain_exec]
  dsimp only [r0, RatchetState.findReceiverChainIndex]
  let ρ1 := envCons (.prod ghostPartsT (.prod PK BV256)) (partsE.eval ρ, (their, rc)) ρ
  have hrcs_eval :
      (gpRcs (.fst (.v0 : Expr OO _ _))).eval ρ1 =
        g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ)) := by
    simp [ρ1, gpRcs, Expr.eval, Expr.v0, Env.get, hparts, hsplit]
  have hfind_eval := eval_findChainWithIdx5E
    (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (gpRcs (.fst .v0)) (.fst (.snd .v0)) ρ1
    (by rw [hrcs_eval]; simpa using hrc5)
  have hth_eval : (Expr.fst (Expr.snd (.v0 : Expr OO _ _))).eval ρ1 = their := rfl
  rw [hrcs_eval, hth_eval, findIdx?_map_eq] at hfind_eval
  have hpred_eq :
      (fun x : ReceiverChain => (encodeRecvChain (ℓ := ℓ) x).1 == their) =
      (fun x : ReceiverChain => x.senderRatchetKey == their) := rfl
  rw [hpred_eq] at hfind_eval
  cases hidx0 : g.session.receiverChains.findIdx? (fun c => c.senderRatchetKey == their) with
  | some i =>
    rw [hidx0] at hfind_eval
    dsimp only at hfind_eval
    obtain ⟨rcAct, hgetAct, hsrkBool⟩ := findIdx?_eq_some_get _ g.session.receiverChains hidx0
    have hsrk : rcAct.senderRatchetKey = their := beq_iff_eq.mp hsrkBool
    have hgetMap :
        (g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ)))[i]? =
          some (encodeRecvChain (ℓ := ℓ) rcAct) := by
      simp [hgetAct]
    rw [hgetMap] at hfind_eval
    have hsetup_some :
        (drRecvChainSetupE partsE theirE rcCoinsE).eval ρ =
          match rcAct.chainKey with
          | none => none
          | some ck =>
            some ((g.session.rootKey,
                   (g.session.previousCounter,
                    (g.session.senderChain.map (encodeSenderChain (ℓ := ℓ)),
                     (g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ)),
                      (g.epoch, (g.chainEpochs.getD i 0, g.chainEpochs)))))),
                  ((ck.key, ck.index), rcAct.messageKeys.map encodeMsgKey)) := by
      simp only [drRecvChainSetupE, Expr.eval]
      change (let v := (findChainWithIdx5E (ℓ := ℓ) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (gpRcs (.fst .v0)) (.fst (.snd .v0))).eval ρ1; _) = _
      rw [hfind_eval]
      simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get, encodeRecvChain]
      rcases hck : rcAct.chainKey with _ | ck
      · rfl
      · simp only [Option.map, encodeChainKey]
        have hcEps_len : g.chainEpochs.length ≤ 5 := by rw [hg.aligned]; exact hrc5
        let ρ4 :=
          envCons (.prod BV256 U32) (ck.key, ck.index)
            (envCons drRecvChainT (encodeRecvChain (ℓ := ℓ) rcAct)
              (envCons (.prod .nat (.opt drRecvChainT))
                (i, some (encodeRecvChain (ℓ := ℓ) rcAct)) ρ1))
        have hceps_eval :
            (getDZero5E (O' := OO) (gpCEps (.fst .v3)) (.fst .v2)).eval ρ4 =
            g.chainEpochs.getD i 0 := by
          rw [eval_getDZero5E _ _ ρ4
            (by simp [ρ4, ρ1, envCons, gpCEps, Expr.eval, Expr.v3, Env.get, hparts, hsplit,
              hcEps_len])]
          simp [ρ4, ρ1, envCons, gpCEps, Expr.eval, Expr.v2, Expr.v3, Env.get, hparts, hsplit]
        simp only [Expr.v2, Expr.v3, ρ4, ρ1, envCons, encodeRecvChain, hck, Option.map,
          encodeChainKey, their, rc] at hceps_eval
        rw [hceps_eval]
        simp only [gpRk, gpPrevCtr, gpSc, gpRcs, gpEp, gpCEps,
          Expr.eval, Env.get, hparts, hsplit]
        rfl
    dsimp only
    rw [hgetAct, hsetup_some]
    dsimp only
    rcases hck : rcAct.chainKey with _ | ck
    · rfl
    · dsimp only
      have hact_mem : rcAct ∈ g.session.receiverChains := List.mem_of_getElem? hgetAct
      refine ⟨i, rcAct, g.epoch, g.chainEpochs.getD i 0, g.chainEpochs, rfl,
        hidx0, hgetAct, hsrk, hck, hg.messageKeys_le_2000 rcAct hact_mem, hrc5,
        hg.messageKeySeed_eq, rfl, ?_⟩
      intro len2 hlen2
      simp [hlen2, hg.aligned]
  | none =>
    let v0 :=
      (findChainWithIdx5E (ℓ := ℓ) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (gpRcs (.fst .v0)) (.fst (.snd .v0))).eval ρ1
    rw [hidx0] at hfind_eval
    change v0.2 = none at hfind_eval
    have hv0 :
        (findChainWithIdx5E (ℓ := ℓ) (P := P) (C := C) (K := K)
          (decT := decT) (encT := encT) (gpRcs (.fst .v0)) (.fst (.snd .v0))).eval ρ1 =
          (v0.1, none) :=
      Prod.ext rfl hfind_eval
    have hsetup_none :
        (drRecvChainSetupE partsE theirE rcCoinsE).eval ρ =
          (drRecvDhStepE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            (.fst .v1) (.fst (.snd .v1)) (.snd (.snd .v1))).eval
            (envCons (.prod .nat (.opt drRecvChainT)) (v0.1, none) ρ1) := by
      simp only [drRecvChainSetupE, Expr.eval]
      change (let v := (findChainWithIdx5E (ℓ := ℓ) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (gpRcs (.fst .v0)) (.fst (.snd .v0))).eval ρ1; _) = _
      rw [hv0]
      rfl
    rw [dhRatchetStep_exec, hsetup_none]
    dsimp only
    simp only [drRecvDhStepE, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get, envCons,
      ρ1, hparts, hsplit, gpSc, gpRk, gpRcs, gpEp, gpCEps]
    rcases hsc : g.session.senderChain with _ | sc
    · rfl
    · dsimp only [Option.map]
      simp only [eval_e2eCryptoOp, E2ECryptoOp.eval, Expr.eval, Env.get]
      have hpriv1 :
          (⟨keyToBytesVec32 (encodeSenderChain (ℓ := ℓ) sc).1.2⟩ :
            CryptoGames.LibsignalSession.PrivateKey) =
          sc.ratchetKey.privateKey := by
        dsimp only [encodeSenderChain]
        exact privateKey_roundtrip sc.ratchetKey.privateKey
      rw [hpriv1]
      rcases hrc1 : rootCreateChain C g.session.rootKey their sc.ratchetKey.privateKey with
        _ | ⟨rk1, rck⟩
      · rfl
      · dsimp only
        simp only [privateKey_roundtrip]
        rcases hrc2 : rootCreateChain C rk1 their (KeyPair.generate C rc).privateKey with
          _ | ⟨rk2, sck⟩
        · rfl
        · dsimp only
          have hrck0 : rck = ⟨rck.key, 0⟩ := by
            have hz := rootCreateChain_index_zero C g.session.rootKey their
              sc.ratchetKey.privateKey hrc1
            cases rck; subst hz; rfl
          have hsck0 : sck = ⟨sck.key, 0⟩ := by
            have hz := rootCreateChain_index_zero C rk1 their
              (KeyPair.generate C rc).privateKey hrc2
            cases sck; subst hz; rfl
          let newKp := KeyPair.generate C rc
          let rcNew : ReceiverChain := ⟨their, some rck, []⟩
          let rcs1 := RatchetState.evictReceiverChains (g.session.receiverChains ++ [rcNew])
          obtain ⟨chainIdx, hfind1, hget1⟩ :=
            findIdx?_evict_pushed g.session.receiverChains their rck hrc5 hidx0
          let ρdh :=
            envCons (.prod BV256 BV256) (rk2, sck.key)
              (envCons (.prod PK BV256)
                (newKp.publicKey, bytesToKey32 newKp.privateKey.bytes.toList)
                (envCons (.prod BV256 BV256) (rk1, rck.key)
                  (envCons drSenderChainT (encodeSenderChain (ℓ := ℓ) sc)
                    (envCons (.prod ghostPartsT (.prod PK BV256))
                      (ghostSplitEval (ℓ := ℓ) g, (their, rc))
                      (envCons (.prod .nat (.opt drRecvChainT))
                        (v0.1, none)
                        ρ1)))))
          have hpush_rcs := eval_pushEvict5E
            (gpRcs (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) : Expr OO _ _)
            (.pair (.fst (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
              (.pair (.some (.pair (.snd .v2) (e2ePureOp (.u32Lit 0#32) .unit))) .nil))
            ρdh
            (by simp [ρdh, envCons, gpRcs, Expr.eval, Env.get, hsplit]; exact hrc5)
          have hpush_ceps := eval_pushEvict5E
            (gpCEps (.fst (.var (.succ (.succ (.succ (.succ .zero)))))) : Expr OO _ _)
            (.add (gpEp (.fst (.var (.succ (.succ (.succ (.succ .zero))))))) (.nat 1))
            ρdh
            (by simp [ρdh, envCons, gpCEps, Expr.eval, Env.get, hsplit, hg.aligned]; exact hrc5)
          have hrcs1_len : rcs1.length ≤ 5 := by
            dsimp only [rcs1, RatchetState.evictReceiverChains, maxReceiverChains]
            simp only [List.length_drop, List.length_append, List.length_singleton]
            omega
          have hrcs1_seed : ∀ rc' ∈ rcs1, ∀ mk ∈ rc'.messageKeys, mk.seed.length = 32 := by
            intro rc' hrc' mk hmk
            have hmem := mem_of_mem_drop_aux (g.session.receiverChains ++ [rcNew]) _ hrc'
            rcases List.mem_append.mp hmem with h_old | h_new
            · exact hg.messageKeySeed_eq rc' h_old mk hmk
            · simp only [List.mem_singleton] at h_new
              subst h_new
              nomatch hmk
          refine ⟨chainIdx, rcNew, g.epoch + 1, g.epoch + 1,
            (g.chainEpochs ++ [g.epoch + 1]).drop ((g.chainEpochs.length + 1) - 5),
            ?_, hfind1, hget1, rfl, rfl, by simp [rcNew], hrcs1_len, hrcs1_seed, rfl, ?_⟩
          · change some _ = some _
            simp only [ρdh, ρ1, envCons, gpRcs, gpEp, gpCEps, Expr.v2, hparts, hsplit,
              hsc, Option.map, newKp] at hpush_rcs hpush_ceps
            rw [hpush_rcs, hpush_ceps]
            simp only [Expr.eval, Env.get, eval_e2ePureOp, E2EPureOp.eval, beq_iff_eq]
            have hsc_idx : (encodeSenderChain (ℓ := ℓ) sc).2.2 = sc.chainKey.index := rfl
            have hnew_sc :
                ((newKp.publicKey, bytesToKey32 newKp.privateKey.bytes.toList), (sck.key, 0#32)) =
                  encodeSenderChain (ℓ := ℓ) ⟨newKp, sck⟩ := by
              rw [hsck0]; rfl
            have hnew_rc :
                (their, (some (rck.key, 0#32), ([] : List (BitVec 256 × BitVec 32)))) =
                  encodeRecvChain (ℓ := ℓ) rcNew := by
              dsimp only [rcNew, encodeRecvChain, encodeChainKey]
              rw [hrck0]; rfl
            have hmap_evict :
                (g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ)) ++
                  [encodeRecvChain (ℓ := ℓ) rcNew]).drop
                    (((g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ))).length + 1) - 5) =
                rcs1.map (encodeRecvChain (ℓ := ℓ)) := by
              simp [rcs1, RatchetState.evictReceiverChains, maxReceiverChains,
                List.map_drop, List.map_append]
            rw [hsc_idx, hnew_sc, hnew_rc, hmap_evict]
            have hrck_idx : rck.index = 0#32 := by rw [hrck0]; rfl
            rw [hrck_idx]
            rfl
          · intro len2 hlen2
            refine ⟨rfl, rfl, ?_⟩
            dsimp only [RatchetState.evictReceiverChains, maxReceiverChains] at hlen2
            simp only [List.length_drop, List.length_append, List.length_singleton] at hlen2
            have hsub_eq :
                (g.chainEpochs ++ [g.epoch + 1]).length - len2 =
                  (g.chainEpochs.length + 1) - 5 := by
              simp only [List.length_append, List.length_singleton, hlen2, hg.aligned]
              omega
            rw [hsub_eq]

private theorem advanceSingleChainC_eval_eq_advanceChain {ι : Type} {T : OracleSpec ι}
    (I : Iface S T) {Γ : List (Ty S)}
    (ckInit : Expr OO Γ (.prod BV256 U32))
    (mksInit : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32) (ρ : Env Γ)
    (their : PublicKey) (ck : ChainKey) (r : RatchetState) (chainIdx : ℕ) (rc : ReceiverChain)
    (hckInit : ckInit.eval ρ = (ck.key, ck.index))
    (hmksInit : mksInit.eval ρ = rc.messageKeys.map encodeMsgKey)
    (hle : ck.index ≤ targetCtr.eval ρ)
    (hj_le : (targetCtr.eval ρ - ck.index).toNat ≤ 25000)
    (hfind : r.findReceiverChainIndex their = some chainIdx)
    (hget : r.receiverChains[chainIdx]? = some rc)
    (hmk_le : rc.messageKeys.length ≤ 2000) :
    (advanceSingleChainC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I ckInit mksInit targetCtr).eval ρ =
      pure (
        match (RatchetState.advanceChain C.F their (targetCtr.eval ρ)
            (targetCtr.eval ρ - ck.index).toNat ck).exec r with
        | (.ok ckOut, rOut) =>
          match rOut.receiverChains[chainIdx]? with
          | some rcOut => some ((ckOut.key, ckOut.index), rcOut.messageKeys.map encodeMsgKey)
          | none => none
        | (.error _, _) => none) := by
  refine Eq.trans (advanceSingleChainC_eval_iterate I ckInit mksInit targetCtr ρ)
    (congrArg pure ?_)
  rw [hckInit, hmksInit]
  exact chainAdvStepFn_iterate_eq_advanceChain C.F their (targetCtr.eval ρ)
    (targetCtr.eval ρ - ck.index).toNat 25000 ck r chainIdx rc
    hle (BitVec.toNat_sub_of_le hle).symm hj_le hfind hget hmk_le

private theorem drRecvConsumeC_eval {ι : Type} {T : OracleSpec ι} (I : Iface S T)
    {Γ : List (Ty S)}
    (theirE : Expr OO Γ PK) (msgCtrE : Expr OO Γ U32)
    (rcs1E : Expr OO Γ (.list drRecvChainT)) (activeE : Expr OO Γ (drChainActiveT ℓ))
    (ρ : Env Γ) {r1 : RatchetState} {ck : ChainKey} {chainIdx : ℕ} {rcAct : ReceiverChain}
    (hrcs1 : rcs1E.eval ρ = r1.receiverChains.map (encodeRecvChain (ℓ := ℓ)))
    (hact : activeE.eval ρ = ((ck.key, ck.index), rcAct.messageKeys.map encodeMsgKey))
    (hfind : r1.findReceiverChainIndex (theirE.eval ρ) = some chainIdx)
    (hget : r1.receiverChains[chainIdx]? = some rcAct)
    (hsrk : rcAct.senderRatchetKey = theirE.eval ρ)
    (hck : rcAct.chainKey = some ck)
    (hmk_le : rcAct.messageKeys.length ≤ 2000)
    (hr1_le : r1.receiverChains.length ≤ 5)
    (hr1_seed : ∀ rc' ∈ r1.receiverChains, ∀ mk ∈ rc'.messageKeys, mk.seed.length = 32)
    (hmfj : r1.maxForwardJumps = 25000) :
    match (RatchetState.consumeMessageKey C.F (theirE.eval ρ) ck (msgCtrE.eval ρ) .whisper).exec r1 with
    | (.error _, _) =>
      (drRecvConsumeC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I theirE msgCtrE rcs1E activeE).eval ρ = pure none
    | (.ok mkg, r2) =>
      (drRecvConsumeC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I theirE msgCtrE rcs1E activeE).eval ρ =
        pure (some (encodeMsgKey mkg, r2.receiverChains.map (encodeRecvChain (ℓ := ℓ)))) ∧
      mkg.seed.length = 32 ∧
      r2.receiverChains.length = r1.receiverChains.length ∧
      (∀ rc' ∈ r2.receiverChains, ∀ mk ∈ rc'.messageKeys, mk.seed.length = 32) ∧
      r2.rootKey = r1.rootKey ∧
      r2.previousCounter = r1.previousCounter ∧
      r2.senderChain = r1.senderChain := by
  set their := theirE.eval ρ with htheir_def
  set ctr := msgCtrE.eval ρ with hctr_def
  have hact_mem : rcAct ∈ r1.receiverChains := List.mem_of_getElem? hget
  have hact_seed : ∀ mk ∈ rcAct.messageKeys, mk.seed.length = 32 := hr1_seed rcAct hact_mem
  have hfind_enc :
      (r1.receiverChains.map (encodeRecvChain (ℓ := ℓ))).findIdx?
        (fun c => c.1 == their) = some chainIdx := by
    rw [findIdx?_map_eq]
    exact hfind
  rw [consumeMessageKey_exec]
  simp only [drRecvConsumeC, Comp.eval, Expr.eval, Expr.v0, Env.get, pure_bind,
    eval_e2ePureOp, E2EPureOp.eval, ← htheir_def, ← hctr_def, hrcs1, hact, decide_eq_true_eq]
  by_cases hlt : ctr < ck.index
  · simp only [hlt, ↓reduceIte]
    rw [takeSkippedKey_exec, hfind]
    dsimp only
    rw [hget]
    dsimp only
    let valT : (Ty.prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ))).denote :=
      ((their, ctr),
       (r1.receiverChains.map (encodeRecvChain (ℓ := ℓ)),
        ((ck.key, ck.index), rcAct.messageKeys.map encodeMsgKey)))
    let ρt := envCons (.prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ))) valT ρ
    let ρt2 := envCons (.prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ))) valT ρt
    have htake := eval_takeSkippedFromListE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (.snd (.snd (.snd .v0))) (.snd (.fst .v0)) ρt2
      (by simp only [ρt2, valT, envCons, Expr.eval, Expr.v0, Env.get, List.length_map]; exact hmk_le)
    have hmks_eval :
        (Expr.snd (Expr.snd (Expr.snd (.v0 : Expr OO _ _)))).eval ρt2 =
          rcAct.messageKeys.map encodeMsgKey := rfl
    have hctr_eval : (Expr.snd (Expr.fst (.v0 : Expr OO _ _))).eval ρt2 = ctr := rfl
    rw [hmks_eval, hctr_eval, findIdx?_map_eq] at htake
    have hpred_mk :
        (fun x : MessageKeyGenerator => (encodeMsgKey x).2 == ctr) =
        (fun x : MessageKeyGenerator => x.counter == ctr) := rfl
    rw [hpred_mk] at htake
    cases hpos : rcAct.messageKeys.findIdx? (fun mk => mk.counter == ctr) with
    | none =>
      dsimp only
      rw [hpos] at htake
      dsimp only [Expr.v0, ρt2, ρt, valT, envCons] at htake
      simp only [drRecvTakeSkippedE, Expr.eval, Expr.v0, Env.get]
      rw [htake]
    | some pos =>
      rw [hpos] at htake
      dsimp only at htake
      obtain ⟨key, hkey_get, _⟩ := findIdx?_eq_some_get _ rcAct.messageKeys hpos
      have hkey_map : (rcAct.messageKeys.map encodeMsgKey)[pos]? = some (encodeMsgKey key) := by
        simp [hkey_get]
      rw [hkey_map] at htake
      dsimp only [Expr.v0, ρt2, ρt, valT, envCons] at htake ⊢
      rw [hkey_get]
      dsimp only
      let ρrep :=
        envCons (.prod BV256 U32) (encodeMsgKey key)
          (envCons (.prod (.opt (.prod BV256 U32)) (.list (.prod BV256 U32)))
            (some (encodeMsgKey key), (rcAct.messageKeys.map encodeMsgKey).eraseIdx pos) ρt2)
      have hrep := eval_replaceFirstChain5E
        (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (.fst (.snd .v2)) (.fst (.fst .v2))
        (.pair (.fst (.fst .v2)) (.pair (.some (.fst (.snd (.snd .v2)))) (.snd .v1)))
        ρrep
        (by simp only [ρrep, ρt2, valT, envCons, Expr.eval, Expr.v2, Env.get, List.length_map]; exact hr1_le)
        (by simp only [ρrep, ρt2, valT, envCons, Expr.eval, Expr.v2, Env.get]; exact hfind_enc)
      let rcUpd : ReceiverChain := { rcAct with messageKeys := rcAct.messageKeys.eraseIdx pos }
      have hnew_enc :
          (their, (some (ck.key, ck.index), (rcAct.messageKeys.map encodeMsgKey).eraseIdx pos)) =
            encodeRecvChain (ℓ := ℓ) rcUpd := by
        dsimp only [rcUpd, encodeRecvChain, encodeChainKey]
        rw [eraseIdx_map_eq, ← hsrk, hck]
        rfl
      have hkey_mem : key ∈ rcAct.messageKeys := List.mem_of_getElem? hkey_get
      refine ⟨?_, hact_seed key hkey_mem, List.length_set, ?_, rfl, rfl, rfl⟩
      · simp only [drRecvTakeSkippedE, Expr.eval, Expr.v0, Env.get]
        rw [htake]
        dsimp only [Expr.v0, Expr.v1, Expr.v2, Env.get]
        refine congrArg pure (congrArg some (Prod.ext rfl ?_))
        dsimp only [Expr.v0, Expr.v1, Expr.v2, ρrep, ρt2, ρt, valT, envCons] at hrep
        rw [hrep]
        simp only [Expr.eval, Env.get]
        rw [hnew_enc, set_map_eq]
      · intro rc' hrc' mk hmk
        rcases mem_set_or_aux r1.receiverChains chainIdx rcUpd rc' hrc' with rfl | h_old
        · exact hact_seed mk (mem_eraseIdx_aux rcAct.messageKeys pos hmk)
        · exact hr1_seed rc' h_old mk hmk
  · simp only [hlt, ↓reduceIte, hmfj]
    by_cases hj : 25000 < (ctr - ck.index).toNat
    · simp only [hj, ↓reduceIte]
    · simp only [hj, ↓reduceIte]
      have hle_ck : ck.index ≤ ctr := BitVec.not_lt.mp hlt
      have hj_le : (ctr - ck.index).toNat ≤ 25000 := Nat.le_of_not_lt hj
      let ρadv := envCons (.prod (.prod PK U32) (.prod (.list drRecvChainT) (drChainActiveT ℓ)))
        ((their, ctr),
         (r1.receiverChains.map (encodeRecvChain (ℓ := ℓ)),
          ((ck.key, ck.index), rcAct.messageKeys.map encodeMsgKey))) ρ
      have hadv := advanceSingleChainC_eval_eq_advanceChain
        (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I
        (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0))) (.snd (.fst .v0)) ρadv
        their ck r1 chainIdx rcAct rfl rfl hle_ck hj_le hfind hget hmk_le
      have hctr_adv : (Expr.snd (Expr.fst (.v0 : Expr OO _ _))).eval ρadv = ctr := rfl
      rw [hctr_adv] at hadv
      rcases hadv_ex : (RatchetState.advanceChain C.F their ctr (ctr - ck.index).toNat ck).exec r1 with
        ⟨err | ckOut, rOut⟩
      · rw [hadv_ex] at hadv
        dsimp only at hadv ⊢
        change ((advanceSingleChainC (ℓ := ℓ) (P := P) (C := C) (K := K)
          (decT := decT) (encT := encT) I (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
          (.snd (.fst .v0))).eval ρadv >>= _) = pure none
        rw [hadv, pure_bind]
      · rw [hadv_ex] at hadv
        dsimp only at hadv ⊢
        obtain ⟨rcOut, hfOut, hgOut, hsrkOut, hseedOut, hrOut_eq⟩ :=
          advanceChain_preserves_slot C.F their ctr (ctr - ck.index).toNat ck r1 chainIdx rcAct
            hfind hget hsrk hmk_le hact_seed hadv_ex
        rcases hnext : ckOut.nextChainKey C.F with _ | ckNext
        · dsimp only
          change ((advanceSingleChainC (ℓ := ℓ) (P := P) (C := C) (K := K)
            (decT := decT) (encT := encT) I (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
            (.snd (.fst .v0))).eval ρadv >>= _) = pure none
          rw [hadv, pure_bind, hgOut]
          dsimp only [Expr.v0, Expr.v2, Env.get]
          simp only [drRecvAfterAdvE, Expr.eval, Expr.v0, Expr.v1, Env.get,
            eval_e2eCryptoOp, E2ECryptoOp.eval]
          have hckOut_eq : ({ key := ckOut.key, index := ckOut.index } : ChainKey) = ckOut := by
            cases ckOut; rfl
          rw [hckOut_eq, hnext]
        · dsimp only
          have hset_exec :
              (RatchetState.setReceiverChainKey their ckNext).exec rOut =
                (.ok (),
                 { rOut with receiverChains :=
                     rOut.receiverChains.set chainIdx { rcOut with chainKey := some ckNext } }) := by
            unfold RatchetState.setReceiverChainKey
            rw [mut_exec_bind_m]
            have hg : (get : Mut RatchetState RatchetState).exec rOut = (.ok rOut, rOut) := rfl
            rw [hg]
            dsimp only
            rw [hfOut]
            dsimp only
            rw [hgOut]
            rfl
          rw [hset_exec]
          dsimp only
          let rcFinal : ReceiverChain := { rcOut with chainKey := some ckNext }
          have hr2_rcs :
              rOut.receiverChains.set chainIdx rcFinal =
                r1.receiverChains.set chainIdx rcFinal := by
            rw [hrOut_eq]
            dsimp only
            exact List.set_set rcOut
          let ρafter :=
            envCons (.prod (.prod BV256 U32) BV256)
              ((ckNext.key, ckNext.index), bytesToKey32 (ckOut.messageKeys C.F).seed)
              (envCons (.prod PK (.prod (.list drRecvChainT) (drChainActiveT ℓ)))
                (their,
                 (r1.receiverChains.map (encodeRecvChain (ℓ := ℓ)),
                  ((ckOut.key, ckOut.index), rcOut.messageKeys.map encodeMsgKey)))
                (envCons (drChainActiveT ℓ)
                  ((ckOut.key, ckOut.index), rcOut.messageKeys.map encodeMsgKey)
                  (envCons (.opt (drChainActiveT ℓ))
                    (some ((ckOut.key, ckOut.index), rcOut.messageKeys.map encodeMsgKey))
                    ρadv)))
          have hrep := eval_replaceFirstChain5E
            (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            (.fst (.snd .v1)) (.fst .v1)
            (.pair (.fst .v1) (.pair (.some (.fst .v0)) (.snd (.snd (.snd .v1)))))
            ρafter
            (by simp only [ρafter, envCons, Expr.eval, Expr.v1, Env.get, List.length_map]; exact hr1_le)
            (by simp only [ρafter, envCons, Expr.eval, Expr.v1, Env.get]; exact hfind_enc)
          have hfinal_enc :
              (their, (some (ckNext.key, ckNext.index), rcOut.messageKeys.map encodeMsgKey)) =
                encodeRecvChain (ℓ := ℓ) rcFinal := by
            dsimp only [rcFinal, encodeRecvChain, encodeChainKey]
            rw [← hsrkOut]
            rfl
          refine ⟨?_, chainKey_messageKeys_seed_len C.F ckOut, ?_, ?_, ?_, ?_, ?_⟩
          · change ((advanceSingleChainC (ℓ := ℓ) (P := P) (C := C) (K := K)
              (decT := decT) (encT := encT) I (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
              (.snd (.fst .v0))).eval ρadv >>= _) = _
            rw [hadv, pure_bind, hgOut]
            dsimp only [Expr.v0, Expr.v2, Env.get]
            simp only [drRecvAfterAdvE, Expr.eval, Expr.v0, Expr.v1, Env.get,
              eval_e2eCryptoOp, E2ECryptoOp.eval]
            have hckOut_eq : ({ key := ckOut.key, index := ckOut.index } : ChainKey) = ckOut := by
              cases ckOut; rfl
            rw [hckOut_eq, hnext]
            refine congrArg pure (congrArg some (Prod.ext rfl ?_))
            dsimp only [Expr.v0, Expr.v1, ρafter, ρadv, envCons] at hrep ⊢
            rw [hrep]
            simp only [Expr.eval, Env.get]
            rw [hfinal_enc, set_map_eq, hr2_rcs]
          · rw [hr2_rcs, List.length_set]
          · intro rc' hrc' mk hmk
            rw [hr2_rcs] at hrc'
            rcases mem_set_or_aux r1.receiverChains chainIdx rcFinal rc' hrc' with rfl | h_old
            · exact hseedOut mk hmk
            · exact hr1_seed rc' h_old mk hmk
          · rw [hrOut_eq]
          · rw [hrOut_eq]
          · rw [hrOut_eq]

private theorem eval_deriveMsgKeys_op (x : (E2ECryptoOp.dom ℓ .deriveMsgKeys).denote) :
    E2ECryptoOp.eval ℓ P C K .deriveMsgKeys x =
      let mks := MessageKeyGenerator.generateKeys C.F ⟨keyToBytes32 x.1, x.2.1⟩
        (x.2.2.map keyToBytesVec32)
      (mks.cipherKey, (mks.macKey, (mks.iv, mks.counter))) := by
  rcases x with ⟨_, _, _⟩; rfl

private theorem eval_signalMsgVerifyMac_op
    (x : (E2ECryptoOp.dom ℓ .signalMsgVerifyMac).denote) :
    E2ECryptoOp.eval ℓ P C K .signalMsgVerifyMac x =
      match SignalMessage.tryFrom protoSignalCodec x.1 with
      | .ok m => m.verifyMacWithAddresses C.F x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
      | .error _ => false := by
  rcases x with ⟨_, _, _, _, _⟩; rfl

private theorem eval_expectedAddrsE_eq_prm {Γ} (isB : Expr OO Γ .bool) (ρ : Env Γ)
    (idA idB : IdentityKey) :
    (expectedAddrsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB).eval ρ =
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).expectedAddrs
        (boolToParty (isB.eval ρ)) := by
  rw [eval_expectedAddrsE]
  cases boolToParty (isB.eval ρ) <;> rfl

theorem drReceiveC_eval_core (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod (B 32) BV256))) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (hg : PartyReachInv C K (e.eval ρ).1) :
    (drReceiveC hooks I e).eval ρ =
      pure (
        let (g, (c, rc)) := e.eval ρ
        let prm := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
        match SignalMessage.tryFrom prm.codec c with
        | .error _ => none
        | .ok msg =>
          if g.session.version.toNat ≠ msg.messageVersion.toNat then none
          else
            match TripleRatchet.fromSessionState.exec g.session with
            | (.error _, _) => none
            | (.ok tr0, s1) =>
              match (RatchetState.ensureReceiverChain prm.C msg.senderRatchetKey rc).exec
                  tr0.ratchet with
              | (.error _, _) => none
              | (.ok ck, r1) =>
                match (RatchetState.consumeMessageKey prm.C.F msg.senderRatchetKey ck msg.counter
                    .whisper).exec r1 with
                | (.error _, _) => none
                | (.ok mkg, r2) =>
                  if prm.spqr.recvPanics tr0.pqrState msg.pqRatchet then none
                  else
                    match prm.spqr.recv tr0.pqrState msg.pqRatchet with
                    | .error _ => none
                    | .ok (newPq, pqKey) =>
                      let mks := mkg.generateKeys prm.C.F pqKey
                      if !(msg.verifyMacWithAddresses prm.C.F (prm.expectedAddrs g.party)
                            tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey) then
                        none
                      else
                        match (e2eCryptoOps ℓ P C K).eval .aes256CbcDec
                            (mks.cipherKey, (mks.iv, msg.ciphertext)) with
                        | none => none
                        | some pt =>
                          let tr1 : TripleRatchet Bytes := { tr0 with ratchet := r2, pqrState := newPq }
                          let s' := (tr1.applyToSessionState s1).clearUnacknowledgedPreKeyMessage
                          let idx0 := g.session.receiverChains.findIdx?
                            (·.senderRatchetKey == msg.senderRatchetKey)
                          let (t, epochs, cur) := match idx0 with
                            | some i => (g.chainEpochs.getD i 0, g.chainEpochs, g.epoch)
                            | none => (g.epoch + 1, g.chainEpochs ++ [g.epoch + 1], g.epoch + 1)
                          let epochs := epochs.drop (epochs.length - s'.receiverChains.length)
                          some ({ g with session := s', epoch := cur, chainEpochs := epochs },
                            (t, (msg.counter.toNat + 1, pt)))) := by
  rcases he : e.eval ρ with ⟨g, ⟨c, rc⟩⟩
  rw [he] at hg
  let spqr := spqrV1SessionUniformCoins C.F K
  let prm := paramsIdsWithSpqr C spqr idA idB
  have hprmCodec : prm.codec = protoSignalCodec := rfl
  have hprmC : prm.C = C := rfl
  have hprmSpqr : prm.spqr = spqr := rfl
  let tIn : Ty S := .prod GhostStT (.prod (B 32) BV256)
  let tPreVal : Ty S := .prod ghostPartsT (.prod IdKey (drRecvMsgT ℓ))
  let tSetVal : Ty S := .prod (drRatchetMidT ℓ) (drChainActiveT ℓ)
  let tConsVal : Ty S := .prod (.prod BV256 U32) (.list drRecvChainT)
  simp only [drReceiveC, Comp.eval, Expr.eval, pure_bind, he]
  have hpre :
      (drRecvPreE (.fst .v0) (.fst (.snd .v0))).eval (envCons tIn (g, (c, rc)) ρ) =
        match SignalMessage.tryFrom protoSignalCodec c with
        | .error _ => none
        | .ok msg =>
          if g.session.version.toNat ≠ msg.messageVersion.toNat then none
          else
            match g.session.remoteIdentity with
            | none => none
            | some rem =>
              some (ghostSplitEval (ℓ := ℓ) g,
                (rem, (msg.senderRatchetKey, (msg.counter, (msg.ciphertext, msg.pqRatchet))))) :=
    eval_drRecvPreE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (.fst .v0) (.fst (.snd .v0)) (envCons tIn (g, (c, rc)) ρ) hg
  rw [hpre, hprmCodec, hprmC, hprmSpqr]
  rcases htry : SignalMessage.tryFrom protoSignalCodec c with _ | msg
  · rfl
  · dsimp only
    by_cases hver : g.session.version.toNat = msg.messageVersion.toNat
    · simp only [hver, ne_eq, not_true_eq_false, ↓reduceIte]
      rw [tripleFromSessionState_exec]
      rcases hrem : g.session.remoteIdentity with _ | remId
      · rfl
      · dsimp only
        let preVal : tPreVal.denote :=
          (ghostSplitEval (ℓ := ℓ) g,
           (remId, (msg.senderRatchetKey, (msg.counter, (msg.ciphertext, msg.pqRatchet)))))
        let ρ2 := envCons tPreVal preVal (envCons tIn (g, (c, rc)) ρ)
        have hsetup := eval_drRecvChainSetupE
          (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          (.fst .v0) (.fst (.snd (.snd .v0))) (.snd (.snd .v1)) ρ2 hg rfl
        have hth2 : (Expr.fst (Expr.snd (Expr.snd (.v0 : Expr OO _ _)))).eval ρ2 =
            msg.senderRatchetKey := rfl
        have hrc2 : (Expr.snd (Expr.snd (.v1 : Expr OO _ _))).eval ρ2 = rc := rfl
        dsimp only at hsetup
        let r0 : RatchetState :=
          ⟨g.session.rootKey, g.session.senderChain, g.session.receiverChains,
           g.session.previousCounter, maxForwardJumps⟩
        rcases hens : (RatchetState.ensureReceiverChain C msg.senderRatchetKey rc).exec r0 with
          ⟨_ | ck, r1⟩
        · rw [hth2, hrc2, hens] at hsetup
          rw [hsetup]
        · rw [hth2, hrc2, hens] at hsetup
          obtain ⟨chainIdx, rcAct, cur', tOut, cEps', hset_eq, hfind1, hget1, hsrk1, hck1,
            hmk1_le, hr1_le, hr1_seed, hmfj1, hepochs⟩ := hsetup
          rw [hset_eq]
          dsimp only
          let setVal : tSetVal.denote :=
            ((r1.rootKey,
              (r1.previousCounter,
               (r1.senderChain.map (encodeSenderChain (ℓ := ℓ)),
                (r1.receiverChains.map (encodeRecvChain (ℓ := ℓ)),
                 (cur', (tOut, cEps')))))),
             ((ck.key, ck.index), rcAct.messageKeys.map encodeMsgKey))
          let ρ3 := envCons tSetVal setVal ρ2
          have hcons := drRecvConsumeC_eval
            (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I
            (.fst (.snd (.snd .v1)))
            (.fst (.snd (.snd (.snd .v1))))
            (.fst (.snd (.snd (.snd (.fst .v0)))))
            (.snd .v0)
            ρ3 rfl rfl hfind1 hget1 hsrk1 hck1 hmk1_le hr1_le hr1_seed hmfj1
          have hth3 : (Expr.fst (Expr.snd (Expr.snd (.v1 : Expr OO _ _)))).eval ρ3 =
              msg.senderRatchetKey := rfl
          have hctr3 : (Expr.fst (Expr.snd (Expr.snd (Expr.snd (.v1 : Expr OO _ _))))).eval ρ3 =
              msg.counter := rfl
          rcases hcmk :
              (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter .whisper).exec
                r1 with ⟨_ | mkg, r2⟩
          · rw [hth3, hctr3, hcmk] at hcons
            dsimp only at hcons ⊢
            rw [hcons, pure_bind]
            rfl
          · rw [hth3, hctr3, hcmk] at hcons
            obtain ⟨hcons_eq, hmkg_seed, hr2_len, hr2_seed, hr2_rk, hr2_pc, hr2_sc⟩ := hcons
            rw [hcons_eq]
            simp only [pure_bind, Expr.eval, Expr.v0, Env.get]
            have hsplit := ghostSplitEval_eq_of_le (ℓ := ℓ) hg.receiverChains_le_five
            let consVal : tConsVal.denote :=
              (encodeMsgKey mkg, r2.receiverChains.map (encodeRecvChain (ℓ := ℓ)))
            let ρ4 := envCons tConsVal consVal (envCons (drRecvConsumeOutT ℓ) (some consVal) ρ3)
            let pqArgE :
              Expr OO (tConsVal :: drRecvConsumeOutT ℓ :: tSetVal :: tPreVal :: tIn :: Γ)
                (.prod (B 32) (B 32)) :=
              .pair (gpPqSt (.fst .v3)) (.snd (.snd (.snd (.snd (.snd .v3)))))
            have hpqArg : pqArgE.eval ρ4 = (g.session.pqRatchetState, msg.pqRatchet) := by
              simp [pqArgE, ρ4, ρ3, ρ2, envCons, preVal, gpPqSt, Expr.eval, Expr.v3, Env.get,
                hsplit]
            have hpq_eval := hooks.recvC_eval I pqArgE ρ4 (by rw [hpqArg]; exact hg.topTight)
            rw [hpqArg] at hpq_eval
            change ((hooks.recvC I pqArgE).eval ρ4 >>= _) = _
            rw [hpq_eval]
            dsimp only [spqr] at *
            by_cases hpan :
                (spqrV1SessionUniformCoins C.F K).recvPanics g.session.pqRatchetState msg.pqRatchet
            · simp [hpan, pure_bind]
            · have hpan_f :
                  (spqrV1SessionUniformCoins C.F K).recvPanics g.session.pqRatchetState
                    msg.pqRatchet = false :=
                Bool.eq_false_iff.mpr hpan
              simp only [hpan_f, Bool.false_eq_true, ↓reduceIte]
              rcases hspqr_r :
                  (spqrV1SessionUniformCoins C.F K).recv g.session.pqRatchetState msg.pqRatchet with
                _ | ⟨newPq, pqKey⟩
              · simp [pure_bind]
              · simp only [pure_bind, drRecvFinishE, gpIsB, gpVer, gpLocId, gpRemId, gpMk,
                  Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, eval_e2ePureOp, eval_e2eCryptoOp,
                  eval_deriveMsgKeys_op, eval_signalMsgVerifyMac_op,
                  eval_expectedAddrsE_eq_prm (idA := idA) (idB := idB),
                  E2EPureOp.eval, hsplit, htry, boolToParty_partyToBool_eq]
                have hgen_eq :
                    ({ seed := keyToBytes32 (encodeMsgKey mkg).1
                       counter := (encodeMsgKey mkg).2 } : MessageKeyGenerator) = mkg :=
                  decodeMsgKey_encodeMsgKey hmkg_seed
                rw [salt_roundtrip pqKey, hgen_eq]
                have hr2_le5 : r2.receiverChains.length ≤ 5 := by
                  rw [hr2_len]; exact hr1_le
                have hrcs2_len :
                    (r2.receiverChains.map (encodeRecvChain (ℓ := ℓ))).length ≤ 5 := by
                  simpa using hr2_le5
                have hsc_dec :
                    (r1.senderChain.map (encodeSenderChain (ℓ := ℓ))).map decodeSenderChain =
                      r2.senderChain := by
                  rw [hr2_sc]
                  cases r1.senderChain <;> simp [decodeSenderChain_encodeSenderChain]
                obtain ⟨hcur, htOut, hcEps⟩ := hepochs r2.receiverChains.length hr2_len
                cases hmac :
                  msg.verifyMacWithAddresses C.F
                    ((paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).expectedAddrs
                      g.party)
                    remId g.session.localIdentity (mkg.generateKeys C.F pqKey).macKey
                · simp
                · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  rcases haes :
                      E2ECryptoOp.eval ℓ P C K .aes256CbcDec
                        ((mkg.generateKeys C.F pqKey).cipherKey,
                         ((mkg.generateKeys C.F pqKey).iv, msg.ciphertext)) with _ | pt
                  · rfl
                  · dsimp only
                    refine congrArg pure (congrArg some ?_)
                    rw [ghostJoinEval_eq_of_le _ _ _ _ _ _ _ _ _ _ _ _ hrcs2_len,
                      boolToParty_partyToBool_eq,
                      decodeRecvChains_encodeRecvChains r2.receiverChains hr2_seed,
                      hsc_dec, ← hr2_rk, ← hr2_pc, hrem, hcur, htOut, hcEps]
                    rfl
    · simp only [hver, ne_eq, not_false_eq_true, ↓reduceIte]

theorem drReceiveC_eval_params (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod (B 32) BV256))) (ρ : Env Γ)
    (idA idB : IdentityKey)
    (hg : PartyReachInv C K (e.eval ρ).1) :
    (drReceiveC hooks I e).eval ρ =
      pure (
        ((paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB).receive
            (e.eval ρ).1 (e.eval ρ).2.1 (e.eval ρ).2.2).map
          fun (g', t, idx, ptBytes) => (g', (t, (idx, padOrTruncatePlain ℓ ptBytes)))) := by
  rw [drReceiveC_eval_core hooks I e ρ idA idB hg]
  congr 1
  rcases he : e.eval ρ with ⟨g, ⟨c, rc⟩⟩
  dsimp only
  set prm := paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB
  have hprmD : prm.C.D = C.D := rfl
  dsimp only [CryptoGames.LibsignalSession.Params.receive, SessionState.tryDecryptFromRecord]
  rcases SignalMessage.tryFrom prm.codec c with _ | msg
  · rfl
  · dsimp only [Option.map]
    by_cases hver : g.session.version.toNat = msg.messageVersion.toNat
    · simp only [hver, ne_eq, not_true_eq_false, ↓reduceIte]
      rw [tryDecryptWithState_exec]
      rcases TripleRatchet.fromSessionState.exec g.session with ⟨_ | tr0, s1⟩
      · rfl
      · dsimp only
        rw [tripleDecrypt_exec]
        rcases (RatchetState.ensureReceiverChain prm.C msg.senderRatchetKey rc).exec tr0.ratchet with
          ⟨_ | ck, r1⟩
        · rfl
        · dsimp only
          rcases (RatchetState.consumeMessageKey prm.C.F msg.senderRatchetKey ck msg.counter
              .whisper).exec r1 with ⟨_ | mkg, r2⟩
          · rfl
          · dsimp only
            by_cases hpan : prm.spqr.recvPanics tr0.pqrState msg.pqRatchet
            · simp only [hpan, ↓reduceIte]
            · simp only [hpan, Bool.false_eq_true, ↓reduceIte]
              rcases prm.spqr.recv tr0.pqrState msg.pqRatchet with (_ | _) | ⟨newPq, pqKey⟩
              · rfl
              · rfl
              · dsimp only
                by_cases hmac :
                    !(msg.verifyMacWithAddresses prm.C.F (prm.expectedAddrs g.party)
                        tr0.remoteIdentityKey tr0.localIdentityKey
                        (mkg.generateKeys prm.C.F pqKey).macKey)
                · simp only [hmac, ↓reduceIte]
                · simp only [hmac, Bool.false_eq_true, ↓reduceIte, E2ECryptoOp.eval]
                  rw [← hprmD]
                  rcases aesCbcDecrypt prm.C.D (mkg.generateKeys prm.C.F pqKey).cipherKey
                      (mkg.generateKeys prm.C.F pqKey).iv msg.ciphertext with _ | ptBytes <;> rfl
    · simp only [hver, ne_eq, not_false_eq_true, ↓reduceIte]

/-- `Comp.eval` agreement of `drReceiveC` with `sessionSchemeFixedSpk.receive` under `PartyReachInv`. -/
theorem drReceiveC_eval (hooks : SpqrDslHooks ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ : List (Ty S)}
    (e : Expr OO Γ (.prod GhostStT (.prod (B 32) BV256))) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (hg : PartyReachInv C K (e.eval ρ).1) :
    (drReceiveC hooks I e).eval ρ =
      pure ((sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).receive
        (e.eval ρ).1 (e.eval ρ).2.1 (e.eval ρ).2.2) := by
  rw [drReceiveC_eval_params hooks I e ρ idA idB hg]
  rfl

end RecvProgram

end Computational.Proofs.E2E.Dsl.DrSessionSimRecv
