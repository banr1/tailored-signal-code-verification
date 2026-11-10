/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
import Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase
import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping

/-!
# Tier-2 Tracker-Halted Hop-2 Step Handler and Reductions

Constructs the table-backed tracker-halted Hop-2 state `hop2HaltedTier2StTy`, initializers,
5-arm step handler `hop2StepTier2TrackC`, and `CostedReduction`s `spkHop2PrgProgHaltedTier2` and
`spkHop2PrfProgHaltedTier2` bounded by `spkTier2Budget`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Step

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp CostedReduction
  bits bits_mono reductionSizeBudget atomicSig atomicSessionOps atomicSamplers
  coinOnlyIface extractPtPrfIface e2eSessionCodec
  BV256 BV512 PK PtT GhostStT PlainT B smQT smRT)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (posTy posSender posEpoch posIdx orE maxN isSomeE pGet sendsInE)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState maxForwardJumps)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalSession (GRedBounded)
open CryptoVerification.E2E (Bytes spkTier2Budget SpkSwapPrgHybridProg SpkSwapPrfHybridProg)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (
  atomicSessionOps_sizeHonest atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (
  wk1Expr wk1Comp wk1Expr_cost wk1Comp_cost wk1Comp_queries
  liftExpr liftExpr_cost drSendAtomicC atomicDraw512_cost)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (
  bits_succ_le liftExpr_size_le wk1Expr_size wk1Comp_size dummyBoolSessionRed
  dummyBoolSessionRed_totalQueries dummyBoolSessionRed_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Lift (
  tier2PureOp tier2PtEncOp tier2CurveOp)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys (
  chunk64NatE packChunksVar0E ptKeyE)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2BookkeepingBase (
  tier2SmRWireE tier2SmRRecvE tier2SmRCorrE tier2RecvRejE tier2RecvAccE
  posTblGetE tier2RecTy tier2RecPos tier2RecMk tier2GsTy
  gsStTier2E gsBTier2E gsWinTier2E gsEpochTier2E gsIdxTier2E gsTLTier2E gsMaxAccTier2E
  gsPosNodeTier2E gsChallTblTier2E gsChallCountTier2E gsCompTblTier2E gsUncompCountTier2E
  initGsTier2E setWinTier2E safeChTier2E safeInjTier2E leakTier2E epMgmtTier2E
  gsChallTier2E gsCompTier2E trivialTier2E corrAllowedTier2E afterCorrAllowedTier2E
  inWindowTier2E sendOKTier2E corrOKTier2E
  cost_tier2SmRWireE cost_tier2RecMk cost_initGsTier2E cost_safeChTier2E
  cost_epMgmtTier2E cost_sendOKTier2E)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Bookkeeping (
  acceptCiphertextTier2E inTransitTier2E recordCiphertextTier2E
  hop2TblTy hop2TblInitE hop2TblSetE
  cost_recordCiphertextTier2E cost_hop2TblInitE cost_hop2TblSetE
  spk_totalCost_le_spkTier2Budget)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2RInProg (
  compCoinToPrf cost_compCoinToPrf size_compCoinToPrf compCoinToPrf_wk1Comp redCoinToPrf
  Hop2Mode prgCoinMode prgLiftedMode prfOracleMode
  queries_compCoinToPrf_zero queries_coinOnly_zero
  drawBoolCoin drawBoolCoin_cost drawBoolCoin_size
  draw256Coin draw256Coin_cost draw256Coin_size
  sPureOp sGroupOp cost_sPureOp cost_sGroupOp size_sPureOp size_sGroupOp
  hop2ChallTy hop2UpdTy
  hop2InitGsE2EE cost_hop2InitGsE2EE size_hop2InitGsE2EE noKemKeyGenExpr_hop2InitGsE2EE
  hop2BadAtE2EE size_hop2BadAtE2EE
  liftExpr_cost_exact drSendAtomicC_cost_exact)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2 (
  kemTrackTier2T honestWiresTier2T kemSessionTrackTier2T
  initKemFailSessionTrackTier2E initKemFailSessionTrackTier2E_cost_le
  initKemFailSessionTrackTier2E_size_le
  stepKemFailSendTier2C stepKemFailSendTier2C_queries_zero
  stepKemFailSendTier2C_cost_le stepKemFailSendTier2C_size_le
  recordHonestWireTier2E recordHonestWireTier2E_cost_le recordHonestWireTier2E_size_le
  findRevHonestWireIdxTier2E findRevHonestWireIdxTier2E_cost_le findRevHonestWireIdxTier2E_size_le
  kemOnDeliverPostTier2E kemOnDeliverPostTier2E_cost_le kemOnDeliverPostTier2E_size_le)
open Computational.Proofs.Game.PromotedCostedReds.SpkHop2Tier2Prog (
  draw512Coin tier2SamIfNec512C
  hop2Tier2AuxTy hop2RecvResTier2Ty hop2Tier2FullStTy
  auxLazyTier2 auxMadeTier2 auxIdxTier2 auxCoinsTier2 auxBadTier2 auxMkTier2 auxSetBadTier2
  stSTier2 stGsTier2 stAuxTier2 stChallTier2 stMkTier2
  hop2CommitTier2E hop2RecvTier2C
  hop2CrArmTier2E hop2DlArmTier2C hop2IjArmTier2C hop2StepTier2C
  cost_hop2CrArmTier2E cost_hop2DlArmTier2C cost_hop2IjArmTier2C
  queries_hop2RecvTier2C
  compCoinToPrf_hop2DlArmTier2C compCoinToPrf_hop2IjArmTier2C
  drSendAtomicC_size_le size_hop2CommitTier2E
  size_acceptCiphertextTier2E size_inTransitTier2E
  size_recordCiphertextTier2E_three size_epMgmtTier2E_three
  size_hop2RecvTier2C size_hop2StepTier2C)

section Tier2HaltedStep

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (K : MlKem)
  (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt)

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

/-- Combined `Ty.tbl`-backed tracker-halted Hop-2 state type `(hop2Tier2FullStTy, kemSessionTrackTier2T)`. -/
@[expose] def hop2HaltedTier2StTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (hop2Tier2FullStTy ℓ Pt) (kemSessionTrackTier2T ℓ Pt)

@[expose] def hst2Base {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedTier2StTy ℓ Pt)) :
    Expr AOps Γ (hop2Tier2FullStTy ℓ Pt) := .fst e
@[expose] def hst2SessionTr {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedTier2StTy ℓ Pt)) :
    Expr AOps Γ (kemSessionTrackTier2T ℓ Pt) := .snd e
@[expose] def hst2Tr {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedTier2StTy ℓ Pt)) :
    Expr AOps Γ (kemTrackTier2T ℓ Pt) := .fst (.snd e)
@[expose] def hst2Wires {Γ : List (Ty ASig)} (e : Expr AOps Γ (hop2HaltedTier2StTy ℓ Pt)) :
    Expr AOps Γ (honestWiresTier2T ℓ Pt) := .snd (.snd e)
@[expose] def hst2Mk {Γ : List (Ty ASig)}
    (baseE : Expr AOps Γ (hop2Tier2FullStTy ℓ Pt))
    (trE : Expr AOps Γ (kemTrackTier2T ℓ Pt))
    (wiresE : Expr AOps Γ (honestWiresTier2T ℓ Pt)) :
    Expr AOps Γ (hop2HaltedTier2StTy ℓ Pt) :=
  .pair baseE (.pair trE wiresE)

@[expose] def hop2InitBodyTier2TrackC (k : ℕ) :
    Comp AOps (coinOnlyIface ℓ Pt)
      [.prod BV256 (hop2ChallTy ℓ Pt)]
      (.prod .unit (hop2HaltedTier2StTy ℓ Pt)) :=
  let dB {Γ} := drawBoolCoin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  let d256 {Γ} := draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  .bind dB (.bind d256 (.bind d256 (.bind d256 (.bind d256 (.bind d256
    (let ck1E : Expr AOps _ BV256 := if k = 0 then (.snd (.snd .v6)) else .v0
     let i0E : Expr AOps _ PtT := sGroupOp (C := C) (K := K) (Dh := Dh) (encPt := encPt)
       (encT := encT) (decT := decT) (lam := lam)
       .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))
     let initArgE : Expr AOps _ _ :=
       .pair .v5 (.pair .v3 (.pair (.pair (sPureOp (.bv256Lit 0) .unit) ck1E)
         (.pair .v4 (.pair .v2 .v1))))
     let abPairE : Expr AOps _ (.prod GhostStT GhostStT) :=
       .fst (.letE initArgE
         (wk1Expr (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
           (encT := encT) (decT := decT) (lam := lam)
           (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB))))
     let gs0E : Expr AOps _ (tier2GsTy ℓ Pt) := .letE abPairE (initGsTier2E (.fst .v0) (.snd .v0) .v6)
     let emptyTbl : Expr AOps _ (hop2TblTy ℓ Pt) := hop2TblInitE (ℓ := ℓ) (Pt := Pt)
       (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
     let aux0E : Expr AOps _ (hop2Tier2AuxTy ℓ Pt) :=
       auxMkTier2 emptyTbl (hop2TblSetE emptyTbl (.nat 0) i0E ck1E)
         (.pair (.some (.nat 1)) (.some (.nat 0))) (.pair .v2 .v3) (.bool false)
     let base0E := stMkTier2 C K Dh encPt encT decT lam (.fst .v6) gs0E aux0E (.snd .v6)
     let sessTr0E := initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh)
       (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) .v1
     .ret (.pair .unit (.pair base0E sessTr0E))))))))

@[expose] def hop2InitPrfTier2TrackC (k : ℕ) :
    Comp AOps (extractPtPrfIface ℓ Pt) [BV256] (.prod .unit (hop2HaltedTier2StTy ℓ Pt)) :=
  let d256 {Γ} := draw256Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  compCoinToPrf (.bind d256 (.bind d256 (.bind (.ret (.pair .v2 (.pair .v1 .v0)))
    (wk1Comp (hop2InitBodyTier2TrackC C K Dh encPt encT decT idA idB lam k)))))

@[expose] def hop2TrArmTier2TrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (sessTrE : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt))
    (trArg : Expr AOps Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    Comp AOps I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT)
        (.prod (tier2GsTy ℓ Pt) (kemSessionTrackTier2T ℓ Pt))) :=
  .bind (.ret (.pair gsE (.pair sessTrE trArg)))
    (.ite (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0))))) (gsWinTier2E (.fst .v0)))
      (.ret (.pair (tier2SmRWireE .none) (.pair (.fst .v0) (.fst (.snd .v0)))))
      (.bind (tier2SamIfNec512C M (.snd (.snd (.snd (.snd .v0)))))
        (.caseOpt (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd (.snd .v1))) (.snd .v0))
          (.ret (.pair (tier2SmRWireE .none) (.pair (.fst .v1) (.fst (.snd .v1)))))
          (.bind (M.embedCoin
              (stepKemFailSendTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                (encT := encT) (decT := decT) (lam := lam) (I := coinOnlyIface ℓ Pt)
                (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2))) (.fst .v1)))
            (.ite (.fst .v0)
              (.ret (.pair (tier2SmRWireE .none)
                (.pair (.fst .v3) (.pair (.snd .v0) (.snd (.fst (.snd .v3)))))))
              (.bind (M.embedCoin
                  (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                    (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
                    (.pair (pGet (gsStTier2E .v1) (.fst (.snd (.snd .v3))))
                      (.pair (.fst (.snd (.snd (.snd .v3)))) (.fst .v2)))))
                (let st' : Expr AOps _ GhostStT := .fst .v0
                 let ct' : Expr AOps _ (B 32) := .snd .v0
                 let trOut2 : Expr AOps _ (kemTrackTier2T ℓ Pt) := .snd .v1
                 let s1 : Expr AOps _ (tier2GsTy ℓ Pt) := .v2
                 let hw4 : Expr AOps _ (honestWiresTier2T ℓ Pt) := .snd (.fst (.snd .v4))
                 let p4 : Expr AOps _ .bool := .fst (.snd (.snd .v4))
                 let m4 : Expr AOps _ PlainT := .fst (.snd (.snd (.snd .v4)))
                 let posE : Expr AOps _ posTy :=
                   .pair p4 (.pair (pGet (gsEpochTier2E s1) p4)
                     (.add (pGet (gsIdxTier2E s1) p4) (.nat 1)))
                 let recE : Expr AOps _ (tier2RecTy ℓ Pt) := tier2RecMk posE m4 ct'
                 let gs' := recordCiphertextTier2E 3 s1 p4 st' recE (.bool false)
                 let hw' := recordHonestWireTier2E (C := C) (K := K) (Dh := Dh)
                   (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) hw4 ct' p4
                 .ret (.pair (tier2SmRWireE (.some ct')) (.pair gs' (.pair trOut2 hw'))))))))))

@[expose] def hop2ChArmTier2TrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (sessTrE : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt))
    (chArg : Expr AOps Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    Comp AOps I Γ
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT)
        (.prod (tier2GsTy ℓ Pt) (kemSessionTrackTier2T ℓ Pt))) :=
  .bind (.ret (.pair gsE (.pair sessTrE chArg)))
    (.ite (orE (.not (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0))))) (gsWinTier2E (.fst .v0)))
      (.ret (.pair (tier2SmRWireE .none) (.pair (.fst .v0) (.fst (.snd .v0)))))
      (.bind (tier2SamIfNec512C M (.snd (.snd (.snd (.snd (.snd .v0))))))
        (.caseOpt (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd (.snd .v1))) (.snd .v0))
          (.ret (.pair (tier2SmRWireE .none) (.pair (.fst .v1) (.fst (.snd .v1)))))
          (.ite (.not (safeChTier2E 3 .v0 (.fst (.snd (.snd .v2)))))
            (.ret (.pair (tier2SmRWireE .none) (.pair (.fst .v2) (.fst (.snd .v2)))))
            (.bind (M.embedCoin
                (stepKemFailSendTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                  (encT := encT) (decT := decT) (lam := lam) (I := coinOnlyIface ℓ Pt)
                  (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2))) (.fst .v1)))
              (.ite (.fst .v0)
                (.ret (.pair (tier2SmRWireE .none)
                  (.pair (.fst .v3) (.pair (.snd .v0) (.snd (.fst (.snd .v3)))))))
                (let mCh3 : Expr AOps _ PlainT :=
                   .ite (gsBTier2E (.fst .v3))
                     (.fst (.snd (.snd (.snd (.snd .v3)))))
                     (.fst (.snd (.snd (.snd .v3))))
                 .bind (M.embedCoin
                     (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                       (encT := encT) (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt)
                       (.pair (pGet (gsStTier2E .v1) (.fst (.snd (.snd .v3))))
                         (.pair mCh3 (.fst .v2)))))
                   (let st' : Expr AOps _ GhostStT := .fst .v0
                    let ct' : Expr AOps _ (B 32) := .snd .v0
                    let trOut2 : Expr AOps _ (kemTrackTier2T ℓ Pt) := .snd .v1
                    let s1 : Expr AOps _ (tier2GsTy ℓ Pt) := .v2
                    let gs4 : Expr AOps _ (tier2GsTy ℓ Pt) := .fst .v4
                    let hw4 : Expr AOps _ (honestWiresTier2T ℓ Pt) := .snd (.fst (.snd .v4))
                    let p4 : Expr AOps _ .bool := .fst (.snd (.snd .v4))
                    let mCh4 : Expr AOps _ PlainT :=
                      .ite (gsBTier2E gs4)
                        (.fst (.snd (.snd (.snd (.snd .v4)))))
                        (.fst (.snd (.snd (.snd .v4))))
                    let posE : Expr AOps _ posTy :=
                      .pair p4 (.pair (pGet (gsEpochTier2E s1) p4)
                        (.add (pGet (gsIdxTier2E s1) p4) (.nat 1)))
                    let recE : Expr AOps _ (tier2RecTy ℓ Pt) := tier2RecMk posE mCh4 ct'
                    let gs' := recordCiphertextTier2E 3 s1 p4 st' recE (.bool true)
                    let hw' := recordHonestWireTier2E (C := C) (K := K) (Dh := Dh)
                      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) hw4 ct' p4
                    .ret (.pair (tier2SmRWireE (.some ct')) (.pair gs' (.pair trOut2 hw')))))))))))

/-- Combined 5-arm Tier-2 tracker-halted `hop2ImplTrackHalted` handler. -/
@[expose] def hop2StepTier2TrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep k : ℕ) :
    Comp AOps I [hop2HaltedTier2StTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
      (.prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (hop2HaltedTier2StTy ℓ Pt)) :=
  .caseSum .v1
    (.bind (hop2TrArmTier2TrackC C K Dh encPt encT decT lam M qep
        (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v1)))
        (hst2SessionTr C K Dh encPt encT decT lam .v1) .v0)
      (let base2 := hst2Base C K Dh encPt encT decT lam .v2
       .ret (.pair (.fst .v0)
         (.pair (stMkTier2 C K Dh encPt encT decT lam
             (stSTier2 C K Dh encPt encT decT lam base2)
             (.fst (.snd .v0))
             (stAuxTier2 C K Dh encPt encT decT lam base2)
             (.snd (.snd (.snd base2))))
           (.snd (.snd .v0))))))
    (.caseSum .v0
      (.bind (hop2ChArmTier2TrackC C K Dh encPt encT decT lam M qep
          (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v2)))
          (hst2SessionTr C K Dh encPt encT decT lam .v2) .v0)
        (let base3 := hst2Base C K Dh encPt encT decT lam .v3
         .ret (.pair (.fst .v0)
           (.pair (stMkTier2 C K Dh encPt encT decT lam
               (stSTier2 C K Dh encPt encT decT lam base3)
               (.fst (.snd .v0))
               (stAuxTier2 C K Dh encPt encT decT lam base3)
               (.snd (.snd (.snd base3))))
             (.snd (.snd .v0))))))
      (.caseSum .v0
        (.bind (.ret (findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)
            (hst2Wires C K Dh encPt encT decT lam .v3) (.fst .v0) (.snd .v0)))
          (.bind (.ret (.pair (hst2Base C K Dh encPt encT decT lam .v4) .v1))
            (.bind (wk1Comp (hop2DlArmTier2C C K Dh encPt encT decT lam M k))
              (let smOut := Expr.fst .v0
               let base' := Expr.snd .v0
               let jOpt := Expr.v2
               let dlArg := Expr.v3
               let hst6 := Expr.v6
               let tr' := kemOnDeliverPostTier2E (C := C) (K := K) (Dh := Dh)
                 (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
                 (.fst dlArg) jOpt (.fst (.snd smOut))
                 (hst2Tr C K Dh encPt encT decT lam hst6)
               .ret (.pair smOut
                 (hst2Mk C K Dh encPt encT decT lam base' tr'
                   (hst2Wires C K Dh encPt encT decT lam hst6)))))))
        (.caseSum .v0
          (.bind (.ret (.pair (hst2Base C K Dh encPt encT decT lam .v4) .v0))
            (.bind (wk1Comp (hop2IjArmTier2C C K Dh encPt encT decT lam M qep k))
              (.ret (.pair (.fst .v0)
                (.pair (.snd .v0) (hst2SessionTr C K Dh encPt encT decT lam .v6))))))
          (.ret (.letE (hop2CrArmTier2E C K Dh encPt encT decT lam
              (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v4))) .v0)
            (let base5 := hst2Base C K Dh encPt encT decT lam .v5
             .pair (.fst .v0)
               (.pair (stMkTier2 C K Dh encPt encT decT lam
                   (stSTier2 C K Dh encPt encT decT lam base5)
                   (.snd .v0)
                   (stAuxTier2 C K Dh encPt encT decT lam base5)
                   (.snd (.snd (.snd base5))))
                 (hst2SessionTr C K Dh encPt encT decT lam .v5))))))))

@[expose] def hop2GameTier2TrackRed {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep k : ℕ) :
    CostedReduction AOps I
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt)
      (.prod BV256 (hop2ChallTy ℓ Pt)) .unit .bool .bool where
  σ := hop2HaltedTier2StTy ℓ Pt
  init := M.embedCoin
    (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k)
  handle := hop2StepTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M qep k
  finish := .ret (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam
    (hst2Base C K Dh encPt encT decT lam .v0)))

@[expose] def spkHop2PrgProgHaltedTier2Real (ℓ _q qep k : ℕ) :
    SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
    (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k

/-- Sub-quadratic Tier-2 `CostedReduction` for `hop2PrgRedKTrackHalted`. -/
@[expose] def spkHop2PrgProgHaltedTier2 (ℓ q qep k : ℕ) :
    SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 ∧ k < 16 then
    spkHop2PrgProgHaltedTier2Real (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else
    dummyBoolSessionRed (coinOnlyIface ℓ Pt) (.prod BV256 (hop2ChallTy ℓ Pt))

@[expose] def spkHop2PrfProgHaltedTier2Real (ℓ _q qep k : ℕ) :
    SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam where
  σ := hop2HaltedTier2StTy ℓ Pt
  init := hop2InitPrfTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
  handle := hop2StepTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
    (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k
  finish := .ret (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam
    (hst2Base C K Dh encPt encT decT lam .v0)))

/-- Sub-quadratic Tier-2 `CostedReduction` for `hop2PrfRedKTrackHalted`. -/
@[expose] def spkHop2PrfProgHaltedTier2 (ℓ q qep k : ℕ) :
    SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam :=
  if ℓ < 10 ^ 6 ∧ k < 16 then
    spkHop2PrfProgHaltedTier2Real (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k
  else
    dummyBoolSessionRed (extractPtPrfIface ℓ Pt) BV256

theorem compCoinToPrf_hop2TrArmTier2TrackC (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (sessTrE : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt))
    (trArg : Expr AOps Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    compCoinToPrf
      (hop2TrArmTier2TrackC C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep gsE sessTrE trArg) =
      hop2TrArmTier2TrackC C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep gsE sessTrE trArg := rfl

theorem compCoinToPrf_hop2ChArmTier2TrackC (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (sessTrE : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt))
    (chArg : Expr AOps Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    compCoinToPrf
      (hop2ChArmTier2TrackC C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep gsE sessTrE chArg) =
      hop2ChArmTier2TrackC C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep gsE sessTrE chArg := rfl

theorem compCoinToPrf_hop2StepTier2TrackC (qep k : ℕ) :
    compCoinToPrf
      (hop2StepTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k) =
      hop2StepTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k := by
  simp only [hop2StepTier2TrackC, compCoinToPrf, compCoinToPrf_wk1Comp,
    compCoinToPrf_hop2TrArmTier2TrackC, compCoinToPrf_hop2ChArmTier2TrackC,
    compCoinToPrf_hop2DlArmTier2C, compCoinToPrf_hop2IjArmTier2C]

theorem redCoinToPrf_hop2GameTier2TrackRed_prgCoinMode (qep k : ℕ) :
    redCoinToPrf
      (hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k) =
      hop2GameTier2TrackRed (ℓ := ℓ) C K Dh encPt encT decT idA idB lam
        (prgLiftedMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k := by
  dsimp only [redCoinToPrf, hop2GameTier2TrackRed]
  rw [compCoinToPrf_hop2StepTier2TrackC]
  rfl

theorem queries_hop2StepTier2TrackC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (qep k : ℕ) :
    (hop2StepTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT lam M qep k).queries
      M.wq (fun _ => 0) ≤ M.qStep := by
  let t0 : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) (.prod .bool (B 32))
  have hdl := queries_hop2RecvTier2C M k (Γ := [BV256, tier2RecTy ℓ Pt, t0])
    (stChallTier2 C K Dh encPt encT decT lam (.fst .v2))
    (stAuxTier2 C K Dh encPt encT decT lam (.fst .v2))
    (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v2))) (.fst (.snd .v2)))
    (.snd (.snd .v2)) .v0
  have hij := queries_hop2RecvTier2C M k (Γ := [BV256, t0])
    (stChallTier2 C K Dh encPt encT decT lam (.fst .v1))
    (stAuxTier2 C K Dh encPt encT decT lam (.fst .v1))
    (pGet (gsStTier2E (stGsTier2 C K Dh encPt encT decT lam (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) .v0
  simp only [hop2StepTier2TrackC, hop2TrArmTier2TrackC, hop2ChArmTier2TrackC,
    hop2DlArmTier2C, hop2IjArmTier2C, tier2SamIfNec512C, Comp.queries,
    wk1Comp_queries, M.embedCoin_queries]
  omega

theorem cost_hop2InitBodyTier2TrackC (k : ℕ) :
    (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤
      75000 := by
  have hgs1 := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
    (noKemKeyGenExpr_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := cost_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  let Γ6 : List (Ty ASig) :=
    [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  let ck1E : Expr AOps Γ6 BV256 := if k = 0 then (.snd (.snd .v6)) else .v0
  have hck1 : ck1E.cost ≤ 3 := by dsimp only [ck1E]; split_ifs <;> simp [Expr.cost, Expr.v0, Expr.v6]
  have hig := cost_initGsTier2E (O := AOps) (Γ := [.prod GhostStT GhostStT] ++ Γ6)
    (.fst .v0) (.snd .v0) .v6
  have hts := cost_hop2TblSetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ6)
    (hop2TblInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    (.nat 0) (sGroupOp .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))) ck1E
  have hstr := initKemFailSessionTrackTier2E_cost_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
    (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ6) .v1
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2InitBodyTier2TrackC]
  dsimp only [ck1E] at hck1 hts
  generalize initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.v1 : Expr AOps Γ6 BV256) = sessTr0 at hstr ⊢
  simp only [stMkTier2, auxMkTier2, cost_hop2TblInitE, Comp.cost, drawBoolCoin_cost,
    draw256Coin_cost, wk1Expr_cost, cost_sGroupOp, _root_.ReductionDsl.AtomicGroupOp.cost,
    cost_sPureOp, _root_.ReductionDsl.AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    hb0, hb1] at hck1 hig hts hstr ⊢
  omega

theorem cost_hop2TrArmTier2TrackC (hℓ : ℓ < 10 ^ 6) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (sessTrE : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt))
    (trArg : Expr AOps Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    (hop2TrArmTier2TrackC C K Dh encPt encT decT lam M qep gsE sessTrE trArg).cost ≤
      gsE.cost + sessTrE.cost + trArg.cost + 61 * ℓ + 2 * bits qep + 1260000 := by
  let t0 : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt)
      (.prod .bool (.prod PlainT (.opt BV512))))
  have hsok := cost_sendOKTier2E (O := AOps) (Γ := [t0] ++ Γ) (.fst .v0) (.fst (.snd (.snd .v0)))
  have hep := cost_epMgmtTier2E (O := AOps) (Γ := [.prod BV512 .bool, t0] ++ Γ) 3 qep
    (.fst .v1) (.fst (.snd (.snd .v1))) (.snd .v0)
  let Γk : List (Ty ASig) := [tier2GsTy ℓ Pt, .prod BV512 .bool, t0] ++ Γ
  have hkf := stepKemFailSendTier2C_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := coinOnlyIface ℓ Pt) (Γ := Γk)
    (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2))) (.fst .v1)
  let Γd : List (Ty ASig) := [.prod .bool (kemTrackTier2T ℓ Pt)] ++ Γk
  have hdr := drSendAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) (Γ := Γd)
    (.pair (pGet (gsStTier2E .v1) (.fst (.snd (.snd .v3))))
      (.pair (.fst (.snd (.snd (.snd .v3)))) (.fst .v2)))
  let Γr : List (Ty ASig) := [.prod GhostStT (B 32)] ++ Γd
  let posE : Expr AOps Γr posTy :=
    .pair (.fst (.snd (.snd .v4)))
      (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd (.snd .v4))))
        (.add (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4)))) (.nat 1)))
  have hrc := cost_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γr) hℓ 3 .v2
    (.fst (.snd (.snd .v4))) (.fst .v0)
    (tier2RecMk posE (.fst (.snd (.snd (.snd .v4)))) (.snd .v0)) (.bool false)
  have hhw := recordHonestWireTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γr) hℓ
    (.snd (.fst (.snd .v4))) (.snd .v0) (.fst (.snd (.snd .v4)))
  have hb3 : bits 3 = 2 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2TrArmTier2TrackC, tier2SamIfNec512C]
  dsimp only [posE] at hrc
  simp only [orE, Comp.cost, M.embedCoin_cost, Expr.cost]
  generalize (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0)))).cost = csok at hsok ⊢
  generalize (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd (.snd .v1))) (.snd .v0)).cost = cep at hep ⊢
  generalize (stepKemFailSendTier2C (Pt := Pt) _ _ _).cost = ckf at hkf ⊢
  generalize (drSendAtomicC (coinOnlyIface ℓ Pt) _).cost = cdr at hdr ⊢
  generalize (recordCiphertextTier2E (Pt := Pt) 3 .v2 _ _ _ (.bool false)).cost = crc at hrc ⊢
  generalize (recordHonestWireTier2E (Pt := Pt) _ _ _).cost = chw at hhw ⊢
  simp only [draw512Coin, pGet, gsWinTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E,
    cost_tier2SmRWireE, cost_tier2RecMk, atomicDraw512_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb3, hb1]
    at hsok hep hkf hdr hrc hhw ⊢
  omega

theorem cost_hop2ChArmTier2TrackC (hℓ : ℓ < 10 ^ 6) {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) {Γ : List (Ty ASig)}
    (gsE : Expr AOps Γ (tier2GsTy ℓ Pt))
    (sessTrE : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt))
    (chArg : Expr AOps Γ (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (hop2ChArmTier2TrackC C K Dh encPt encT decT lam M qep gsE sessTrE chArg).cost ≤
      gsE.cost + sessTrE.cost + chArg.cost + 61 * ℓ + 2 * bits qep + 1261000 := by
  let t0 : Ty ASig :=
    .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt)
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))))
  have hsok := cost_sendOKTier2E (O := AOps) (Γ := [t0] ++ Γ) (.fst .v0) (.fst (.snd (.snd .v0)))
  have hep := cost_epMgmtTier2E (O := AOps) (Γ := [.prod BV512 .bool, t0] ++ Γ) 3 qep
    (.fst .v1) (.fst (.snd (.snd .v1))) (.snd .v0)
  let Γk : List (Ty ASig) := [tier2GsTy ℓ Pt, .prod BV512 .bool, t0] ++ Γ
  have hsch := cost_safeChTier2E (O := AOps) (Γ := Γk) 3 .v0 (.fst (.snd (.snd .v2)))
  have hkf := stepKemFailSendTier2C_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := coinOnlyIface ℓ Pt) (Γ := Γk)
    (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2))) (.fst .v1)
  let Γd : List (Ty ASig) := [.prod .bool (kemTrackTier2T ℓ Pt)] ++ Γk
  let mCh3 : Expr AOps Γd PlainT :=
    .ite (gsBTier2E (.fst .v3))
      (.fst (.snd (.snd (.snd (.snd .v3)))))
      (.fst (.snd (.snd (.snd .v3))))
  have hdr := drSendAtomicC_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (coinOnlyIface ℓ Pt) (Γ := Γd)
    (.pair (pGet (gsStTier2E .v1) (.fst (.snd (.snd .v3)))) (.pair mCh3 (.fst .v2)))
  let Γr : List (Ty ASig) := [.prod GhostStT (B 32)] ++ Γd
  let mCh4 : Expr AOps Γr PlainT :=
    .ite (gsBTier2E (.fst .v4))
      (.fst (.snd (.snd (.snd (.snd .v4)))))
      (.fst (.snd (.snd (.snd .v4))))
  let posE : Expr AOps Γr posTy :=
    .pair (.fst (.snd (.snd .v4)))
      (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd (.snd .v4))))
        (.add (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4)))) (.nat 1)))
  have hrc := cost_recordCiphertextTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γr) hℓ 3 .v2
    (.fst (.snd (.snd .v4))) (.fst .v0)
    (tier2RecMk posE mCh4 (.snd .v0)) (.bool true)
  have hhw := recordHonestWireTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γr) hℓ
    (.snd (.fst (.snd .v4))) (.snd .v0) (.fst (.snd (.snd .v4)))
  have hb3 : bits 3 = 2 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [hop2ChArmTier2TrackC, tier2SamIfNec512C]
  dsimp only [mCh3, mCh4, posE] at hdr hrc
  simp only [orE, Comp.cost, M.embedCoin_cost, Expr.cost]
  generalize (sendOKTier2E (.fst .v0) (.fst (.snd (.snd .v0)))).cost = csok at hsok ⊢
  generalize (epMgmtTier2E 3 qep (.fst .v1) (.fst (.snd (.snd .v1))) (.snd .v0)).cost = cep at hep ⊢
  generalize (safeChTier2E 3 .v0 (.fst (.snd (.snd .v2)))).cost = csch at hsch ⊢
  generalize (stepKemFailSendTier2C (Pt := Pt) _ _ _).cost = ckf at hkf ⊢
  generalize (drSendAtomicC (coinOnlyIface ℓ Pt) _).cost = cdr at hdr ⊢
  generalize (recordCiphertextTier2E (Pt := Pt) 3 .v2 _ _ _ (.bool true)).cost = crc at hrc ⊢
  generalize (recordHonestWireTier2E (Pt := Pt) _ _ _).cost = chw at hhw ⊢
  simp only [draw512Coin, pGet, gsWinTier2E, gsBTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E,
    cost_tier2SmRWireE, cost_tier2RecMk, atomicDraw512_cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb3, hb1]
    at hsok hep hsch hkf hdr hrc hhw ⊢
  omega

theorem cost_hop2StepTier2TrackC (hℓ : ℓ < 10 ^ 6) {k : ℕ} (hk : k < 16)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I)
    (qep : ℕ) :
    (hop2StepTier2TrackC C K Dh encPt encT decT lam M qep k).cost ≤
      5165000 + 61 * ℓ + 2 * bits qep := by
  let tTr : Ty ASig := .prod .bool (.prod PlainT (.opt BV512))
  let tCh : Ty ASig := .prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))
  let tDl : Ty ASig := .prod .bool (B 32)
  let tR3 : Ty ASig := .sum tDl .bool
  let tR2 : Ty ASig := .sum tDl tR3
  let tR1 : Ty ASig := .sum tCh tR2
  let Γ0 : List (Ty ASig) := [hop2HaltedTier2StTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  have htr := cost_hop2TrArmTier2TrackC C K Dh encPt encT decT lam hℓ M qep (Γ := [tTr] ++ Γ0)
    (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v1)))
    (hst2SessionTr C K Dh encPt encT decT lam .v1) .v0
  have hch := cost_hop2ChArmTier2TrackC C K Dh encPt encT decT lam hℓ M qep
    (Γ := [tCh, tR1] ++ Γ0)
    (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v2)))
    (hst2SessionTr C K Dh encPt encT decT lam .v2) .v0
  have hfind := findRevHonestWireIdxTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := [tDl, tR2, tR1] ++ Γ0) hℓ
    (hst2Wires C K Dh encPt encT decT lam .v3) (.fst .v0) (.snd .v0)
  have hdl := cost_hop2DlArmTier2C C K Dh encPt encT decT lam hℓ hk M
  let tDlIn : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) tDl
  let tDlOut : Ty ASig := .prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (hop2Tier2FullStTy ℓ Pt)
  have hkemDl := kemOnDeliverPostTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tDlOut, tDlIn, .opt .nat, tDl, tR2, tR1] ++ Γ0)
    (.fst .v3) .v2 (.fst (.snd (.fst .v0)))
    (hst2Tr C K Dh encPt encT decT lam .v6)
  have hij := cost_hop2IjArmTier2C C K Dh encPt encT decT lam hℓ hk M qep
  have hcr := cost_hop2CrArmTier2E C K Dh encPt encT decT lam
    (Γ := [.bool, tR3, tR2, tR1] ++ Γ0)
    (.fst (.snd (hst2Base C K Dh encPt encT decT lam .v4))) .v0
  dsimp only [hop2StepTier2TrackC]
  generalize hop2TrArmTier2TrackC C K Dh encPt encT decT lam M qep _ _ _ = trC at htr ⊢
  generalize hop2ChArmTier2TrackC C K Dh encPt encT decT lam M qep _ _ _ = chC at hch ⊢
  generalize findRevHonestWireIdxTier2E (Pt := Pt) _ _ _ = findE at hfind ⊢
  generalize hop2DlArmTier2C C K Dh encPt encT decT lam M k = dlC at hdl ⊢
  generalize kemOnDeliverPostTier2E (Pt := Pt) _ _ _ _ = kemDlE at hkemDl ⊢
  generalize hop2IjArmTier2C C K Dh encPt encT decT lam M qep k = ijC at hij ⊢
  generalize hop2CrArmTier2E C K Dh encPt encT decT lam _ _ = crE at hcr ⊢
  simp only [hst2Base, hst2SessionTr, hst2Tr, hst2Wires, hst2Mk,
    stSTier2, stAuxTier2, stMkTier2,
    wk1Comp_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
    at htr hch hfind hkemDl hcr ⊢
  omega

private theorem size_ptKeyE_local {Γ : List (Ty ASig)} (qE : Expr AOps Γ PtT) :
    (ptKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qE).size ≤ qE.size + 450 := by
  have hb : bits 0 = 1 ∧ bits 8 = 4 ∧ bits 16 = 5 ∧ bits 24 = 5 ∧ bits 32 = 6 ∧
      bits (2 ^ 64) = 65 := by decide
  dsimp only [ptKeyE, packChunksVar0E, chunk64NatE, tier2PureOp, tier2PtEncOp, Expr.size, Expr.v0,
    atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops, _root_.ReductionDsl.atomicFsOps,
    Ops.sum, Sum.elim, _root_.ReductionDsl.atomicPureOps, _root_.ReductionDsl.atomicPtEncOps,
    _root_.ReductionDsl.AtomicPureOp.opSize]
  simp only [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2]; omega

private theorem size_hop2TblSetE_local {Γ : List (Ty ASig)} (tblE : Expr AOps Γ (hop2TblTy ℓ Pt))
    (tE : Expr AOps Γ .nat) (qE : Expr AOps Γ PtT) (vE : Expr AOps Γ BV256) :
    (hop2TblSetE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) tblE tE qE vE).size ≤
      tblE.size + tE.size + qE.size + vE.size + 490 := by
  have hp := size_ptKeyE_local C K Dh encPt encT decT lam qE
  simp only [hop2TblSetE, Expr.size, Expr.v0] at hp ⊢; omega

theorem size_hop2InitBodyTier2TrackC (k : ℕ) :
    (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size ≤
      6300 := by
  have hgs1 := liftExpr_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB)
  have hgs2 := size_hop2InitGsE2EE (ℓ := ℓ) (C := C) (K := K) (decT := decT) (encT := encT) idA idB
  let Γ6 : List (Ty ASig) :=
    [BV256, BV256, BV256, BV256, BV256, .bool, .prod BV256 (hop2ChallTy ℓ Pt)]
  let ck1E : Expr AOps Γ6 BV256 := if k = 0 then (.snd (.snd .v6)) else .v0
  have hck1 : ck1E.size ≤ 3 := by dsimp only [ck1E]; split_ifs <;> simp [Expr.size, Expr.v0, Expr.v6]
  have hts := size_hop2TblSetE_local C K Dh encPt encT decT lam (Γ := Γ6)
    (hop2TblInitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    (.nat 0) (sGroupOp .ptDh (.pair .v3 (sGroupOp .ptDh (.pair .v2 (sGroupOp .ptBase .unit))))) ck1E
  have hstr := initKemFailSessionTrackTier2E_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
    (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ6) .v1
  have hb : bits 0 = 1 ∧ bits 1 = 1 := by decide
  dsimp only [hop2InitBodyTier2TrackC]
  dsimp only [ck1E] at hck1 hts
  generalize initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (.v1 : Expr AOps Γ6 BV256) = sessTr0 at hstr ⊢
  simp only [stMkTier2, auxMkTier2, hop2TblInitE, initGsTier2E, Comp.size, drawBoolCoin_size,
    draw256Coin_size, wk1Expr_size, size_sGroupOp, size_sPureOp,
    _root_.ReductionDsl.AtomicPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    hb.1, hb.2] at hck1 hts hstr ⊢
  omega

set_option linter.unusedSimpArgs false in
theorem size_hop2StepTier2TrackC (hℓ : ℓ < 10 ^ 6) {k : ℕ} (hk : k < 16)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (M : Hop2Mode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I) (qep : ℕ) :
    (hop2StepTier2TrackC C K Dh encPt encT decT lam M qep k).size ≤
      7850000 + 9 * bits qep := by
  have hb : bits 0 = 1 ∧ bits 1 = 1 ∧ bits 2 = 2 ∧ bits 3 = 2 ∧ bits 10 = 4 := by decide
  have hd512 : ∀ {Δ : List (Ty ASig)},
      (draw512Coin (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (Γ := Δ)).size = 2 := rfl
  have hdij :
      (hop2DlArmTier2C C K Dh encPt encT decT lam M k).size +
        (hop2IjArmTier2C C K Dh encPt encT decT lam M qep k).size ≤
        7460000 + 5 * bits qep := by
    have hst := size_hop2StepTier2C C K Dh encPt encT decT lam hℓ hk M qep
    dsimp only [hop2StepTier2C] at hst
    simp only [Comp.size, wk1Comp_size] at hst
    generalize (hop2DlArmTier2C C K Dh encPt encT decT lam M k).size = sdl at hst ⊢
    generalize (hop2IjArmTier2C C K Dh encPt encT decT lam M qep k).size = sij at hst ⊢
    omega
  let tTr : Ty ASig := .prod .bool (.prod PlainT (.opt BV512))
  let tCh : Ty ASig := .prod .bool (.prod PlainT (.prod PlainT (.opt BV512)))
  let tDl : Ty ASig := .prod .bool (B 32)
  let tR3 : Ty ASig := .sum tDl .bool
  let tR2 : Ty ASig := .sum tDl tR3
  let tR1 : Ty ASig := .sum tCh tR2
  let Γ0 : List (Ty ASig) := [hop2HaltedTier2StTy ℓ Pt, smQT (ℓ := ℓ) (Pt := Pt)]
  let tTr0 : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt) tTr)
  have hep1 := size_epMgmtTier2E_three C K Dh encPt encT decT lam qep
    (Γ := [.prod BV512 .bool, tTr0, tTr] ++ Γ0)
    (.fst .v1) (.fst (.snd (.snd .v1))) (.snd .v0)
  let Γk1 : List (Ty ASig) := [tier2GsTy ℓ Pt, .prod BV512 .bool, tTr0, tTr] ++ Γ0
  have hkf1 := stepKemFailSendTier2C_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := coinOnlyIface ℓ Pt) (Γ := Γk1)
    (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2))) (.fst .v1)
  let Γd1 : List (Ty ASig) := [.prod .bool (kemTrackTier2T ℓ Pt)] ++ Γk1
  have hdrS1 := drSendAtomicC_size_le C K Dh encPt encT decT lam (coinOnlyIface ℓ Pt) (Γ := Γd1)
    (.pair (pGet (gsStTier2E .v1) (.fst (.snd (.snd .v3))))
      (.pair (.fst (.snd (.snd (.snd .v3)))) (.fst .v2)))
  let Γr1 : List (Ty ASig) := [.prod GhostStT (B 32)] ++ Γd1
  have hrc1 := size_recordCiphertextTier2E_three C K Dh encPt encT decT lam hℓ (Γ := Γr1)
    .v2 (.fst (.snd (.snd .v4))) (.fst .v0)
    (tier2RecMk
      (.pair (.fst (.snd (.snd .v4)))
        (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd (.snd .v4))))
          (.add (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4)))) (.nat 1))))
      (.fst (.snd (.snd (.snd .v4)))) (.snd .v0)) (.bool false)
  have hhw1 := recordHonestWireTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γr1) hℓ
    (.snd (.fst (.snd .v4))) (.snd .v0) (.fst (.snd (.snd .v4)))
  let tCh0 : Ty ASig := .prod (tier2GsTy ℓ Pt) (.prod (kemSessionTrackTier2T ℓ Pt) tCh)
  have hep2 := size_epMgmtTier2E_three C K Dh encPt encT decT lam qep
    (Γ := [.prod BV512 .bool, tCh0, tCh, tR1] ++ Γ0)
    (.fst .v1) (.fst (.snd (.snd .v1))) (.snd .v0)
  let Γk2 : List (Ty ASig) := [tier2GsTy ℓ Pt, .prod BV512 .bool, tCh0, tCh, tR1] ++ Γ0
  have hkf2 := stepKemFailSendTier2C_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := coinOnlyIface ℓ Pt) (Γ := Γk2)
    (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2))) (.fst .v1)
  let Γd2 : List (Ty ASig) := [.prod .bool (kemTrackTier2T ℓ Pt)] ++ Γk2
  have hdrS2 := drSendAtomicC_size_le C K Dh encPt encT decT lam (coinOnlyIface ℓ Pt) (Γ := Γd2)
    (.pair (pGet (gsStTier2E .v1) (.fst (.snd (.snd .v3))))
      (.pair (.ite (gsBTier2E (.fst .v3))
        (.fst (.snd (.snd (.snd (.snd .v3)))))
        (.fst (.snd (.snd (.snd .v3))))) (.fst .v2)))
  let Γr2 : List (Ty ASig) := [.prod GhostStT (B 32)] ++ Γd2
  have hrc2 := size_recordCiphertextTier2E_three C K Dh encPt encT decT lam hℓ (Γ := Γr2)
    .v2 (.fst (.snd (.snd .v4))) (.fst .v0)
    (tier2RecMk
      (.pair (.fst (.snd (.snd .v4)))
        (.pair (pGet (gsEpochTier2E .v2) (.fst (.snd (.snd .v4))))
          (.add (pGet (gsIdxTier2E .v2) (.fst (.snd (.snd .v4)))) (.nat 1))))
      (.ite (gsBTier2E (.fst .v4))
        (.fst (.snd (.snd (.snd (.snd .v4)))))
        (.fst (.snd (.snd (.snd .v4))))) (.snd .v0)) (.bool true)
  have hhw2 := recordHonestWireTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γr2) hℓ
    (.snd (.fst (.snd .v4))) (.snd .v0) (.fst (.snd (.snd .v4)))
  have hfind := findRevHonestWireIdxTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := [tDl, tR2, tR1] ++ Γ0) hℓ
    (hst2Wires C K Dh encPt encT decT lam .v3) (.fst .v0) (.snd .v0)
  let tDlIn : Ty ASig := .prod (hop2Tier2FullStTy ℓ Pt) tDl
  let tDlOut : Ty ASig := .prod (smRT (ℓ := ℓ) (Pt := Pt) GhostStT) (hop2Tier2FullStTy ℓ Pt)
  have hkemDl := kemOnDeliverPostTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := [tDlOut, tDlIn, .opt .nat, tDl, tR2, tR1] ++ Γ0)
    (.fst .v3) .v2 (.fst (.snd (.fst .v0)))
    (hst2Tr C K Dh encPt encT decT lam .v6)
  dsimp only [hop2StepTier2TrackC]
  simp only [Comp.size, wk1Comp_size]
  dsimp only [hop2TrArmTier2TrackC, hop2ChArmTier2TrackC, hop2CrArmTier2E, tier2SamIfNec512C]
  generalize (hop2DlArmTier2C C K Dh encPt encT decT lam M k).size = sdl at hdij ⊢
  generalize (hop2IjArmTier2C C K Dh encPt encT decT lam M qep k).size = sij at hdij ⊢
  generalize stepKemFailSendTier2C (Pt := Pt) (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2)))
    (.fst .v1) = kf1 at hkf1 ⊢
  generalize stepKemFailSendTier2C (Pt := Pt) (.fst (.fst (.snd .v2))) (.fst (.snd (.snd .v2)))
    (.fst .v1) = kf2 at hkf2 ⊢
  generalize recordHonestWireTier2E (Pt := Pt) (.snd (.fst (.snd .v4))) (.snd .v0)
    (.fst (.snd (.snd .v4))) = hwE1 at hhw1 ⊢
  generalize recordHonestWireTier2E (Pt := Pt) (.snd (.fst (.snd .v4))) (.snd .v0)
    (.fst (.snd (.snd .v4))) = hwE2 at hhw2 ⊢
  generalize findRevHonestWireIdxTier2E (Pt := Pt) _ _ _ = findE at hfind ⊢
  generalize kemOnDeliverPostTier2E (Pt := Pt) _ _ _ _ = kemDlE at hkemDl ⊢
  simp only [Comp.size, M.embedCoin_size, hd512,
    hst2Base, hst2SessionTr, hst2Tr, hst2Wires, hst2Mk,
    stSTier2, stAuxTier2, stMkTier2,
    tier2SmRWireE, tier2SmRCorrE,
    tier2RecMk, sendOKTier2E, safeChTier2E, leakTier2E, sendsInE,
    CryptoGames.SM.healedByE, CryptoGames.SM.maxOptE, CryptoGames.SM.leN,
    corrAllowedTier2E, afterCorrAllowedTier2E, inWindowTier2E, corrOKTier2E,
    orE, maxN, pGet,
    gsWinTier2E, gsBTier2E, gsStTier2E, gsEpochTier2E, gsIdxTier2E,
    gsTLTier2E, gsMaxAccTier2E, gsChallTblTier2E, gsChallCountTier2E,
    gsCompTblTier2E, gsUncompCountTier2E,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2]
    at hep1 hkf1 hdrS1 hrc1 hhw1 hep2 hkf2 hdrS2 hrc2 hhw2 hfind hkemDl ⊢
  omega

private theorem qep_le_spkTier2Budget_local (ℓ q qep qep' : ℕ) (hqep : qep ≤ q + 10) :
    qep ≤ spkTier2Budget q qep' ℓ := by
  have hb := spk_totalCost_le_spkTier2Budget q qep' ℓ 10 0 0
    (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
  omega

theorem spkHop2PrgProgHaltedTier2_totalQueries_zero (ℓ q qep k : ℕ) :
    (spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  unfold spkHop2PrgProgHaltedTier2
  split_ifs
  · dsimp only [spkHop2PrgProgHaltedTier2Real, hop2GameTier2TrackRed, CostedReduction.totalQueries]
    simp only [queries_coinOnly_zero]; omega
  · exact dummyBoolSessionRed_totalQueries _ _ _ _ _

theorem spkHop2PrgProgHaltedTier2_totalCost_le (ℓ q qep k : ℕ) {qep' : ℕ} (hle : qep ≤ qep') :
    (spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost
      q ≤ spkTier2Budget q qep' ℓ := by
  unfold spkHop2PrgProgHaltedTier2
  split_ifs with h
  · have hi := cost_hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hs := cost_hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam h.1 h.2
      (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep
    have hbm := bits_mono hle
    have hfin : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (I := coinOnlyIface ℓ Pt) (Γ := [hop2HaltedTier2StTy ℓ Pt, .bool])
        (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam
          (hst2Base C K Dh encPt encT decT lam .v0)))).cost = 10 := rfl
    have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 75000 10
      (5165000 + 61 * ℓ + 2 * bits qep')
      (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
    dsimp only [spkHop2PrgProgHaltedTier2Real, hop2GameTier2TrackRed, CostedReduction.totalCost]
    have hinitEq :
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)).embedCoin
          (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k) =
        hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k := rfl
    rw [hinitEq, hfin]
    generalize (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost =
      ci at hi ⊢
    generalize (hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).cost = ch at hs ⊢
    have hmul : q * max 1 (ch + 16) ≤ q * (16 + (5165000 + 61 * ℓ + 2 * bits qep')) :=
      Nat.mul_le_mul_left q (by omega)
    omega
  · have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 3 3 8
      (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
    dsimp only [dummyBoolSessionRed, CostedReduction.totalCost, Comp.cost, Expr.cost]
    have hmax : max 1 (1 + (1 + 1 + 1) + 1 + 1 + 1 + 1 + 16) = 24 := by decide
    rw [hmax]; omega

theorem spkHop2PrgProgHaltedTier2_size_raw_le (ℓ q qep k : ℕ) :
    (spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      7860000 + 9 * bits qep := by
  unfold spkHop2PrgProgHaltedTier2
  split_ifs with h
  · have hi := size_hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hs := size_hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam h.1 h.2
      (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep
    have hfin : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (I := coinOnlyIface ℓ Pt) (Γ := [hop2HaltedTier2StTy ℓ Pt, .bool])
        (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam
          (hst2Base C K Dh encPt encT decT lam .v0)))).size = 10 := rfl
    have hinitEq :
        (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)).embedCoin
          (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k) =
        hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k := rfl
    dsimp only [spkHop2PrgProgHaltedTier2Real, hop2GameTier2TrackRed, CostedReduction.size]
    rw [hinitEq, hfin]
    generalize (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size =
      si at hi ⊢
    generalize (hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prgCoinMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).size = sh at hs ⊢
    omega
  · dsimp only [dummyBoolSessionRed, CostedReduction.size, Comp.size, Expr.size]
    omega

theorem spkHop2PrgProgHaltedTier2_gRedBounded_of_le (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ q + 10) (hle : qep ≤ qep') :
    GRedBounded
      (spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      Empty.elim (fun _ => 0) q 0 (spkTier2Budget q qep' ℓ) := by
  refine gRedBounded_of_bounds
    (spkHop2PrgProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    Empty.elim (fun _ => 0) q 0 (spkTier2Budget q qep' ℓ)
    (spkHop2PrgProgHaltedTier2_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hle)
    ?_
    (Nat.le_of_eq
      (spkHop2PrgProgHaltedTier2_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep k))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (show _root_.ReductionDsl.SampSizeHonest (coinOnlyIface ℓ Pt).smp from
      atomicSamplers_sizeHonest ℓ Pt)
  have hraw := spkHop2PrgProgHaltedTier2_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hbm := bits_mono (qep_le_spkTier2Budget_local ℓ q qep qep' hqep)
  have hrb : (7860000 : ℕ) ≤ reductionSizeBudget := by decide
  omega

theorem spkHop2PrfProgHaltedTier2_totalQueries_le (ℓ q qep k : ℕ) :
    (spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q := by
  unfold spkHop2PrfProgHaltedTier2
  split_ifs
  · have hq := queries_hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k
    change (hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).queries
        (fun _ => 1) (fun _ => 0) ≤ 1 at hq
    have hqi :
        (hop2InitPrfTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).queries
          (fun _ => 1) (fun _ => 0) = 0 :=
      queries_compCoinToPrf_zero _ _
    have hqf : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (I := extractPtPrfIface ℓ Pt) (Γ := [hop2HaltedTier2StTy ℓ Pt, .bool])
        (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam
          (hst2Base C K Dh encPt encT decT lam .v0)))).queries (fun _ => 1) (fun _ => 0) = 0 := rfl
    dsimp only [spkHop2PrfProgHaltedTier2Real, CostedReduction.totalQueries]
    rw [hqi, hqf]
    generalize (hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).queries
        (fun _ => 1) (fun _ => 0) = qh at hq ⊢
    have hmul : q * qh ≤ q * 1 := Nat.mul_le_mul_left q hq
    omega
  · simp only [dummyBoolSessionRed_totalQueries]; omega

theorem spkHop2PrfProgHaltedTier2_totalCost_le (ℓ q qep k : ℕ) {qep' : ℕ} (hle : qep ≤ qep') :
    (spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).totalCost
      q ≤ spkTier2Budget q qep' ℓ := by
  unfold spkHop2PrfProgHaltedTier2
  split_ifs with h
  · have hi0 := cost_hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hi :
        (hop2InitPrfTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost ≤
          75100 := by
      dsimp only [hop2InitPrfTier2TrackC]
      simp only [cost_compCoinToPrf, Comp.cost, draw256Coin_cost, wk1Comp_cost,
        Expr.cost, Expr.v0, Expr.v1, Expr.v2]
      generalize (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost =
        ci0 at hi0 ⊢
      omega
    have hs := cost_hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam h.1 h.2
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep
    have hbm := bits_mono hle
    have hfin : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (I := extractPtPrfIface ℓ Pt) (Γ := [hop2HaltedTier2StTy ℓ Pt, .bool])
        (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam
          (hst2Base C K Dh encPt encT decT lam .v0)))).cost = 10 := rfl
    have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 75100 10
      (5165000 + 61 * ℓ + 2 * bits qep')
      (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
    dsimp only [spkHop2PrfProgHaltedTier2Real, CostedReduction.totalCost]
    rw [hfin]
    generalize (hop2InitPrfTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).cost =
      ci at hi ⊢
    generalize (hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).cost = ch at hs ⊢
    have hmul : q * max 1 (ch + 16) ≤ q * (16 + (5165000 + 61 * ℓ + 2 * bits qep')) :=
      Nat.mul_le_mul_left q (by omega)
    omega
  · have hbud := spk_totalCost_le_spkTier2Budget q qep' ℓ 3 3 8
      (by unfold maxForwardJumps; omega) (by unfold maxForwardJumps; omega)
    dsimp only [dummyBoolSessionRed, CostedReduction.totalCost, Comp.cost, Expr.cost]
    have hmax : max 1 (1 + (1 + 1 + 1) + 1 + 1 + 1 + 1 + 16) = 24 := by decide
    rw [hmax]; omega

theorem spkHop2PrfProgHaltedTier2_size_raw_le (ℓ q qep k : ℕ) :
    (spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k).size ≤
      7860000 + 9 * bits qep := by
  unfold spkHop2PrfProgHaltedTier2
  split_ifs with h
  · have hi0 := size_hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k
    have hi :
        (hop2InitPrfTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size ≤
          6320 := by
      dsimp only [hop2InitPrfTier2TrackC]
      simp only [size_compCoinToPrf, Comp.size, draw256Coin_size, wk1Comp_size,
        Expr.size, Expr.v0, Expr.v1, Expr.v2]
      generalize (hop2InitBodyTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size =
        si0 at hi0 ⊢
      omega
    have hs := size_hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam h.1 h.2
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep
    have hfin : (Comp.ret (O := atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
        (I := extractPtPrfIface ℓ Pt) (Γ := [hop2HaltedTier2StTy ℓ Pt, .bool])
        (auxBadTier2 (stAuxTier2 C K Dh encPt encT decT lam
          (hst2Base C K Dh encPt encT decT lam .v0)))).size = 10 := rfl
    dsimp only [spkHop2PrfProgHaltedTier2Real, CostedReduction.size]
    rw [hfin]
    generalize (hop2InitPrfTier2TrackC (ℓ := ℓ) (Pt := Pt) C K Dh encPt encT decT idA idB lam k).size =
      si at hi ⊢
    generalize (hop2StepTier2TrackC (ℓ := ℓ) C K Dh encPt encT decT lam
      (prfOracleMode (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)) qep k).size = sh at hs ⊢
    omega
  · dsimp only [dummyBoolSessionRed, CostedReduction.size, Comp.size, Expr.size]
    omega

theorem spkHop2PrfProgHaltedTier2_gRedBounded_of_le (ℓ q qep k : ℕ) {qep' : ℕ}
    (hqep : qep ≤ q + 10) (hle : qep ≤ qep') :
    GRedBounded
      (spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
      (fun _ => 1) (fun _ => 0) q q (spkTier2Budget q qep' ℓ) := by
  refine gRedBounded_of_bounds
    (spkHop2PrfProgHaltedTier2 (Pt := Pt) C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (fun _ => 1) (fun _ => 0) q q (spkTier2Budget q qep' ℓ)
    (spkHop2PrfProgHaltedTier2_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep k hle)
    ?_
    (spkHop2PrfProgHaltedTier2_totalQueries_le C K Dh encPt encT decT idA idB lam ℓ q qep k)
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (show _root_.ReductionDsl.SampSizeHonest (extractPtPrfIface ℓ Pt).smp from
      atomicSamplers_sizeHonest ℓ Pt)
  have hraw := spkHop2PrfProgHaltedTier2_size_raw_le C K Dh encPt encT decT idA idB lam ℓ q qep k
  have hbm := bits_mono (qep_le_spkTier2Budget_local ℓ q qep qep' hqep)
  have hrb : (7860000 : ℕ) ≤ reductionSizeBudget := by decide
  omega

end Tier2HaltedStep

end Computational.Proofs.Game.PromotedCostedReds.HaltedSpkHop2Tier2Step
