/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys -- proof-setup: allow-public-import
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl

/-!
# Table-Backed Per-Session KEM-Failure Tracker Gadget

Implements `Ty.tbl`-backed `SimKemFailTrack` (`kemTrackTier2T`) and honest-wire reverse-index
lookup (`honestWiresTier2T`) over `atomicSessionOps` with `q`-independent step cost, together
with canonical pure encodings and `.eval` theorems.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Env Iface Expr Comp atomicSig atomicSessionOps
  partyToBool spqrMsgPayloadSuffix B BV256 BV512 PlainT recvResultT recvResultEnc bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (RecvResult)
open CryptoGames.LibsignalSession (Crypto PublicKey ShaCompress)
open CryptoGames.Ratchet.LibsignalSim (SimKemSeed SimKemEncRand SimKemFailTrack
  simInitKemFailTrack simStepKemFailSend simStepKemFailDeliver)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (sessionEmbed kemSentEntryT kemTrackT SimKemSessionTrack simInitKemSessionTrack
   kemCandVecToBv kemTrackAtomicEnc trE_e trE_c trE_st trE_sentB trE_sendCtr trE_cand
   trCandIsSomeE trMk pGet pSet initKemFailTrackE stepKemFailSendPairC stepKemFailDeliverE
   initKemFailTrackE_cost_le stepKemFailSendPairC_cost_le stepKemFailDeliverE_cost_le
   initKemFailTrackE_size_le stepKemFailSendPairC_size_le stepKemFailDeliverE_size_le
   stepKemFailSendPairC_queries_zero)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux
  (KemTrackDeliverInv kemTrackDeliverInv_initSim kemTrackDeliverInv_stepDeliverSim
   kemTrackDeliverInv_stepSendSim)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl
  (initKemFailTrackE_eval stepKemFailSendPairC_eval stepKemFailDeliverE_eval)
open Computational.Proofs.Game.PromotedCostedReds.SpkTier2Keys
  (spkMaxWireLen spkWireChunks spkWireKeyVal spkWireKeyVal_injective
   wireKeyVal_eq_some_of_le wireKeyVal_eq_none_of_gt
   spkWireKeyE eval_spkWireKeyE cost_spkWireKeyE_of_lt size_spkWireKeyE_of_lt)

/-! ## State types and encodings -/

/-- Table-backed `SimKemFailTrack` representation `(trBase, (sentLen, sentTbl))`. -/
@[expose, reducible] def kemTrackTier2T (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.prod .nat (.tbl (.opt (kemSentEntryT ℓ Pt))))

/-- Table-backed `honestWires` representation `(wireCount, (tblA, tblB))`. -/
@[expose, reducible] def honestWiresTier2T (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .nat (.prod (.tbl (.opt .nat)) (.tbl (.opt .nat)))

@[expose, reducible] def kemSessionTrackTier2T (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackTier2T ℓ Pt) (honestWiresTier2T ℓ Pt)

@[expose] def kemTrackTier2Enc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (tr : SimKemFailTrack F) : (kemTrackTier2T ℓ Pt).denote :=
  (kemTrackAtomicEnc { tr with sentB := [] },
   (tr.sentB.length,
    fun j => (tr.sentB[j]?).map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr))))

@[expose] def tblInsertFirst (tbl : ℕ → Option ℕ) (k idx : ℕ) : ℕ → Option ℕ :=
  match tbl k with
  | none => fun k' => if k' = k then some idx else tbl k'
  | some _ => tbl

@[expose] def honestWiresSubTbl (ℓ : ℕ) (P : Party) : List (Bytes × Party) → (ℕ → Option ℕ)
  | [] => fun _ => none
  | (w, P0) :: rest =>
    let sub := honestWiresSubTbl ℓ P rest
    if P0 = P then
      match spkWireKeyVal ℓ w with
      | none => sub
      | some k => tblInsertFirst sub k rest.length
    else sub

@[expose] def honestWiresTier2Enc (ℓ : ℕ) {Pt : Type}
    (hw : List (Bytes × Party)) : (honestWiresTier2T ℓ Pt).denote :=
  (hw.length, (honestWiresSubTbl ℓ .A hw, honestWiresSubTbl ℓ .B hw))

@[expose] def kemSessionTrackTier2Enc (ℓ : ℕ) {Pt : Type} {F : ShaCompress}
    (st : SimKemSessionTrack F Bytes) : (kemSessionTrackTier2T ℓ Pt).denote :=
  (kemTrackTier2Enc st.1, honestWiresTier2Enc ℓ st.2)

/-- Braid state and message-deserialization invariant for `SimKemFailTrack`. -/
structure KemTrackTier2Inv (F : ShaCompress) (K : MlKem) (tr : SimKemFailTrack F) : Prop where
  bOk : ∀ Q : Party, BOkTight (tr.st Q)
  sentB_deser : ∀ mc ∈ tr.sentB,
    CryptoVerification.LibsignalSpqrV1.Message.deserialize
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi mc.1.epoch (spqrMsgPayloadSuffix mc.1) =
      .ok mc.1

theorem KemTrackTier2Inv.of_deliverInv {F : ShaCompress} {K : MlKem} {L : ℕ}
    {tr : SimKemFailTrack F} (h : KemTrackDeliverInv F K L tr) : KemTrackTier2Inv F K tr :=
  ⟨h.bOk, h.sentB_deser⟩

theorem KemTrackTier2Inv.to_deliverInv {F : ShaCompress} {K : MlKem}
    {tr : SimKemFailTrack F} (h : KemTrackTier2Inv F K tr) :
    KemTrackDeliverInv F K tr.sentB.length tr :=
  ⟨Nat.le_refl _, h.bOk, h.sentB_deser⟩

theorem KemTrackTier2Inv.withCand {F : ShaCompress} {K : MlKem}
    {tr : SimKemFailTrack F} (h : KemTrackTier2Inv F K tr)
    (cand' : Option (SimKemSeed × SimKemEncRand)) :
    KemTrackTier2Inv F K { tr with cand := cand' } :=
  ⟨h.bOk, h.sentB_deser⟩

theorem kemTrackTier2Inv_initSim (F : ShaCompress) (K : MlKem) (pqrKey : BitVec 256) :
    KemTrackTier2Inv F K (simInitKemFailTrack F pqrKey) :=
  KemTrackTier2Inv.of_deliverInv (kemTrackDeliverInv_initSim F K 0 pqrKey)

theorem kemTrackTier2Inv_stepSendSim (F : ShaCompress) (K : MlKem)
    (tr : SimKemFailTrack F) (Q : Party) (r : BitVec 512) (h : KemTrackTier2Inv F K tr) :
    KemTrackTier2Inv F K (simStepKemFailSend F K tr Q r) :=
  KemTrackTier2Inv.of_deliverInv (kemTrackDeliverInv_stepSendSim F K tr.sentB.length tr Q r h.to_deliverInv)

theorem kemTrackTier2Inv_stepDeliverSim (F : ShaCompress) (K : MlKem)
    (tr : SimKemFailTrack F) (Q : Party) (j : ℕ) (h : KemTrackTier2Inv F K tr) :
    KemTrackTier2Inv F K (simStepKemFailDeliver F K tr Q j) :=
  KemTrackTier2Inv.of_deliverInv (kemTrackDeliverInv_stepDeliverSim F K tr.sentB.length tr Q j h.to_deliverInv)

/-! ## DSL combinators -/

section DslOps

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "sEmb" => sessionEmbed ℓ Pt C K Dh encPt encT decT lam

@[expose] def tr2_cand {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) : Expr AOps Γ (.opt (.prod BV512 BV256)) :=
  trE_cand (.fst tr2E)

@[expose] def tr2CandIsSomeE {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) : Expr AOps Γ .bool :=
  trCandIsSomeE (.fst tr2E)

@[expose] def resetSentBNilE {Γ : List (Ty ASig)}
    (trBaseE : Expr AOps Γ (kemTrackT ℓ Pt)) : Expr AOps Γ (kemTrackT ℓ Pt) :=
  .letE trBaseE (trMk (trE_e .v0) (trE_c .v0) (trE_st .v0) .nil (trE_sendCtr .v0) (trE_cand .v0))

@[expose] def initKemFailTrackTier2E {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) : Expr AOps Γ (kemTrackTier2T ℓ Pt) :=
  .pair (initKemFailTrackE sEmb pqrKeyE) (.pair (.nat 0) (.tconst .none))

@[expose] def initHonestWiresTier2E {Γ : List (Ty ASig)} : Expr AOps Γ (honestWiresTier2T ℓ Pt) :=
  .pair (.nat 0) (.pair (.tconst .none) (.tconst .none))

@[expose] def initKemFailSessionTrackTier2E {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt) :=
  .pair (initKemFailTrackTier2E pqrKeyE) initHonestWiresTier2E

@[expose] def stepKemFailSendPairTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    Comp AOps I Γ (.prod (kemTrackTier2T ℓ Pt) (kemTrackTier2T ℓ Pt)) :=
  .bind (.ret (.pair tr2E (.pair qBE rqE)))
    (.bind (stepKemFailSendPairC sEmb 0 (.fst (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0)))
      (.ret
        (let sentPair := Expr.snd (.fst .v1)
         let trFull0 := Expr.fst .v0
         let trCand0 := Expr.snd .v0
         let headOpt := Expr.foldrB 1 (trE_sentB trFull0) .none (.some .v0)
         let full2 : Expr AOps _ (kemTrackTier2T ℓ Pt) :=
           .caseOpt headOpt
             (.pair trFull0 sentPair)
             (.pair (resetSentBNilE (.fst .v1))
               (.pair (.add (.fst (.snd (.fst .v2))) (.nat 1))
                 (.tset (.snd (.snd (.fst .v2))) (.fst (.snd (.fst .v2))) (.some .v0))))
         let candOnly2 : Expr AOps _ (kemTrackTier2T ℓ Pt) := .pair trCand0 sentPair
         .pair full2 candOnly2)))

@[expose] def stepKemFailSendTier2C {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) : Comp AOps I Γ (.prod .bool (kemTrackTier2T ℓ Pt)) :=
  .bind (stepKemFailSendPairTier2C tr2E qBE rqE)
    (.ret (.ite (tr2CandIsSomeE (.fst .v0))
      (.pair (.bool true) (.snd .v0))
      (.pair (.bool false) (.fst .v0))))

/-- First-write-wins insertion of `(wE, pBE)` into `honestWiresTier2T`. -/
@[expose] def recordHonestWireTier2E {Γ : List (Ty ASig)}
    (hw2E : Expr AOps Γ (honestWiresTier2T ℓ Pt))
    (wE : Expr AOps Γ (B 32)) (pBE : Expr AOps Γ .bool) :
    Expr AOps Γ (honestWiresTier2T ℓ Pt) :=
  .letE (.pair hw2E (.pair (spkWireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) wE) pBE))
    (let hw0 := Expr.fst .v0
     let cnt0 := Expr.fst hw0
     let tbls0 := Expr.snd hw0
     let tbls' : Expr AOps _ (.prod (.tbl (.opt .nat)) (.tbl (.opt .nat))) :=
       .caseOpt (.fst (.snd .v0)) tbls0
         (let tbls1 := Expr.snd (.fst .v1)
          let p1 := Expr.snd (.snd .v1)
          let sub1 := pGet tbls1 p1
          .caseOpt (.tget sub1 .v0)
            (pSet tbls1 p1 (.tset sub1 .v0 (.some (.fst (.fst .v1)))))
            (.snd (.fst .v2)))
     .pair (.add cnt0 (.nat 1)) tbls')

/-- Table-backed reverse honest-wire index lookup matching `honestWires.reverse.findIdx?`. -/
@[expose] def findRevHonestWireIdxTier2E {Γ : List (Ty ASig)}
    (hw2E : Expr AOps Γ (honestWiresTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt .nat) :=
  .letE (.pair hw2E (.pair qBE (spkWireKeyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) wE)))
    (.caseOpt (.snd (.snd .v0)) .none
      (.tget (pGet (.snd (.fst .v1)) (.not (.fst (.snd .v1)))) .v0))

@[expose] def stepKemFailDeliverTier2E {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (jE : Expr AOps Γ .nat) : Expr AOps Γ (kemTrackTier2T ℓ Pt) :=
  .letE (.pair tr2E (.pair qBE jE))
    (let tr2_0 := Expr.fst .v0
     let j0 := Expr.snd (.snd .v0)
     .caseOpt (.tget (.snd (.snd tr2_0)) j0) tr2_0
       (let tr2_1 := Expr.fst .v1
        let q1 := Expr.fst (.snd .v1)
        let base1 := Expr.fst tr2_1
        let trTmp := trMk (trE_e base1) (trE_c base1) (trE_st base1)
          (.cons .v0 .nil) (trE_sendCtr base1) (trE_cand base1)
        let trDelivered := stepKemFailDeliverE sEmb 1 trTmp q1 (.nat 0)
        .pair (resetSentBNilE trDelivered) (.snd tr2_1)))

@[expose] def kemOnDeliverPostTier2E {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) : Expr AOps Γ (kemTrackTier2T ℓ Pt) :=
  .letE (.pair qBE (.pair jOptE (.pair rrOptE tr2E)))
    (.caseOpt (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
      (.caseSum .v0 (.snd (.snd (.snd .v2)))
        (.caseOpt (.fst (.snd .v2)) (.snd (.snd (.snd .v2)))
          (stepKemFailDeliverTier2E (.snd (.snd (.snd .v3))) (.fst .v3) .v0))))

@[expose] def stepKemSessionDeliverOptTier2E {Γ : List (Ty ASig)}
    (st2E : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (jOptE : Expr AOps Γ (.opt .nat)) : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt) :=
  .letE (.pair st2E (.pair qBE jOptE))
    (let st0 := Expr.fst .v0
     .caseOpt (.snd (.snd .v0)) st0
       (.pair (stepKemFailDeliverTier2E (.fst (.fst .v1)) (.fst (.snd .v1)) .v0)
              (.snd (.fst .v1))))

/-! ## Cost and size bounds -/

theorem stepKemFailSendPairTier2C_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (stepKemFailSendPairTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I := I) tr2E qBE rqE).queries w ws = 0 := by
  simp [stepKemFailSendPairTier2C, Comp.queries, stepKemFailSendPairC_queries_zero]

theorem stepKemFailSendTier2C_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (stepKemFailSendTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I := I) tr2E qBE rqE).queries w ws = 0 := by
  simp [stepKemFailSendTier2C, Comp.queries, stepKemFailSendPairTier2C_queries_zero]

theorem initKemFailTrackTier2E_cost_le {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    (initKemFailTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).cost ≤ pqrKeyE.cost + 7620 := by
  have h0 := initKemFailTrackE_cost_le sEmb pqrKeyE
  have hb0 : bits 0 = 1 := by decide
  dsimp only [initKemFailTrackTier2E, Expr.cost]
  omega

theorem initHonestWiresTier2E_cost_le {Γ : List (Ty ASig)} :
    (initHonestWiresTier2E (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost ≤ 20 := by
  have hb0 : bits 0 = 1 := by decide
  dsimp only [initHonestWiresTier2E, Expr.cost]
  omega

theorem initKemFailSessionTrackTier2E_cost_le {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    (initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).cost ≤ pqrKeyE.cost + 7650 := by
  have h1 := initKemFailTrackTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) pqrKeyE
  have h2 := initHonestWiresTier2E_cost_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  dsimp only [initKemFailSessionTrackTier2E, Expr.cost]
  omega

theorem stepKemFailSendPairTier2C_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendPairTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I := I) tr2E qBE rqE).cost ≤
      tr2E.cost + qBE.cost + rqE.cost + 1155300 := by
  have hs := stepKemFailSendPairC_cost_le sEmb 0 (I := I)
    (Γ := .prod (kemTrackTier2T ℓ Pt) (.prod .bool BV512) :: Γ)
    (.fst (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hb1 : bits 1 = 1 := by decide
  dsimp only [stepKemFailSendPairTier2C, resetSentBNilE, trMk, trE_e, trE_c, trE_st, trE_sentB,
    trE_sendCtr, trE_cand, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2] at hs ⊢
  omega

theorem stepKemFailSendTier2C_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I := I) tr2E qBE rqE).cost ≤
      tr2E.cost + qBE.cost + rqE.cost + 1155350 := by
  have hs := stepKemFailSendPairTier2C_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := I) tr2E qBE rqE
  dsimp only [stepKemFailSendTier2C, tr2CandIsSomeE, trCandIsSomeE, trE_cand,
    Comp.cost, Expr.cost, Expr.v0]
  omega

theorem recordHonestWireTier2E_cost_le {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (hw2E : Expr AOps Γ (honestWiresTier2T ℓ Pt))
    (wE : Expr AOps Γ (B 32)) (pBE : Expr AOps Γ .bool) :
    (recordHonestWireTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hw2E wE pBE).cost ≤
      hw2E.cost + wE.cost + pBE.cost + 30 * ℓ + 14400 := by
  have hk := cost_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) hℓ wE
  have hb1 : bits 1 = 1 := by decide
  dsimp only [recordHonestWireTier2E, pGet, pSet, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem findRevHonestWireIdxTier2E_cost_le {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (hw2E : Expr AOps Γ (honestWiresTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hw2E qBE wE).cost ≤
      hw2E.cost + qBE.cost + wE.cost + 30 * ℓ + 14150 := by
  have hk := cost_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) hℓ wE
  dsimp only [findRevHonestWireIdxTier2E, pGet, Expr.cost, Expr.v0, Expr.v1]
  omega

theorem stepKemFailDeliverTier2E_cost_le {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (jE : Expr AOps Γ .nat) :
    (stepKemFailDeliverTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) tr2E qBE jE).cost ≤
      tr2E.cost + qBE.cost + jE.cost + 8300 := by
  have hd := stepKemFailDeliverE_cost_le sEmb 1
    (Γ := kemSentEntryT ℓ Pt :: .prod (kemTrackTier2T ℓ Pt) (.prod .bool .nat) :: Γ)
    (trMk (trE_e (.fst (.fst .v1))) (trE_c (.fst (.fst .v1))) (trE_st (.fst (.fst .v1)))
      (.cons .v0 .nil) (trE_sendCtr (.fst (.fst .v1))) (trE_cand (.fst (.fst .v1))))
    (.fst (.snd .v1)) (.nat 0)
  have hb0 : bits 0 = 1 := by decide
  dsimp only [stepKemFailDeliverTier2E, resetSentBNilE, trMk, trE_e, trE_c, trE_st, trE_sendCtr,
    trE_cand, Expr.cost, Expr.v0, Expr.v1] at hd ⊢
  omega

theorem kemOnDeliverPostTier2E_cost_le {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) :
    (kemOnDeliverPostTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qBE jOptE rrOptE tr2E).cost ≤
      qBE.cost + jOptE.cost + rrOptE.cost + tr2E.cost + 8400 := by
  have hd := stepKemFailDeliverTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .nat :: .prod .nat (.prod .nat (.opt (PlainT (ℓ := ℓ) (Pt := Pt)))) ::
      recvResultT (ℓ := ℓ) (Pt := Pt) ::
      .prod .bool (.prod (.opt .nat) (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (kemTrackTier2T ℓ Pt))) :: Γ)
    (.snd (.snd (.snd .v3))) (.fst .v3) .v0
  dsimp only [kemOnDeliverPostTier2E, Expr.cost, Expr.v0, Expr.v2, Expr.v3] at hd ⊢
  omega

theorem stepKemSessionDeliverOptTier2E_cost_le {Γ : List (Ty ASig)}
    (st2E : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (jOptE : Expr AOps Γ (.opt .nat)) :
    (stepKemSessionDeliverOptTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) st2E qBE jOptE).cost ≤
      st2E.cost + qBE.cost + jOptE.cost + 8400 := by
  have hd := stepKemFailDeliverTier2E_cost_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .nat :: .prod (kemSessionTrackTier2T ℓ Pt) (.prod .bool (.opt .nat)) :: Γ)
    (.fst (.fst .v1)) (.fst (.snd .v1)) .v0
  dsimp only [stepKemSessionDeliverOptTier2E, Expr.cost, Expr.v0, Expr.v1] at hd ⊢
  omega

theorem initKemFailTrackTier2E_size_le {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    (initKemFailTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).size ≤ pqrKeyE.size + 120 := by
  have h0 := initKemFailTrackE_size_le sEmb pqrKeyE
  have hb0 : bits 0 = 1 := by decide
  dsimp only [initKemFailTrackTier2E, Expr.size]
  omega

theorem initHonestWiresTier2E_size_le {Γ : List (Ty ASig)} :
    (initHonestWiresTier2E (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).size ≤ 20 := by
  have hb0 : bits 0 = 1 := by decide
  dsimp only [initHonestWiresTier2E, Expr.size]
  omega

theorem initKemFailSessionTrackTier2E_size_le {Γ : List (Ty ASig)} (pqrKeyE : Expr AOps Γ BV256) :
    (initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).size ≤ pqrKeyE.size + 150 := by
  have h1 := initKemFailTrackTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) pqrKeyE
  have h2 := initHonestWiresTier2E_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  dsimp only [initKemFailSessionTrackTier2E, Expr.size]
  omega

theorem stepKemFailSendPairTier2C_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendPairTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I := I) tr2E qBE rqE).size ≤
      tr2E.size + qBE.size + rqE.size + 1000 := by
  have hs := stepKemFailSendPairC_size_le sEmb 0 (I := I)
    (Γ := .prod (kemTrackTier2T ℓ Pt) (.prod .bool BV512) :: Γ)
    (.fst (.fst .v0)) (.fst (.snd .v0)) (.snd (.snd .v0))
  have hb01 : bits (0 + 1) = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [stepKemFailSendPairTier2C, resetSentBNilE, trMk, trE_e, trE_c, trE_st, trE_sentB,
    trE_sendCtr, trE_cand, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2] at hs ⊢
  omega

theorem stepKemFailSendTier2C_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I := I) tr2E qBE rqE).size ≤
      tr2E.size + qBE.size + rqE.size + 1050 := by
  have hs := stepKemFailSendPairTier2C_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I := I) tr2E qBE rqE
  dsimp only [stepKemFailSendTier2C, tr2CandIsSomeE, trCandIsSomeE, trE_cand,
    Comp.size, Expr.size, Expr.v0]
  omega

theorem recordHonestWireTier2E_size_le {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (hw2E : Expr AOps Γ (honestWiresTier2T ℓ Pt))
    (wE : Expr AOps Γ (B 32)) (pBE : Expr AOps Γ .bool) :
    (recordHonestWireTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hw2E wE pBE).size ≤
      hw2E.size + wE.size + pBE.size + 900 := by
  have hk := size_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) hℓ wE
  have hb1 : bits 1 = 1 := by decide
  dsimp only [recordHonestWireTier2E, pGet, pSet, Expr.size, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem findRevHonestWireIdxTier2E_size_le {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (hw2E : Expr AOps Γ (honestWiresTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hw2E qBE wE).size ≤
      hw2E.size + qBE.size + wE.size + 850 := by
  have hk := size_spkWireKeyE_of_lt (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) hℓ wE
  dsimp only [findRevHonestWireIdxTier2E, pGet, Expr.size, Expr.v0, Expr.v1]
  omega

theorem stepKemFailDeliverTier2E_size_le {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (jE : Expr AOps Γ .nat) :
    (stepKemFailDeliverTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) tr2E qBE jE).size ≤
      tr2E.size + qBE.size + jE.size + 510 := by
  have hd := stepKemFailDeliverE_size_le sEmb 1
    (Γ := kemSentEntryT ℓ Pt :: .prod (kemTrackTier2T ℓ Pt) (.prod .bool .nat) :: Γ)
    (trMk (trE_e (.fst (.fst .v1))) (trE_c (.fst (.fst .v1))) (trE_st (.fst (.fst .v1)))
      (.cons .v0 .nil) (trE_sendCtr (.fst (.fst .v1))) (trE_cand (.fst (.fst .v1))))
    (.fst (.snd .v1)) (.nat 0)
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  dsimp only [stepKemFailDeliverTier2E, resetSentBNilE, trMk, trE_e, trE_c, trE_st, trE_sendCtr,
    trE_cand, Expr.size, Expr.v0, Expr.v1] at hd ⊢
  omega

theorem kemOnDeliverPostTier2E_size_le {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) :
    (kemOnDeliverPostTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qBE jOptE rrOptE tr2E).size ≤
      qBE.size + jOptE.size + rrOptE.size + tr2E.size + 560 := by
  have hd := stepKemFailDeliverTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .nat :: .prod .nat (.prod .nat (.opt (PlainT (ℓ := ℓ) (Pt := Pt)))) ::
      recvResultT (ℓ := ℓ) (Pt := Pt) ::
      .prod .bool (.prod (.opt .nat) (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (kemTrackTier2T ℓ Pt))) :: Γ)
    (.snd (.snd (.snd .v3))) (.fst .v3) .v0
  dsimp only [kemOnDeliverPostTier2E, Expr.size, Expr.v0, Expr.v2, Expr.v3] at hd ⊢
  omega

theorem stepKemSessionDeliverOptTier2E_size_le {Γ : List (Ty ASig)}
    (st2E : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (jOptE : Expr AOps Γ (.opt .nat)) :
    (stepKemSessionDeliverOptTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) st2E qBE jOptE).size ≤
      st2E.size + qBE.size + jOptE.size + 560 := by
  have hd := stepKemFailDeliverTier2E_size_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .nat :: .prod (kemSessionTrackTier2T ℓ Pt) (.prod .bool (.opt .nat)) :: Γ)
    (.fst (.fst .v1)) (.fst (.snd .v1)) .v0
  dsimp only [stepKemSessionDeliverOptTier2E, Expr.size, Expr.v0, Expr.v1] at hd ⊢
  omega

/-! ## Evaluation lemmas -/

theorem initKemFailTrackTier2E_eval {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) (ρ : Env Γ) (k : BitVec 256) (hk : pqrKeyE.eval ρ = k) :
    (initKemFailTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).eval ρ =
      kemTrackTier2Enc (simInitKemFailTrack C.F k) := by
  dsimp only [initKemFailTrackTier2E, Expr.eval]
  rw [initKemFailTrackE_eval sEmb pqrKeyE ρ, hk]
  rfl

theorem initHonestWiresTier2E_eval {Γ : List (Ty ASig)} (ρ : Env Γ) :
    (initHonestWiresTier2E (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).eval ρ =
      honestWiresTier2Enc ℓ [] := rfl

theorem initKemFailSessionTrackTier2E_eval {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) (ρ : Env Γ) (k : BitVec 256) (hk : pqrKeyE.eval ρ = k) :
    (initKemFailSessionTrackTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) pqrKeyE).eval ρ =
      kemSessionTrackTier2Enc ℓ (simInitKemSessionTrack C.F Bytes k) := by
  dsimp only [initKemFailSessionTrackTier2E, simInitKemSessionTrack, kemSessionTrackTier2Enc, Expr.eval]
  rw [initKemFailTrackTier2E_eval pqrKeyE ρ k hk, initHonestWiresTier2E_eval]

private theorem simStepKemFailSend_nil_sentB (tr : SimKemFailTrack C.F) (Q : Party) (r : BitVec 512) :
    let tr' := simStepKemFailSend C.F K tr Q r
    let tr0' := simStepKemFailSend C.F K { tr with sentB := [] } Q r
    { tr0' with sentB := [] } = { tr' with sentB := [] } ∧
      tr0'.cand = tr'.cand ∧
      ((tr0'.sentB = [] ∧ tr'.sentB = tr.sentB) ∨
       ∃ mc, tr0'.sentB = [mc] ∧ tr'.sentB = tr.sentB ++ [mc]) := by
  dsimp only [simStepKemFailSend]
  rcases (tr.st Q).send K (CryptoVerification.LibsignalSpqrV1.coinBytes r) with _ | ⟨out, _⟩
  · refine ⟨?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
    rfl
  · dsimp only
    refine ⟨rfl, rfl, Or.inr ⟨(out.msg, BitVec.ofNat 32 (tr.sendCtr Q (out.msg.epoch.toNat - 1) + 1)), rfl, rfl⟩⟩

theorem stepKemFailSendPairTier2C_eval {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (rq : BitVec 512)
    (htr : tr2E.eval ρ = kemTrackTier2Enc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq) (hBOk : BOkTight (tr.st Q)) :
    (stepKemFailSendPairTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I := I) tr2E qBE rqE).eval ρ =
      let tr' := simStepKemFailSend C.F K tr Q rq
      pure (kemTrackTier2Enc tr', kemTrackTier2Enc { tr with cand := tr'.cand }) := by
  simp only [stepKemFailSendPairTier2C, Comp.eval, Expr.eval, htr, hqB, hrq, pure_bind]
  set p0 : (Ty.prod (kemTrackTier2T ℓ Pt) (Ty.prod .bool BV512)).denote :=
    (kemTrackTier2Enc tr, (partyToBool Q, rq))
  rw [stepKemFailSendPairC_eval sEmb 0 _ _ _ (.cons p0 ρ) { tr with sentB := [] } Q rq
    (by simp [p0, kemTrackTier2Enc, Expr.eval, Expr.v0, Env.get])
    (by simp [p0, Expr.eval, Expr.v0, Env.get])
    (by simp [p0, Expr.eval, Expr.v0, Env.get])
    hBOk (by simp), pure_bind]
  obtain ⟨hbase, hcand, hcases⟩ := simStepKemFailSend_nil_sentB (C := C) (K := K) tr Q rq
  set tr' := simStepKemFailSend C.F K tr Q rq
  set tr0' := simStepKemFailSend C.F K { tr with sentB := [] } Q rq
  rcases hcases with ⟨h0nil, hlen_eq⟩ | ⟨⟨m, ctr⟩, h0one, happ⟩
  · have htr0_eq : tr0' = { tr' with sentB := [] } := by
      have h0 : { tr0' with sentB := [] } = tr0' := by
        clear_value tr0'
        cases tr0'
        cases h0nil
        rfl
      exact h0.symm.trans hbase
    simp [p0, kemTrackTier2Enc, kemTrackAtomicEnc, htr0_eq, hlen_eq,
      trE_sentB, Expr.eval, Expr.v0, Expr.v1, Env.get]
  · have hbaseEnc : kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt)
        { tr0' with sentB := [], cand := tr'.cand } =
        kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) { tr' with sentB := [] } := by
      simpa [hcand] using congrArg (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt)) hbase
    simp only [p0, kemTrackTier2Enc, kemTrackAtomicEnc, h0one, happ, hcand,
      resetSentBNilE, trMk, trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr, trE_cand,
      Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get,
      List.take, List.map, List.foldr, List.length_append, List.length_singleton]
    refine congrArg pure (Prod.ext (Prod.ext hbaseEnc (Prod.ext rfl ?_)) rfl)
    funext j
    by_cases hj : j = tr.sentB.length
    · subst hj
      simp
    · simp only [hj, ↓reduceIte]
      by_cases hlt : j < tr.sentB.length
      · rw [List.getElem?_append_left hlt]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem stepKemFailSendTier2C_eval {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (rq : BitVec 512)
    (htr : tr2E.eval ρ = kemTrackTier2Enc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = rq) (hBOk : BOkTight (tr.st Q)) :
    (stepKemFailSendTier2C (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I := I) tr2E qBE rqE).eval ρ =
      let tr' := simStepKemFailSend C.F K tr Q rq
      pure (tr'.cand.isSome,
        if tr'.cand.isSome then kemTrackTier2Enc { tr with cand := tr'.cand }
        else kemTrackTier2Enc tr') := by
  dsimp only [stepKemFailSendTier2C, Comp.eval]
  rw [stepKemFailSendPairTier2C_eval tr2E qBE rqE ρ tr Q rq htr hqB hrq hBOk, pure_bind]
  set tr' := simStepKemFailSend C.F K tr Q rq
  rcases hC : tr'.cand with _ | candVal <;>
    simp [tr2CandIsSomeE, trCandIsSomeE, trE_cand, kemTrackTier2Enc, kemTrackAtomicEnc, hC,
      Expr.eval, Expr.v0, Env.get]

theorem recordHonestWireTier2E_eval {Γ : List (Ty ASig)}
    (hw2E : Expr AOps Γ (honestWiresTier2T ℓ Pt))
    (wE : Expr AOps Γ (B 32)) (pBE : Expr AOps Γ .bool) (ρ : Env Γ)
    (hw : List (Bytes × Party)) (w : Bytes) (P : Party)
    (hhw : hw2E.eval ρ = honestWiresTier2Enc ℓ hw)
    (hwE : wE.eval ρ = w) (hpB : pBE.eval ρ = partyToBool P) :
    (recordHonestWireTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hw2E wE pBE).eval ρ =
      honestWiresTier2Enc ℓ ((w, P) :: hw) := by
  dsimp only [recordHonestWireTier2E, Expr.eval]
  rw [hhw, eval_spkWireKeyE, hwE, hpB]
  dsimp only [honestWiresTier2Enc, honestWiresSubTbl, List.length_cons]
  rcases hk : spkWireKeyVal ℓ w with _ | k
  · cases P <;> simp [partyToBool, Expr.eval, Expr.v0, Env.get]
  · cases P
    · dsimp only [partyToBool, pGet, pSet, tblInsertFirst, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get]
      rcases hsubA : honestWiresSubTbl ℓ .A hw k with _ | oldIdx <;> simp [hsubA, Env.get]
    · dsimp only [partyToBool, pGet, pSet, tblInsertFirst, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get]
      rcases hsubB : honestWiresSubTbl ℓ .B hw k with _ | oldIdx <;> simp [hsubB, Env.get]

private theorem findIdx?_append_singleton {α : Type} (p : α → Bool) (xs : List α) (a : α) :
    (xs ++ [a]).findIdx? p =
      match xs.findIdx? p with
      | some j => some j
      | none => if p a then some xs.length else none := by
  induction xs with
  | nil =>
    simp only [List.nil_append, List.findIdx?_nil, List.findIdx?_cons, List.length_nil]
    cases p a <;> simp
  | cons x xs ih =>
    simp only [List.cons_append, List.findIdx?_cons, List.length_cons]
    cases hx : p x
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
      cases xs.findIdx? p <;> cases p a <;> simp
    · simp

private theorem honestWiresSubTbl_eq_findIdx {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6)
    (P : Party) (hw : List (Bytes × Party))
    (hlen : ∀ wp ∈ hw, wp.1.length ≤ spkMaxWireLen ℓ)
    (w : Bytes) (k : ℕ) (hk : spkWireKeyVal ℓ w = some k) :
    honestWiresSubTbl ℓ P hw k =
      hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == P) := by
  induction hw with
  | nil => simp [honestWiresSubTbl]
  | cons wp rest ih =>
    rcases wp with ⟨w0, P0⟩
    have hw0_len : w0.length ≤ spkMaxWireLen ℓ := hlen (w0, P0) List.mem_cons_self
    have hrest_len : ∀ wp ∈ rest, wp.1.length ≤ spkMaxWireLen ℓ :=
      fun wp hm => hlen wp (List.mem_cons_of_mem _ hm)
    have ih_k := ih hrest_len
    simp only [honestWiresSubTbl, List.reverse_cons, findIdx?_append_singleton, List.length_reverse]
    have hk0 : spkWireKeyVal ℓ w0 =
        some (w0.length + 2 ^ 64 * SpkTier2Keys.packChunks w0 (spkWireChunks ℓ) 0) :=
      wireKeyVal_eq_some_of_le hw0_len
    rw [hk0]
    by_cases hP : P0 = P
    · subst hP
      simp only [↓reduceIte, BEq.rfl, Bool.and_true]
      set k0 := w0.length + 2 ^ 64 * SpkTier2Keys.packChunks w0 (spkWireChunks ℓ) 0
      unfold tblInsertFirst
      by_cases hkk : k = k0
      · have hww : w0 = w := spkWireKeyVal_injective hℓ hk0 (hkk ▸ hk)
        subst hww
        cases hsub0 : honestWiresSubTbl ℓ P0 rest k0 <;>
          cases hfind : rest.reverse.findIdx? (fun wp => wp.1 == w0 && wp.2 == P0) <;>
          simp_all
      · have hne : (w0 == w) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro hEq; subst hEq
          rw [hk0] at hk
          exact hkk (Option.some.inj hk).symm
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        cases hsub0 : honestWiresSubTbl ℓ P0 rest k0 <;>
          cases hfind : rest.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == P0) <;>
          simp [hkk] at ih_k ⊢ <;> simp_all
    · have hneP : (P0 == P) = false := beq_eq_false_iff_ne.mpr hP
      simp only [hP, ↓reduceIte, hneP, Bool.and_false, Bool.false_eq_true, ih_k]
      cases rest.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == P) <;> rfl

theorem findRevHonestWireIdxTier2E_eval {Γ : List (Ty ASig)} (hℓ : ℓ < 10 ^ 6)
    (hw2E : Expr AOps Γ (honestWiresTier2T ℓ Pt))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (ρ : Env Γ)
    (hw : List (Bytes × Party)) (Q : Party) (w : Bytes)
    (hhw : hw2E.eval ρ = honestWiresTier2Enc ℓ hw)
    (hqB : qBE.eval ρ = partyToBool Q) (hwE : wE.eval ρ = w)
    (hlen : ∀ wp ∈ hw, wp.1.length ≤ spkMaxWireLen ℓ) :
    (findRevHonestWireIdxTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hw2E qBE wE).eval ρ =
      hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) := by
  dsimp only [findRevHonestWireIdxTier2E, Expr.eval]
  rw [hhw, hqB, eval_spkWireKeyE, hwE]
  by_cases hw_le : w.length ≤ spkMaxWireLen ℓ
  · have hk : spkWireKeyVal ℓ w =
        some (w.length + 2 ^ 64 * SpkTier2Keys.packChunks w (spkWireChunks ℓ) 0) :=
      wireKeyVal_eq_some_of_le hw_le
    rw [hk]
    have htbl := honestWiresSubTbl_eq_findIdx hℓ Q.other hw hlen w _ hk
    cases Q <;> simpa [honestWiresTier2Enc, partyToBool, Party.other, pGet,
      Expr.eval, Expr.v0, Expr.v1, Env.get] using htbl
  · have hgt : spkMaxWireLen ℓ < w.length := by omega
    have hk : spkWireKeyVal ℓ w = none := wireKeyVal_eq_none_of_gt hgt
    rw [hk]
    symm
    refine List.findIdx?_eq_none_iff.mpr fun wp hmem => ?_
    have hwp_len : wp.1.length ≤ spkMaxWireLen ℓ := hlen wp (List.mem_reverse.mp hmem)
    have hne : wp.1 ≠ w := fun hEq => by rw [hEq] at hwp_len; omega
    simp [beq_eq_false_iff_ne.mpr hne]

theorem stepKemFailDeliverTier2E_eval {Γ : List (Ty ASig)}
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (jE : Expr AOps Γ .nat) (ρ : Env Γ)
    (tr : SimKemFailTrack C.F) (Q : Party) (j : ℕ)
    (htr : tr2E.eval ρ = kemTrackTier2Enc tr) (hqB : qBE.eval ρ = partyToBool Q)
    (hj : jE.eval ρ = j) (hInv : KemTrackTier2Inv C.F K tr) :
    (stepKemFailDeliverTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) tr2E qBE jE).eval ρ =
      kemTrackTier2Enc (simStepKemFailDeliver C.F K tr Q j) := by
  dsimp only [stepKemFailDeliverTier2E, Expr.eval]
  rw [htr, hqB, hj]
  set p0 : (Ty.prod (kemTrackTier2T ℓ Pt) (Ty.prod .bool .nat)).denote :=
    (kemTrackTier2Enc tr, (partyToBool Q, j))
  simp only [p0, kemTrackTier2Enc, Expr.eval, Expr.v0, Env.get]
  cases hj_get : tr.sentB[j]? with
  | none =>
    simp [simStepKemFailDeliver, hj_get]
  | some mc =>
    rcases mc with ⟨m, ctr⟩
    dsimp only [Option.map]
    set entryD : (kemSentEntryT ℓ Pt).denote := ((m.epoch, spqrMsgPayloadSuffix m), ctr)
    set ρ1 : Env (kemSentEntryT ℓ Pt :: .prod (kemTrackTier2T ℓ Pt) (.prod .bool .nat) :: Γ) :=
      .cons entryD (.cons p0 ρ)
    set tr1 : SimKemFailTrack C.F := { tr with sentB := [(m, ctr)] }
    have hTmp : (trMk (trE_e (.fst (.fst .v1))) (trE_c (.fst (.fst .v1))) (trE_st (.fst (.fst .v1)))
        (.cons .v0 .nil) (trE_sendCtr (.fst (.fst .v1))) (trE_cand (.fst (.fst .v1))) :
        Expr AOps _ (kemTrackT ℓ Pt)).eval ρ1 = kemTrackAtomicEnc tr1 := by
      simp [ρ1, entryD, p0, tr1, kemTrackTier2Enc, kemTrackAtomicEnc,
        trMk, trE_e, trE_c, trE_st, trE_sendCtr, trE_cand, Expr.eval, Expr.v0, Expr.v1, Env.get]
    have hInv1 : KemTrackDeliverInv C.F K 1 tr1 :=
      ⟨by simp [tr1], hInv.bOk, fun x hx => by
        simp only [tr1, List.mem_singleton] at hx
        subst hx
        exact hInv.sentB_deser (m, ctr) (List.mem_of_getElem? hj_get)⟩
    have hDel1 := stepKemFailDeliverE_eval sEmb 1 _ (.fst (.snd .v1)) (.nat 0) ρ1 tr1 Q 0
      hTmp (by simp [ρ1, p0, Expr.eval, Expr.v1, Env.get]) rfl hInv1
    have hSimEq : { simStepKemFailDeliver C.F K tr1 Q 0 with sentB := [] } =
        { simStepKemFailDeliver C.F K tr Q j with sentB := [] } := by
      unfold simStepKemFailDeliver
      simp only [tr1, hj_get, List.getElem?_cons_zero]
      cases (tr.st Q).recv K m with
      | error _ => rfl
      | ok out =>
        dsimp only
        split_ifs <;> (try cases tr.c) <;> rfl
    have hSentEq : (simStepKemFailDeliver C.F K tr Q j).sentB = tr.sentB := by
      unfold simStepKemFailDeliver
      simp only [hj_get]
      cases (tr.st Q).recv K m with
      | error _ => rfl
      | ok out =>
        dsimp only
        split_ifs <;> (try cases tr.c) <;> rfl
    refine Prod.ext ?_ ?_
    · change (resetSentBNilE _).eval ρ1 =
          kemTrackAtomicEnc { simStepKemFailDeliver C.F K tr Q j with sentB := [] }
      dsimp only [resetSentBNilE, Expr.eval]
      dsimp only [Expr.v0] at hDel1
      rw [hDel1, ← hSimEq]
      simp [trMk, trE_e, trE_c, trE_st, trE_sendCtr, trE_cand,
        kemTrackAtomicEnc, Expr.eval, Expr.v0, Env.get]
    · simp [hSentEq, Expr.eval, Expr.v1, Env.get]

theorem kemOnDeliverPostTier2E_eval {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (tr2E : Expr AOps Γ (kemTrackTier2T ℓ Pt)) (ρ : Env Γ)
    (Q : Party) (j? : Option ℕ) (rr? : Option (RecvResult (Plain ℓ)))
    (tr : SimKemFailTrack C.F)
    (hq : qBE.eval ρ = partyToBool Q) (hj : jOptE.eval ρ = j?)
    (hrr : rrOptE.eval ρ = rr?.map recvResultEnc)
    (htr : tr2E.eval ρ = kemTrackTier2Enc tr)
    (hInv : KemTrackTier2Inv C.F K tr) :
    (kemOnDeliverPostTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) qBE jOptE rrOptE tr2E).eval ρ =
      kemTrackTier2Enc
        (match rr?, j? with
         | some (.accepted _ _ _), some j => simStepKemFailDeliver C.F K tr Q j
         | _, _ => tr) := by
  dsimp only [kemOnDeliverPostTier2E, Expr.eval]
  rw [hq, hj, hrr, htr]
  rcases rr? with _ | rr
  · rfl
  · cases rr with
    | rejected => rfl
    | accepted t i m =>
      rcases j? with _ | j
      · rfl
      · dsimp only [Option.map, recvResultEnc, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Env.get]
        exact stepKemFailDeliverTier2E_eval (.snd (.snd (.snd .v3))) (.fst .v3) .v0 _
          tr Q j rfl rfl rfl hInv

theorem stepKemSessionDeliverOptTier2E_eval {Γ : List (Ty ASig)}
    (st2E : Expr AOps Γ (kemSessionTrackTier2T ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (jOptE : Expr AOps Γ (.opt .nat)) (ρ : Env Γ)
    (st : SimKemSessionTrack C.F Bytes) (Q : Party) (j? : Option ℕ)
    (hst : st2E.eval ρ = kemSessionTrackTier2Enc ℓ st)
    (hq : qBE.eval ρ = partyToBool Q) (hj : jOptE.eval ρ = j?)
    (hInv : KemTrackTier2Inv C.F K st.1) :
    (stepKemSessionDeliverOptTier2E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) st2E qBE jOptE).eval ρ =
      kemSessionTrackTier2Enc ℓ
        (match j? with | none => st | some j => (simStepKemFailDeliver C.F K st.1 Q j, st.2)) := by
  dsimp only [stepKemSessionDeliverOptTier2E, Expr.eval]
  rw [hst, hq, hj]
  rcases j? with _ | j
  · rfl
  · dsimp only [Env.get, kemSessionTrackTier2Enc]
    exact Prod.ext
      (stepKemFailDeliverTier2E_eval (.fst (.fst .v1)) (.fst (.snd .v1)) .v0 _ st.1 Q j rfl rfl rfl hInv)
      rfl

end DslOps

end Computational.Proofs.Game.PromotedCostedReds.KemFailTrackTier2
