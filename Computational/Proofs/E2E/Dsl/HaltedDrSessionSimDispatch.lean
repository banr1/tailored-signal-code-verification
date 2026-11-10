/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.LocalSessionStep -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import

/-!
# Pure Driver Wrapper and Receive-Tail Oracle Bridge for `HaltedDrSessionSim`

Defines the pure `e2eOps` pre-step guard/filter (`prepLocalSmE2EE`) and post-step state/metadata
update (`finishLocalSmE2EE`), shared atomic step codecs, and the receive-tail bridge between
`oracleImplRSessionTracked` and `oracleImplRTrackHalted`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ops Ty Var Env Expr atomicSig
  B PlainT recvResultEnc bits partyToBool)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (RecvResult GameState ConfigR deliverR injectR)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes BHE2EDrvState BHModelInst BHE2ESmResp SampledSessionKey
  ModelDriverInstanceMeta bhE2EDrvInstClean bhE2EInstIkACorr bhIsBobRecvSMQuery
  bhIsBobAcceptSMResp bhPackSmResp deliverRM injectRM liftStateT)
open CryptoVerification.E2E.Costed (E2EPureOp e2eSig e2eOps GhostStT smQT smQenc smRT)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (KemFailSessionTrack initKemFailSessionTrack stepKemFailSend stepKemFailDeliver
   deliverRTrackHalted oracleImplRTrackHalted)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (liftTy liftVal liftVal_heq)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore
  (SessionHaltTracker oracleImplRSessionTracked deliverRSessionTracked smSchemeTrackState
   bhFilterSmQuery)
open Computational.Proofs.E2E.Dsl.M2Interfaces (e2eGsTy e2eGsEnc smQdec_smQenc)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eDrvStateTy e2eDrvStateEnc e2eModelInstTy
  e2eModelInstEnc e2eInstMetaTy e2eInstMetaEnc e2eInstMetaDec_e2eInstMetaEnc
  packSmRespEnc DrvMetaAligned respNotRevealedE smRenc_id_eq_packSmRespEnc)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp sidOfV_sidV hdrOfV_hdrV)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v eLet eCaseOpt eCaseSum eAny isSomeE orE
  isNoneE optEqByE hdrIkA hdrEkA hdrSpkId hdrOpkId hdrPqId hdrKemCt env_get_zero env_get_succ)
open Computational.Proofs.E2E.Dsl.LocalSessionStepAux (emptySmRespE eval_emptySmRespE
  cost_emptySmRespE listGetOptE eval_listGetOptE cost_listGetOptE listSetE eval_listSetE
  cost_listSetE initPrinOptE initRegIdE hdrEqE
  isBobRecvSmQueryE eval_isBobRecvSmQueryVal cost_isBobRecvSmQueryE
  isBobAcceptSmRespE eval_isBobAcceptSmRespE cost_isBobAcceptSmRespE
  setInstMetaAcceptE eval_setInstMetaAcceptVal cost_setInstMetaAcceptE
  filterLocalSmQueryE eval_filterLocalSmQueryVal cost_filterLocalSmQueryE
  bhFilterLocalSmQuery_eq_bhFilterSmQuery)
open Computational.Proofs.E2E.Dsl.LocalSessionStep (corrTblOfListE instIkACorrTblE
  instIkACorrListE eval_instIkACorrListE cost_instIkACorrListE
  drvInstCleanDrvStateE eval_drvInstCleanDrvStateE cost_drvInstCleanDrvStateE)

/-! ## Shared atomic state types and `SessionHaltTracker` -/

@[expose, reducible] def drvTy (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  liftTy (e2eDrvStateTy S ℓ)

theorem drvTy_denote_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    (drvTy S ℓ Pt).denote = (e2eDrvStateTy S ℓ).denote :=
  rfl

@[expose, reducible] def drvEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (σ : BHE2EDrvState S ℓ) : (drvTy S ℓ Pt).denote :=
  e2eDrvStateEnc σ

theorem liftVal_e2eDrvStateEnc_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (σ : BHE2EDrvState S ℓ) :
    liftVal (Pt := Pt) (e2eDrvStateEnc σ) = drvEnc σ :=
  eq_of_heq (liftVal_heq (e2eDrvStateEnc σ))

/-- `SessionHaltTracker` instantiating `MainHaltedPrefixCore` with `KemFailSessionTrack C.F Bytes`. -/
@[expose] def kemFailSessionTracker {ℓ : ℕ} (C : Crypto) (K : MlKem) :
    SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes
      SampledSessionKey (KemFailSessionTrack C.F Bytes) where
  init k := initKemFailSessionTrack C.F Bytes k.2.2
  onSend _ P coins st :=
    let tr' := stepKemFailSend C.F K st.1 P coins
    (tr'.cand.isSome,
     ({ st.1 with cand := tr'.cand }, st.2),
     fun ct => (tr', (ct, P) :: st.2))
  onDeliver _ Q w res st :=
    let j? := st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
    match res, j? with
    | some (.accepted _ _ _), some j => (stepKemFailDeliver C.F K st.1 Q j, st.2)
    | _, _ => st

@[simp] theorem kemFailSessionTracker_init {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (k : SampledSessionKey) :
    (kemFailSessionTracker (ℓ := ℓ) C K).init k = initKemFailSessionTrack C.F Bytes k.2.2 :=
  rfl

/-! ## Pure `e2eOps` driver preparation and post-step update -/

section PureDriverWrapper

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

@[expose, reducible] def prepLocalSmCtxTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eModelInstTy S ℓ) (.prod (e2eInstMetaTy S ℓ) .bool)

@[expose, reducible] def prepLocalSmInTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eDrvStateTy S ℓ) (.prod .nat smQT)

@[expose, reducible] def prepLocalSmOutTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .sum (.prod (smRT GhostStT) (e2eDrvStateTy S ℓ))
       (.prod (e2eGsTy ℓ) (.prod smQT (prepLocalSmCtxTy S ℓ)))

@[expose, reducible] def finishLocalSmInTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eDrvStateTy S ℓ)
    (.prod .nat (.prod (prepLocalSmCtxTy S ℓ) (.prod smQT (.prod (smRT GhostStT) (e2eGsTy ℓ)))))

/-- Pre-step guard, instance lookup, early Bob-receive corruption update, and wire filter for `bhE2EStepLocalSmSessionTracked`. -/
@[expose] def prepLocalSmE2EE (qStart nCorr nPrins : ℕ) :
    Expr (e2eOps ℓ P C K decT encT) [prepLocalSmInTy S ℓ] (prepLocalSmOutTy S ℓ) :=
  let s0 : Expr (e2eOps ℓ P C K decT encT) [prepLocalSmInTy S ℓ] (e2eDrvStateTy S ℓ) := .fst .v0
  let ix0 : Expr (e2eOps ℓ P C K decT encT) [prepLocalSmInTy S ℓ] .nat := .fst (.snd .v0)
  let adv0 := Expr.fst (.snd (.snd s0))
  let insts0 := Expr.fst (.snd (.snd (.snd s0)))
  let metas0 := Expr.fst (.snd (.snd (.snd (.snd s0))))
  let early0 : Expr (e2eOps ℓ P C K decT encT) [prepLocalSmInTy S ℓ] (prepLocalSmOutTy S ℓ) :=
    .inl (.pair emptySmRespE s0)
  .ite (.not (drvInstCleanDrvStateE qStart nCorr adv0 insts0 metas0 ix0))
    early0
    (.caseOpt (listGetOptE qStart insts0 ix0)
      early0
      (let s1 : Expr (e2eOps ℓ P C K decT encT)
           [e2eModelInstTy S ℓ, prepLocalSmInTy S ℓ] (e2eDrvStateTy S ℓ) := .fst .v1
       let ix1 : Expr (e2eOps ℓ P C K decT encT)
           [e2eModelInstTy S ℓ, prepLocalSmInTy S ℓ] .nat := .fst (.snd .v1)
       let metas1 := Expr.fst (.snd (.snd (.snd (.snd s1))))
       let early1 : Expr (e2eOps ℓ P C K decT encT)
           [e2eModelInstTy S ℓ, prepLocalSmInTy S ℓ] (prepLocalSmOutTy S ℓ) :=
         .inl (.pair emptySmRespE s1)
       .caseOpt (listGetOptE qStart metas1 ix1)
         early1
         (let s2 : Expr (e2eOps ℓ P C K decT encT)
              [e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, prepLocalSmInTy S ℓ] (e2eDrvStateTy S ℓ) :=
            .fst .v2
          let base2 := Expr.fst s2
          let cp2 := Expr.fst (.snd s2)
          .letE (instIkACorrListE nCorr nPrins (.fst .v1) (.fst (.fst (.snd .v1)))
              cp2 (.fst base2))
            (let s3 : Expr (e2eOps ℓ P C K decT encT)
                 [.bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, prepLocalSmInTy S ℓ]
                 (e2eDrvStateTy S ℓ) := .fst .v3
             let ix3 := Expr.fst (.snd .v3)
             let q3 := Expr.snd (.snd .v3)
             let base3 := Expr.fst s3
             let cp3 := Expr.fst (.snd s3)
             let adv3 := Expr.fst (.snd (.snd s3))
             let insts3 := Expr.fst (.snd (.snd (.snd s3)))
             let metas3 := Expr.fst (.snd (.snd (.snd (.snd s3))))
             let tail3 := Expr.snd (.snd (.snd (.snd (.snd s3))))
             let early3 : Expr (e2eOps ℓ P C K decT encT) _ (prepLocalSmOutTy S ℓ) :=
               .inl (.pair emptySmRespE s3)
             .ite (.and (.not (.fst .v1)) (.and (isBobRecvSmQueryE q3) .v0))
               (.inl (.pair emptySmRespE
                 (.pair base3 (.pair cp3 (.pair adv3 (.pair insts3
                   (.pair (listSetE qStart metas3 ix3 (setInstMetaAcceptE .v1 (.bool true)))
                     tail3)))))))
               (.caseOpt (.snd (.snd (.snd (.snd (.snd .v2)))))
                 early3
                 (let s4 : Expr (e2eOps ℓ P C K decT encT)
                      [e2eGsTy ℓ, .bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, prepLocalSmInTy S ℓ]
                      (e2eDrvStateTy S ℓ) := .fst .v4
                  let q4 := Expr.snd (.snd .v4)
                  let early4 : Expr (e2eOps ℓ P C K decT encT) _ (prepLocalSmOutTy S ℓ) :=
                    .inl (.pair emptySmRespE s4)
                  .caseOpt (filterLocalSmQueryE (.fst .v2) (.fst .v3) (.fst (.snd .v3)) q4)
                    early4
                    (.inr (.pair .v1 (.pair .v0 (.pair .v4 (.pair .v3 .v2)))))))))))

/-- Post-step metadata and session-list update for `bhE2EStepLocalSmSessionTracked`. -/
@[expose] def finishLocalSmE2EE (qStart : ℕ) :
    Expr (e2eOps ℓ P C K decT encT) [finishLocalSmInTy S ℓ] (e2eDrvStateTy S ℓ) :=
  let in0 : Expr (e2eOps ℓ P C K decT encT) [finishLocalSmInTy S ℓ] (finishLocalSmInTy S ℓ) := .v0
  let ctx0 := Expr.fst (.snd (.snd in0))
  let qf0 := Expr.fst (.snd (.snd (.snd in0)))
  let resp0 := Expr.fst (.snd (.snd (.snd (.snd in0))))
  let im0 := Expr.fst (.snd ctx0)
  let ikc0 := Expr.snd (.snd ctx0)
  .letE (.ite (.and (.not (.fst im0)) (isBobAcceptSmRespE qf0 resp0))
      (setInstMetaAcceptE im0 ikc0) im0)
    (let in1 : Expr (e2eOps ℓ P C K decT encT)
         [e2eInstMetaTy S ℓ, finishLocalSmInTy S ℓ] (finishLocalSmInTy S ℓ) := .v1
     let s1 := Expr.fst in1
     let ix1 := Expr.fst (.snd in1)
     let ctx1 := Expr.fst (.snd (.snd in1))
     let gs'1 := Expr.snd (.snd (.snd (.snd (.snd in1))))
     let d1 := Expr.fst ctx1
     let base1 := Expr.fst s1
     let cp1 := Expr.fst (.snd s1)
     let adv1 := Expr.fst (.snd (.snd s1))
     let insts1 := Expr.fst (.snd (.snd (.snd s1)))
     let metas1 := Expr.fst (.snd (.snd (.snd (.snd s1))))
     let tail1 := Expr.snd (.snd (.snd (.snd (.snd s1))))
     let dEnc' := Expr.pair (.fst d1) (.pair (.fst (.snd d1))
       (.pair (.fst (.snd (.snd d1))) (.pair (.fst (.snd (.snd (.snd d1))))
         (.pair (.fst (.snd (.snd (.snd (.snd d1))))) (.some gs'1)))))
     .pair base1 (.pair cp1 (.pair adv1
       (.pair (listSetE qStart insts1 ix1 dEnc')
         (.pair (listSetE qStart metas1 ix1 .v0) tail1)))))

@[local simp] private theorem size_v {O : Ops (e2eSig ℓ)} {Γ Δ : List (Ty (e2eSig ℓ))} [Ext Γ Δ]
    {τ : Ty (e2eSig ℓ)} (x : Var Γ τ) : (v (O := O) (Δ := Δ) x).size = 1 := by
  simp [v, Expr.size]

@[local simp] private theorem size_eLet {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {τ υ : Ty (e2eSig ℓ)} (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    (eLet e k).size = e.size + (k .zero).size + 1 := rfl

@[local simp] private theorem size_eCaseOpt {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {τ υ : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt τ)) (n : Expr O Γ υ)
    (s : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    (eCaseOpt e n s).size = e.size + n.size + (s .zero).size + 1 := by
  simp only [eCaseOpt, Expr.size]

@[local simp] private theorem size_eCaseSum {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {α β υ : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β))
    (l : Var (α :: Γ) α → Expr O (α :: Γ) υ) (r : Var (β :: Γ) β → Expr O (β :: Γ) υ) :
    (eCaseSum e l r).size = e.size + (l .zero).size + (r .zero).size + 1 := by
  simp only [eCaseSum, Expr.size]

@[local simp] private theorem size_eAny {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {τ : Ty (e2eSig ℓ)} (n : ℕ) (l : Expr O Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr O (τ :: Γ) .bool) :
    (eAny n l p).size = l.size + (p .zero).size + bits n + 1 := by
  simp only [eAny, Expr.size]

@[local simp] private theorem size_pureOp_loc {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + o.opSize + 1 := rfl

@[local simp] private theorem size_var {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {τ : Ty S₀}
    (x : Var Γ τ) : (Expr.var (O := O) x).size = 1 := rfl

private theorem size_orE {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (a b : Expr O Γ .bool) : (orE a b).size = a.size + b.size + 4 := by
  simp only [orE, Expr.size]; omega

private theorem size_isSomeE {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt t)) : (isSomeE e).size = e.size + 3 := by
  simp only [isSomeE, Expr.size]

private theorem size_emptySmRespE {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    (emptySmRespE (O := O) (Γ := Γ)).size = 5 := rfl

private theorem size_listGetOptE {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (k : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) :
    (listGetOptE k lE iE).size ≤ lE.size + iE.size + bits k + 50 := by
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl
  simp only [listGetOptE, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb0, hb1]; omega

private theorem size_listSetE {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {t : Ty (e2eSig ℓ)} (k : ℕ) (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat)
    (valE : Expr O Γ t) :
    (listSetE k lE iE valE).size ≤ lE.size + iE.size + valE.size + bits k + 55 := by
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl
  simp only [listSetE, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb0, hb1]; omega

private theorem size_drvInstCleanDrvStateE {Γ : List (Ty (e2eSig ℓ))} (qStart nCorr : ℕ)
    (revE : Expr (e2eOps ℓ P C K decT encT) Γ _) (instsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (instMetaE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (ixE : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    (drvInstCleanDrvStateE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      qStart nCorr revE instsE instMetaE ixE).size ≤
      revE.size + instsE.size + instMetaE.size + ixE.size + 2 * bits qStart + bits nCorr + 200 := by
  have hb0 : bits 0 = 1 := rfl; have hb1 : bits 1 = 1 := rfl
  unfold drvInstCleanDrvStateE respNotRevealedE
  simp only [listGetOptE, initPrinOptE, size_isSomeE, size_eLet, size_eCaseOpt, size_eCaseSum,
    size_eAny, size_v, size_pureOp_loc, E2EPureOp.opSize, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    hb0, hb1]; omega

private theorem size_instIkACorrListE {Γ : List (Ty (e2eSig ℓ))} (nCorr nPrins : ℕ)
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ _) (ikAPkE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (corrPrinsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (prinsE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (instIkACorrListE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      nCorr nPrins sidE ikAPkE corrPrinsE prinsE).size ≤
      sidE.size + ikAPkE.size + corrPrinsE.size + prinsE.size + bits nCorr + bits nPrins + 95 := by
  unfold instIkACorrListE instIkACorrTblE corrTblOfListE
  simp only [initPrinOptE, size_eLet, size_eCaseOpt, size_eCaseSum, size_eAny, size_v,
    size_pureOp_loc, E2EPureOp.opSize, size_orE, Expr.size, Expr.v0, Expr.v1]; omega

private theorem size_filterLocalSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (bobAccE : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ _) (hdrE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) :
    (filterLocalSmQueryE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      bobAccE sidE hdrE qE).size ≤
      bobAccE.size + sidE.size + hdrE.size + qE.size + 450 := by
  unfold filterLocalSmQueryE
  simp only [initRegIdE, initPrinOptE, hdrEqE, optEqByE, isNoneE,
    hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
    size_eLet, size_eCaseSum, size_eCaseOpt, size_v, size_pureOp_loc, E2EPureOp.opSize, Expr.size]; omega

private theorem size_isBobRecvSmQueryE {Γ : List (Ty (e2eSig ℓ))}
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) :
    (isBobRecvSmQueryE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qE).size ≤
      qE.size + 30 := by
  simp only [isBobRecvSmQueryE, size_eCaseSum, size_v, Expr.size]; omega

private theorem size_isBobAcceptSmRespE {Γ : List (Ty (e2eSig ℓ))}
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (respE : Expr (e2eOps ℓ P C K decT encT) Γ (smRT GhostStT)) :
    (isBobAcceptSmRespE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qE respE).size ≤
      qE.size + respE.size + 50 := by
  simp only [isBobAcceptSmRespE, isBobRecvSmQueryE, size_eLet, size_eCaseSum, size_eCaseOpt,
    size_v, Expr.size]; omega

private theorem size_setInstMetaAcceptE {Γ : List (Ty (e2eSig ℓ))}
    (imE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (ikACorrE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (setInstMetaAcceptE (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) imE ikACorrE).size ≤ imE.size + ikACorrE.size + 15 := by
  simp only [setInstMetaAcceptE, Expr.size]; omega

attribute [local irreducible] emptySmRespE listGetOptE listSetE drvInstCleanDrvStateE
  instIkACorrListE isBobRecvSmQueryE isBobAcceptSmRespE setInstMetaAcceptE filterLocalSmQueryE

theorem prepLocalSmE2EE_size (qStart nCorr nPrins : ℕ) :
    (prepLocalSmE2EE (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart nCorr nPrins).size ≤
      5 * bits qStart + 2 * bits nCorr + bits nPrins + 1150 := by
  let InTy := prepLocalSmInTy S ℓ
  let s0 : Expr (e2eOps ℓ P C K decT encT) [InTy] (e2eDrvStateTy S ℓ) := .fst .v0
  let ix0 : Expr (e2eOps ℓ P C K decT encT) [InTy] .nat := .fst (.snd .v0)
  let s1 : Expr (e2eOps ℓ P C K decT encT) [e2eModelInstTy S ℓ, InTy] (e2eDrvStateTy S ℓ) :=
    .fst .v1
  let ix1 : Expr (e2eOps ℓ P C K decT encT) [e2eModelInstTy S ℓ, InTy] .nat := .fst (.snd .v1)
  let s2 : Expr (e2eOps ℓ P C K decT encT)
      [e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy] (e2eDrvStateTy S ℓ) := .fst .v2
  let s3 : Expr (e2eOps ℓ P C K decT encT)
      [.bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy] (e2eDrvStateTy S ℓ) := .fst .v3
  let s4 : Expr (e2eOps ℓ P C K decT encT)
      [e2eGsTy ℓ, .bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy] (e2eDrvStateTy S ℓ) :=
    .fst .v4
  have hcl := size_drvInstCleanDrvStateE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nCorr
    (.fst (.snd (.snd s0))) (.fst (.snd (.snd (.snd s0))))
    (.fst (.snd (.snd (.snd (.snd s0))))) ix0
  have hg1 := size_listGetOptE qStart (.fst (.snd (.snd (.snd s0)))) ix0
  have hg2 := size_listGetOptE qStart (.fst (.snd (.snd (.snd (.snd s1))))) ix1
  have hik := size_instIkACorrListE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr nPrins
    (Γ := [e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy])
    (.fst .v1) (.fst (.fst (.snd .v1))) (.fst (.snd s2)) (.fst (.fst s2))
  have hbr := size_isBobRecvSmQueryE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [.bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy]) (.snd (.snd .v3))
  have hsm := size_setInstMetaAcceptE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [.bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy]) .v1 (.bool true)
  have hls := size_listSetE qStart (.fst (.snd (.snd (.snd (.snd s3))))) (.fst (.snd .v3))
    (setInstMetaAcceptE .v1 (.bool true))
  have hfl := size_filterLocalSmQueryE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [e2eGsTy ℓ, .bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy])
    (.fst .v2) (.fst .v3) (.fst (.snd .v3)) (.snd (.snd .v4))
  unfold prepLocalSmE2EE
  dsimp only [InTy, s0, ix0, s1, ix1, s2, s3, s4] at hcl hg1 hg2 hik hbr hsm hls hfl ⊢
  simp only [Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, size_var,
    size_emptySmRespE] at hcl hg1 hg2 hik hbr hsm hls hfl ⊢
  omega

theorem finishLocalSmE2EE_size (qStart : ℕ) :
    (finishLocalSmE2EE (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart).size ≤
      2 * bits qStart + 330 := by
  let InTy := finishLocalSmInTy S ℓ
  let in0 : Expr (e2eOps ℓ P C K decT encT) [InTy] InTy := .v0
  let ctx0 := Expr.fst (.snd (.snd in0))
  let in1 : Expr (e2eOps ℓ P C K decT encT) [e2eInstMetaTy S ℓ, InTy] InTy := .v1
  let s1 := Expr.fst in1
  let d1 := Expr.fst (.fst (.snd (.snd in1)))
  let gs'1 := Expr.snd (.snd (.snd (.snd (.snd in1))))
  let dEnc' := Expr.pair (.fst d1) (.pair (.fst (.snd d1))
    (.pair (.fst (.snd (.snd d1))) (.pair (.fst (.snd (.snd (.snd d1))))
      (.pair (.fst (.snd (.snd (.snd (.snd d1))))) (.some gs'1)))))
  have hiba := size_isBobAcceptSmRespE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (.fst (.snd (.snd (.snd in0)))) (.fst (.snd (.snd (.snd (.snd in0)))))
  have hsm := size_setInstMetaAcceptE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (.fst (.snd ctx0)) (.snd (.snd ctx0))
  have hls1 := size_listSetE qStart (.fst (.snd (.snd (.snd s1)))) (.fst (.snd in1)) dEnc'
  have hls2 := size_listSetE qStart (.fst (.snd (.snd (.snd (.snd s1))))) (.fst (.snd in1)) .v0
  unfold finishLocalSmE2EE
  dsimp only [InTy, in0, ctx0, in1, s1, d1, gs'1, dEnc'] at hiba hsm hls1 hls2 ⊢
  simp only [Expr.size, Expr.v0, Expr.v1, size_var] at hiba hsm hls1 hls2 ⊢
  omega

theorem prepLocalSmE2EE_cost (qStart nCorr nPrins : ℕ) :
    (prepLocalSmE2EE (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart nCorr nPrins).cost ≤
      150 * qStart + 160 * nCorr + 160 * nPrins + 8500 := by
  let InTy := prepLocalSmInTy S ℓ
  let s0 : Expr (e2eOps ℓ P C K decT encT) [InTy] (e2eDrvStateTy S ℓ) := .fst .v0
  let ix0 : Expr (e2eOps ℓ P C K decT encT) [InTy] .nat := .fst (.snd .v0)
  let s1 : Expr (e2eOps ℓ P C K decT encT) [e2eModelInstTy S ℓ, InTy] (e2eDrvStateTy S ℓ) :=
    .fst .v1
  let ix1 : Expr (e2eOps ℓ P C K decT encT) [e2eModelInstTy S ℓ, InTy] .nat := .fst (.snd .v1)
  let s2 : Expr (e2eOps ℓ P C K decT encT)
      [e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy] (e2eDrvStateTy S ℓ) := .fst .v2
  let s3 : Expr (e2eOps ℓ P C K decT encT)
      [.bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy] (e2eDrvStateTy S ℓ) := .fst .v3
  let s4 : Expr (e2eOps ℓ P C K decT encT)
      [e2eGsTy ℓ, .bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy] (e2eDrvStateTy S ℓ) :=
    .fst .v4
  have hcl := cost_drvInstCleanDrvStateE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nCorr
    (.fst (.snd (.snd s0))) (.fst (.snd (.snd (.snd s0))))
    (.fst (.snd (.snd (.snd (.snd s0))))) ix0
  have hg1 := cost_listGetOptE qStart (.fst (.snd (.snd (.snd s0)))) ix0
  have hg2 := cost_listGetOptE qStart (.fst (.snd (.snd (.snd (.snd s1))))) ix1
  have hik := cost_instIkACorrListE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr nPrins
    (Γ := [e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy])
    (.fst .v1) (.fst (.fst (.snd .v1))) (.fst (.snd s2)) (.fst (.fst s2))
  have hbr := cost_isBobRecvSmQueryE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (Γ := [.bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy]) (.snd (.snd .v3))
  have hsm := cost_setInstMetaAcceptE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [.bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy]) .v1 (.bool true)
  have hls := cost_listSetE qStart (.fst (.snd (.snd (.snd (.snd s3))))) (.fst (.snd .v3))
    (setInstMetaAcceptE .v1 (.bool true))
  have hfl := cost_filterLocalSmQueryE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [e2eGsTy ℓ, .bool, e2eInstMetaTy S ℓ, e2eModelInstTy S ℓ, InTy])
    (.fst .v2) (.fst .v3) (.fst (.snd .v3)) (.snd (.snd .v4))
  unfold prepLocalSmE2EE
  dsimp only [InTy, s0, ix0, s1, ix1, s2, s3, s4] at hcl hg1 hg2 hik hbr hsm hls hfl ⊢
  simp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    cost_emptySmRespE] at hcl hg1 hg2 hik hbr hsm hls hfl ⊢
  omega

theorem finishLocalSmE2EE_cost (qStart : ℕ) :
    (finishLocalSmE2EE (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart).cost ≤
      60 * qStart + 250 := by
  let InTy := finishLocalSmInTy S ℓ
  let in0 : Expr (e2eOps ℓ P C K decT encT) [InTy] InTy := .v0
  let ctx0 := Expr.fst (.snd (.snd in0))
  let in1 : Expr (e2eOps ℓ P C K decT encT) [e2eInstMetaTy S ℓ, InTy] InTy := .v1
  let s1 := Expr.fst in1
  let d1 := Expr.fst (.fst (.snd (.snd in1)))
  let gs'1 := Expr.snd (.snd (.snd (.snd (.snd in1))))
  let dEnc' := Expr.pair (.fst d1) (.pair (.fst (.snd d1))
    (.pair (.fst (.snd (.snd d1))) (.pair (.fst (.snd (.snd (.snd d1))))
      (.pair (.fst (.snd (.snd (.snd (.snd d1))))) (.some gs'1)))))
  have hiba := cost_isBobAcceptSmRespE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (.fst (.snd (.snd (.snd in0)))) (.fst (.snd (.snd (.snd (.snd in0)))))
  have hsm := cost_setInstMetaAcceptE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (.fst (.snd ctx0)) (.snd (.snd ctx0))
  have hls1 := cost_listSetE qStart (.fst (.snd (.snd (.snd s1)))) (.fst (.snd in1)) dEnc'
  have hls2 := cost_listSetE qStart (.fst (.snd (.snd (.snd (.snd s1))))) (.fst (.snd in1)) .v0
  unfold finishLocalSmE2EE
  dsimp only [InTy, in0, ctx0, in1, s1, d1, gs'1, dEnc'] at hiba hsm hls1 hls2 ⊢
  simp only [Expr.cost, Expr.v0, Expr.v1] at hiba hsm hls1 hls2 ⊢
  omega

private theorem map_set_eq {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : ℕ) (x : α), (l.map f).set i (f x) = (l.set i x).map f
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: as, i + 1, x => congrArg (f a :: ·) (map_set_eq f as i x)

theorem prepLocalSmE2EE_eval (qStart nCorr nPrins : ℕ)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (hInstLen : σ.insts.length ≤ qStart) (hMeta : DrvMetaAligned σ)
    (hCorrLen : σ.corrPrins.length ≤ nCorr) (hRevLen : σ.revealedSpks.length ≤ nCorr)
    (hPrinLen : σ.prins.length ≤ nPrins) :
    (prepLocalSmE2EE (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart nCorr nPrins).eval
      (.cons (e2eDrvStateEnc σ, (i, smQenc sq)) .nil) =
    if !bhE2EDrvInstClean σ i then
      .inl (packSmRespEnc (none, none, none), e2eDrvStateEnc σ)
    else
      match σ.insts[i]?, σ.instMeta[i]? with
      | some d, some im =>
        if !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d then
          let im' := { im with bobAccepted := true, ikACorrAtAccept := true }
          .inl (packSmRespEnc (none, none, none),
                e2eDrvStateEnc { σ with instMeta := σ.instMeta.set i im' })
        else
          match d.gs, bhFilterSmQuery d im sq with
          | some gs, some q' =>
            .inr (e2eGsEnc gs,
                  (smQenc q', (e2eModelInstEnc d, (e2eInstMetaEnc im, bhE2EInstIkACorr σ d))))
          | _, _ =>
            .inl (packSmRespEnc (none, none, none), e2eDrvStateEnc σ)
      | _, _ =>
        .inl (packSmRespEnc (none, none, none), e2eDrvStateEnc σ) := by
  have hMetaLen : σ.instMeta.length ≤ qStart := hMeta.trans_le hInstLen
  have hInstMapLen : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by simp [hInstLen]
  have hMetaMapLen : (σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by simp [hMetaLen]
  let ρ0 : Env [prepLocalSmInTy S ℓ] := .cons (e2eDrvStateEnc σ, (i, smQenc sq)) .nil
  let s0 : Expr (e2eOps ℓ P C K decT encT) [prepLocalSmInTy S ℓ] (e2eDrvStateTy S ℓ) := .fst .v0
  have hclEval :
      (drvInstCleanDrvStateE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        qStart nCorr (.fst (.snd (.snd s0))) (.fst (.snd (.snd (.snd s0))))
        (.fst (.snd (.snd (.snd (.snd s0))))) (.fst (.snd .v0))).eval ρ0 =
      bhE2EDrvInstClean σ i :=
    eval_drvInstCleanDrvStateE qStart nCorr σ i hInstLen hMetaLen hRevLen rfl rfl rfl rfl
  unfold prepLocalSmE2EE
  dsimp only [s0, ρ0, Expr.v0] at hclEval
  dsimp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, env_get_zero, env_get_succ]
  simp only [hclEval]
  by_cases hcl : (!bhE2EDrvInstClean σ i) = true
  · simp [hcl, eval_emptySmRespE, e2eDrvStateEnc]
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
    rw [eval_listGetOptE qStart _ _ _ (by exact hInstMapLen)]
    dsimp only [e2eDrvStateEnc, Expr.eval, env_get_zero, env_get_succ]
    rw [List.getElem?_map]
    cases hd : σ.insts[i]? with
    | none => simp [eval_emptySmRespE]
    | some d =>
      dsimp only [Option.map]
      rw [eval_listGetOptE qStart _ _ _ (by exact hMetaMapLen)]
      dsimp only [e2eDrvStateEnc, Expr.eval, env_get_zero, env_get_succ]
      rw [List.getElem?_map]
      cases him : σ.instMeta[i]? with
      | none => simp [eval_emptySmRespE]
      | some im =>
        dsimp only [Option.map]
        have hikEval :=
          eval_instIkACorrListE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
            nCorr nPrins (Expr.var Var.zero.succ).fst (Expr.var Var.zero.succ).snd.fst.fst
            (Expr.var Var.zero.succ.succ).fst.snd.fst (Expr.var Var.zero.succ.succ).fst.fst.fst
            (.cons (e2eInstMetaEnc im) (.cons (e2eModelInstEnc d) ρ0))
            σ d rfl rfl rfl rfl hCorrLen hPrinLen
        dsimp only [ρ0, e2eDrvStateEnc] at hikEval
        have hb0 : (e2eInstMetaEnc (ℓ := ℓ) im).1 = im.bobAccepted := rfl
        simp only [hikEval, eval_isBobRecvSmQueryVal, Expr.eval, env_get_zero, env_get_succ,
          smQdec_smQenc, hb0, ← Bool.and_assoc]
        by_cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d) = true
        · simp only [hcorr, ↓reduceIte, eval_emptySmRespE]
          rw [eval_listSetE qStart _ _ _ _ (by exact hMetaMapLen)]
          simp only [eval_setInstMetaAcceptVal, e2eInstMetaDec_e2eInstMetaEnc,
            Expr.eval, env_get_zero, env_get_succ]
          rw [map_set_eq (e2eInstMetaEnc (ℓ := ℓ)) σ.instMeta i _]
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
          have hgsProj : (e2eModelInstEnc d).2.2.2.2.2 = d.gs.map e2eGsEnc := rfl
          simp only [hgsProj]
          cases hgs : d.gs with
          | none => simp [eval_emptySmRespE]
          | some gs =>
            have hsidProj : (e2eModelInstEnc d).1 = CryptoVerification.E2E.Costed.sidV d.sid := rfl
            have hhdrProj : (e2eModelInstEnc d).2.1 = CryptoVerification.E2E.Costed.hdrV d.hdr := rfl
            have hfltEq : Computational.Proofs.E2E.Dsl.M3Interfaces.bhFilterSmQuery d im sq =
                bhFilterSmQuery d im sq := rfl
            simp only [Option.map, eval_filterLocalSmQueryVal, Expr.eval, env_get_zero,
              env_get_succ, hb0, hsidProj, hhdrProj, sidOfV_sidV, hdrOfV_hdrV, smQdec_smQenc,
              bhFilterLocalSmQuery_eq_bhFilterSmQuery, hfltEq]
            cases hflt : bhFilterSmQuery d im sq <;> simp only [eval_emptySmRespE]

theorem finishLocalSmE2EE_eval (qStart : ℕ)
    (σ : BHE2EDrvState S ℓ) (i : ℕ) (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (ikACorr : Bool)
    (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range q')
    (gs' : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hInstLen : σ.insts.length ≤ qStart) (hMetaLen : σ.instMeta.length ≤ qStart) :
    (finishLocalSmE2EE (S := S) (ℓ := ℓ) (Pt := Pt) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart).eval
      (.cons (e2eDrvStateEnc σ, (i, ((e2eModelInstEnc d, (e2eInstMetaEnc im, ikACorr)),
        (smQenc q', (packSmRespEnc (bhPackSmResp q' r), e2eGsEnc gs'))))) .nil) =
    let im' := if !im.bobAccepted && bhIsBobAcceptSMResp q' r then
        { im with bobAccepted := true, ikACorrAtAccept := ikACorr }
      else im
    e2eDrvStateEnc { σ with insts := σ.insts.set i { d with gs := some gs' },
                            instMeta := σ.instMeta.set i im' } := by
  have hInstMapLen : (σ.insts.map (e2eModelInstEnc (ℓ := ℓ))).length ≤ qStart := by simp [hInstLen]
  have hMetaMapLen : (σ.instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by simp [hMetaLen]
  let ρ0 : Env [finishLocalSmInTy S ℓ] :=
    .cons (e2eDrvStateEnc σ, (i, ((e2eModelInstEnc d, (e2eInstMetaEnc im, ikACorr)),
      (smQenc q', (packSmRespEnc (bhPackSmResp q' r), e2eGsEnc gs'))))) .nil
  let in0 : Expr (e2eOps ℓ P C K decT encT) [finishLocalSmInTy S ℓ] (finishLocalSmInTy S ℓ) := .v0
  have haccEval :
      (isBobAcceptSmRespE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (.fst (.snd (.snd (.snd in0)))) (.fst (.snd (.snd (.snd (.snd in0)))))).eval ρ0 =
      bhIsBobAcceptSMResp q' r :=
    eval_isBobAcceptSmRespE _ _ ρ0 q' r rfl (smRenc_id_eq_packSmRespEnc q' r).symm
  unfold finishLocalSmE2EE
  dsimp only [in0, ρ0, Expr.v0] at haccEval
  dsimp only [Expr.eval, Expr.v0, Expr.v1, env_get_zero, env_get_succ]
  have hb0 : (e2eInstMetaEnc (ℓ := ℓ) im).1 = im.bobAccepted := rfl
  simp only [haccEval, hb0, eval_setInstMetaAcceptVal, Expr.eval, env_get_zero,
    e2eInstMetaDec_e2eInstMetaEnc]
  rw [eval_listSetE qStart _ _ _ _ (by exact hInstMapLen),
    eval_listSetE qStart _ _ _ _ (by exact hMetaMapLen)]
  dsimp only [e2eDrvStateEnc, Expr.eval, env_get_zero, env_get_succ]
  have hd' : ((e2eModelInstEnc d).1, ((e2eModelInstEnc d).2.1, ((e2eModelInstEnc d).2.2.1,
      ((e2eModelInstEnc d).2.2.2.1, ((e2eModelInstEnc d).2.2.2.2.1, some (e2eGsEnc gs')))))) =
      e2eModelInstEnc { d with gs := some gs' } := rfl
  rw [hd', map_set_eq (e2eModelInstEnc (ℓ := ℓ)) σ.insts i { d with gs := some gs' }]
  by_cases hacc : (!im.bobAccepted && bhIsBobAcceptSMResp q' r) = true
  · simp only [hacc, ↓reduceIte]
    rw [map_set_eq (e2eInstMetaEnc (ℓ := ℓ)) σ.instMeta i _]
  · simp only [hacc, Bool.false_eq_true, ↓reduceIte]
    rw [map_set_eq (e2eInstMetaEnc (ℓ := ℓ)) σ.instMeta i im]

end PureDriverWrapper

/-! ## Atomic step argument and response codecs -/

@[expose, reducible] def gsAtomicTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  liftTy (Pt := Pt) (e2eGsTy ℓ)

@[expose, reducible] def gsAtomicEnc {ℓ : ℕ} {Pt : Type}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) : (gsAtomicTy ℓ Pt).denote :=
  liftVal (Pt := Pt) (e2eGsEnc gs)

@[expose, reducible] def trArgAtomicTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod PlainT (.opt (_root_.ReductionDsl.BV512 (ℓ := ℓ) (Pt := Pt))))

@[expose, reducible] def chArgAtomicTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .bool (.prod PlainT (.prod PlainT (.opt (_root_.ReductionDsl.BV512 (ℓ := ℓ) (Pt := Pt)))))

@[expose, reducible] def smRecvTailTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum (.prod .bool (B (ℓ := ℓ) (Pt := Pt) 32))
    (.sum (.prod .bool (B (ℓ := ℓ) (Pt := Pt) 32)) .bool)

@[expose, reducible] def smRecvTailEnc {ℓ : ℕ} {Pt : Type} :
    (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party) → (smRecvTailTy ℓ Pt).denote
  | .inl (Q, w) => .inl (partyToBool Q, w)
  | .inr (.inl (Q, w)) => .inr (.inl (partyToBool Q, w))
  | .inr (.inr Q) => .inr (.inr (partyToBool Q))

@[expose, reducible] def smRecvTailToSpec {ℓ : ℕ} {PQC : Type} :
    (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party) →
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain
  | .inl dl => .inl (.inl (.inr dl))
  | .inr (.inl ij) => .inl (.inr ij)
  | .inr (.inr cr) => .inr cr

@[expose, reducible] def atomicSmRT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  _root_.ReductionDsl.smRT (ℓ := ℓ) (Pt := Pt) (_root_.ReductionDsl.GhostStT (ℓ := ℓ) (Pt := Pt))

@[expose, reducible] def atomicSmQT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  _root_.ReductionDsl.smQT (ℓ := ℓ) (Pt := Pt)

@[expose, reducible] def packAtomicSmRespEnc {ℓ : ℕ} {Pt : Type}
    (br : BHE2ESmResp ℓ) : (atomicSmRT ℓ Pt).denote :=
  (br.1, (br.2.1.map recvResultEnc, br.2.2))

theorem liftVal_packSmRespEnc_eq {ℓ : ℕ} {Pt : Type} (br : BHE2ESmResp ℓ) :
    liftVal (Pt := Pt) (packSmRespEnc br) = packAtomicSmRespEnc (Pt := Pt) br := by
  rcases br with ⟨w, rr?, st?⟩
  rcases rr? with _ | rr
  · cases w <;> cases st? <;> rfl
  · rcases rr with _ | ⟨t, i, m?⟩
    · cases w <;> cases st? <;> rfl
    · cases m? <;> cases w <;> cases st? <;> rfl

theorem liftVal_smQenc_eq {ℓ : ℕ} {Pt : Type}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    liftVal (Pt := Pt) (smQenc (ℓ := ℓ) sq) =
      _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) sq := by
  rcases sq with (((⟨_, _, r⟩ | ⟨_, _, _, r⟩) | _) | _) | _
  · cases r <;> rfl
  · cases r <;> rfl
  · rfl
  · rfl
  · rfl

/-! ## Receive-tail oracle bridge -/

section RecvTailOracleBridge

private theorem liftM_state_run {τ α : Type} (p : ProbComp α) (tr : τ) :
    (liftM p : StateT τ ProbComp α).run tr = (p >>= fun a => pure (a, tr)) := by
  show StateT.run (StateT.lift p) tr = _
  simp [StateT.run_lift]

private theorem liftStateT_run_state_loc {σ τ α : Type}
    (m : StateT σ ProbComp α) (s : σ) (tr : τ) :
    ((liftStateT m : StateT σ (StateT τ ProbComp) α).run s).run tr =
      (m.run s >>= fun x => pure (x, tr)) := by
  change (liftM (m.run s) : StateT τ ProbComp (α × σ)).run tr = _
  exact liftM_state_run (m.run s) tr

private theorem rawPure_run {τ α : Type} (f : τ → α × τ) (tr : τ) :
    StateT.run (σ := τ) (m := ProbComp) (fun s => pure (f s)) tr = pure (f tr) := rfl

private theorem deliverRM_smSchemeTrackState_eq {τ Key St Msg Coins RCoins C₀ : Type}
    [DecidableEq Msg] [DecidableEq C₀] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C₀) (cfg : ConfigR St Msg C₀) (q : Party × C₀) :
    deliverRM (smSchemeTrackState (τ := τ) sm) cfg q = liftStateT (deliverR sm cfg q) := by
  rcases q with ⟨P, c⟩
  ext s tr
  rw [liftStateT_run_state_loc]
  unfold deliverRM deliverR smSchemeTrackState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
  cases s.inTransit P.other c with
  | none => simp
  | some r =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, bind_assoc, pure_bind]
    congr 1; funext rc
    cases sm.receive (s.st P) c rc with
    | none => split_ifs <;> simp [StateT.run_map, StateT.run_set, StateT.run_pure]
    | some x =>
      rcases x with ⟨st', t', i', m'⟩
      dsimp only
      split_ifs <;> simp [StateT.run_map, StateT.run_set, StateT.run_pure]

private theorem injectRM_smSchemeTrackState_eq {τ Key St Msg Coins RCoins C₀ : Type}
    [DecidableEq Msg] [DecidableEq C₀] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C₀) (Δ qep : ℕ) (cfg : ConfigR St Msg C₀)
    (q : Party × C₀) :
    injectRM (smSchemeTrackState (τ := τ) sm) Δ qep cfg q =
      liftStateT (injectR sm Δ qep cfg q) := by
  rcases q with ⟨P, c⟩
  ext s tr
  rw [liftStateT_run_state_loc]
  unfold injectRM injectR smSchemeTrackState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind,
      StateT.run_lift, liftM_state_run, bind_assoc]
  congr 1; funext rc
  cases sm.receive (s.st P) c rc with
  | none => simp
  | some x =>
    rcases x with ⟨st', t', i', m'⟩
    dsimp only
    split_ifs <;> simp [StateT.run_map, StateT.run_set, StateT.run_pure]

private theorem deliverRSessionTracked_kemFail_eq {ℓ : ℕ} {RCoins : Type} [SampleableType RCoins]
    (C : Crypto) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes) :
    deliverRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C K) sm cfg =
      deliverRTrackHalted C.F K sm cfg := by
  funext ⟨Q, w⟩
  unfold deliverRSessionTracked deliverRTrackHalted
  dsimp only
  rw [deliverRM_smSchemeTrackState_eq]
  ext s ⟨tr, hw⟩
  unfold kemFailSessionTracker
  simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_pure, rawPure_run,
    liftStateT_run_state_loc, bind_assoc, pure_bind]
  congr 1; funext ⟨res, s'⟩
  cases res with
  | none => simp
  | some rr =>
    cases rr
    · simp
    · have hpred :
          (fun wp : Bytes × Party => @BEq.beq Bytes instBEqOfDecidableEq wp.1 w && wp.2 == Q.other) =
          (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other) := by
        funext wp
        by_cases h : wp.1 = w
        · subst h; simp
        · rw [show @BEq.beq Bytes instBEqOfDecidableEq wp.1 w = false from decide_eq_false h,
              beq_false_of_ne h]
      rw [hpred]
      cases List.findIdx? (fun wp : Bytes × Party => wp.1 == w && wp.2 == Q.other) hw.reverse with
      | none => simp
      | some j => rfl

theorem oracleImplRSessionTracked_recvTail_eq_trackHalted {ℓ : ℕ} {RCoins : Type}
    [SampleableType RCoins] (C : Crypto) (K : MlKem)
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (qep : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (tail : (Party × Bytes) ⊕ ((Party × Bytes) ⊕ Party)) :
    oracleImplRSessionTracked (kemFailSessionTracker (ℓ := ℓ) C K) sm (2 + 1) qep cfg
        (smRecvTailToSpec (ℓ := ℓ) tail) =
      oracleImplRTrackHalted C.F K sm 3 qep cfg (smRecvTailToSpec (ℓ := ℓ) tail) := by
  rcases tail with dl | (ij | cr)
  · exact congrFun (deliverRSessionTracked_kemFail_eq C K sm cfg) dl
  · exact injectRM_smSchemeTrackState_eq sm 3 qep cfg ij
  · rfl

end RecvTailOracleBridge

end Computational.Proofs.E2E.Dsl.HaltedDrSessionSimDispatch
