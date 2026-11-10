/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.M2Interfaces
public import Computational.Proofs.E2E.Dsl.PqxdhSimTypes
import Computational.Proofs.E2E.Dsl.ClampsLossless

/-!
# Driver State Representation, Mirror Updates, and Query Guards

Defines the `ReductionDsl` representation `e2eDrvStateTy` of `BHE2EDrvState`, bounded-list
indexing and update combinators, `KeyInd` mirror updates, and admissibility/promotion guards.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Computational.Proofs.E2E.Dsl.E2EStateRepr

open OracleSpec OracleComp
open ReductionDsl (Ty Var Env Ops Iface Expr Comp UniformSamplerTag bits)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (GameState)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes ModelDriverBase ModelDriverInstanceMeta BHModelInst
  BHE2EDrvState bhDrvSessionInitPrin? bhInitRegId bhDrvAcceptIkOk bhDrvInitiateIkOk
  bhDrvKiQueryOk bhNoOpkRespPromoted bhBaseMirror bhE2EMirror bhBaseOpkOk bhE2EGuard
  bhE2EDrvWon bhE2EInstIkACorr)
open CryptoVerification.E2E.Costed (e2eSig PB PU32 U32 BV256 FinT IdKey
  bundleT bundleV bundleOfV hdrT hdrV hdrOfV sidT sidV sidOfV
  keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec
  E2EPureOp E2ECryptoOp e2eCryptoOps e2eOps e2eSessionTargetIface)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  size_e2ePureOp e2eCryptoOp eval_e2eCryptoOp cost_e2eCryptoOp size_e2eCryptoOp
  bundleOfV_bundleV bundleV_bundleOfV hdrOfV_hdrV hdrV_hdrOfV sidOfV_sidV sidV_sidOfV
  keyIndQdec_keyIndQenc keyIndQenc_keyIndQdec keyIndRdec_keyIndRenc keyIndRenc_keyIndRdec)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2eCryptoOps_eval_pow8_lossless)
open Computational.Proofs.GameHop.ReductionDsl.CostUB (exprCostUB compCostUB compQueriesUB
  exprCost_le_costUB compCost_le_costUB compQueries_le_queriesUB
  exprCostUB_v0 exprCostUB_v1 exprCostUB_v2 bits_zero bits_one bits_two bits_three)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v cost_v exprCostUB_v
  eLet eCaseOpt eCaseSum eFind eAny
  orE eval_orE isSomeE eval_isSomeE isNoneE eval_isNoneE optMapE eval_optMapE
  sidEqE eval_sidEqE stepAIface mkStepAPqxdhHooks
  liftP_bind liftP_pure liftP_map
  bndIkB bndSpkB bndOpkB bndPqB hdrIkA hdrEkA hdrSpkId hdrPqId
  e2eKeyIndStateTy e2eKeyIndStateToVal e2eValToKeyIndState
  e2eValToKeyIndState_toVal e2eKeyIndStateToVal_ofVal)
open Computational.Proofs.E2E.Dsl.M2Interfaces (e2eGsTy e2eGsEnc e2eGsDec)

/-! ## Driver-state representation and codecs -/

section StateTypes

@[reducible] def e2eMirrorPrinEntryTy {ℓ : ℕ} (S : SignalPqxdh.Setup) : Ty (e2eSig ℓ) :=
  .prod (FinT S.N_id) (PB 32)

@[reducible] def e2eMirrorBundleEntryTy {ℓ : ℕ} (S : SignalPqxdh.Setup) : Ty (e2eSig ℓ) :=
  .prod (.prod (FinT S.N_id) (FinT S.N_recv)) (.prod (PB 32) (PB 1568))

@[reducible] def e2eMirrorOpkEntryTy {ℓ : ℕ} (S : SignalPqxdh.Setup) : Ty (e2eSig ℓ) :=
  .prod (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_opk))) (PB 32)

@[reducible] def e2eMirrorSendEntryTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (sidT S) (.prod bundleT hdrT)

def e2eMirrorSendEnc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (x : SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr) :
    (e2eMirrorSendEntryTy S ℓ).denote :=
  (sidV x.1, (bundleV x.2.1, hdrV x.2.2))

def e2eMirrorSendDec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (e2eMirrorSendEntryTy S ℓ).denote) :
    SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr :=
  (sidOfV v.1, (bundleOfV v.2.1, hdrOfV v.2.2))

@[simp] theorem e2eMirrorSendDec_e2eMirrorSendEnc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (x : SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr) :
    e2eMirrorSendDec (e2eMirrorSendEnc (ℓ := ℓ) x) = x := by
  rcases x with ⟨s, bnd, hdr⟩; simp [e2eMirrorSendEnc, e2eMirrorSendDec]

@[simp] theorem e2eMirrorSendEnc_e2eMirrorSendDec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (e2eMirrorSendEntryTy S ℓ).denote) :
    e2eMirrorSendEnc (e2eMirrorSendDec v) = v := by
  rcases v with ⟨sv, bv, hv⟩; simp [e2eMirrorSendEnc, e2eMirrorSendDec]

@[reducible] def e2eMirrorBaseTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (.list (e2eMirrorPrinEntryTy S))
    (.prod (.list (e2eMirrorBundleEntryTy S))
      (.prod (.list (e2eMirrorOpkEntryTy S))
        (.list (e2eMirrorSendEntryTy S ℓ))))

def e2eMirrorBaseEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} (ds : ModelDriverBase S) :
    (e2eMirrorBaseTy S ℓ).denote :=
  (ds.prins, (ds.bundles, (ds.opks, ds.sends.map e2eMirrorSendEnc)))

def e2eMirrorBaseDec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (e2eMirrorBaseTy S ℓ).denote) : ModelDriverBase S :=
  { prins := v.1, bundles := v.2.1, opks := v.2.2.1, sends := v.2.2.2.map e2eMirrorSendDec }

@[simp] theorem e2eMirrorBaseDec_e2eMirrorBaseEnc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverBase S) :
    e2eMirrorBaseDec (e2eMirrorBaseEnc (ℓ := ℓ) ds) = ds := by
  cases ds; simp [e2eMirrorBaseEnc, e2eMirrorBaseDec, Function.comp_def]

@[simp] theorem e2eMirrorBaseEnc_e2eMirrorBaseDec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (e2eMirrorBaseTy S ℓ).denote) :
    e2eMirrorBaseEnc (e2eMirrorBaseDec v) = v := by
  rcases v with ⟨_, _, _, _⟩; simp [e2eMirrorBaseEnc, e2eMirrorBaseDec, Function.comp_def]

@[reducible] def e2eInstMetaTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod .bool (.prod .bool (.prod (.opt (FinT S.N_id)) (.prod (.opt (FinT S.N_recv)) (.opt PU32))))

def e2eInstMetaEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} (im : ModelDriverInstanceMeta S) :
    (e2eInstMetaTy S ℓ).denote :=
  (im.bobAccepted, (im.ikACorrAtAccept, (im.respPrin, (im.respSpkIdx, im.instOpkId?))))

def e2eInstMetaDec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (e2eInstMetaTy S ℓ).denote) : ModelDriverInstanceMeta S :=
  { bobAccepted := v.1, ikACorrAtAccept := v.2.1, respPrin := v.2.2.1,
    respSpkIdx := v.2.2.2.1, instOpkId? := v.2.2.2.2 }

@[simp] theorem e2eInstMetaDec_e2eInstMetaEnc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (im : ModelDriverInstanceMeta S) :
    e2eInstMetaDec (e2eInstMetaEnc (ℓ := ℓ) im) = im := by
  cases im; rfl

@[simp] theorem e2eInstMetaEnc_e2eInstMetaDec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (e2eInstMetaTy S ℓ).denote) :
    e2eInstMetaEnc (e2eInstMetaDec v) = v := by
  rcases v with ⟨_, _, _, _, _⟩; rfl

@[reducible] def e2eModelInstTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (sidT S) (.prod hdrT (.prod IdKey (.prod IdKey (.prod BV256 (.opt (e2eGsTy ℓ))))))

def e2eModelInstEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : BHModelInst S ℓ) :
    (e2eModelInstTy S ℓ).denote :=
  (sidV d.sid, (hdrV d.hdr, (d.idA, (d.idB, (d.spkCoins, d.gs.map e2eGsEnc)))))

def e2eModelInstDec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (e2eModelInstTy S ℓ).denote) : BHModelInst S ℓ :=
  { sid := sidOfV v.1, hdr := hdrOfV v.2.1, idA := v.2.2.1, idB := v.2.2.2.1,
    spkCoins := v.2.2.2.2.1, gs := v.2.2.2.2.2.map e2eGsDec }

@[simp] theorem e2eModelInstDec_sid {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : BHModelInst S ℓ) :
    (e2eModelInstDec (e2eModelInstEnc d)).sid = d.sid := by
  simp [e2eModelInstEnc, e2eModelInstDec]

@[simp] theorem e2eModelInstDec_hdr {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : BHModelInst S ℓ) :
    (e2eModelInstDec (e2eModelInstEnc d)).hdr = d.hdr := by
  simp [e2eModelInstEnc, e2eModelInstDec]

@[simp] theorem e2eModelInstDec_idA {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : BHModelInst S ℓ) :
    (e2eModelInstDec (e2eModelInstEnc d)).idA = d.idA := rfl

@[simp] theorem e2eModelInstDec_idB {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : BHModelInst S ℓ) :
    (e2eModelInstDec (e2eModelInstEnc d)).idB = d.idB := rfl

@[simp] theorem e2eModelInstDec_spkCoins {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : BHModelInst S ℓ) :
    (e2eModelInstDec (e2eModelInstEnc d)).spkCoins = d.spkCoins := rfl

@[simp] theorem e2eGsDec_e2eGsEnc_b {ℓ : ℕ}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) :
    (e2eGsDec (e2eGsEnc gs)).b = gs.b := rfl

@[simp] theorem e2eGsDec_e2eGsEnc_win {ℓ : ℕ}
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes) :
    (e2eGsDec (e2eGsEnc gs)).win = gs.win := rfl

theorem e2eModelInstDec_e2eModelInstEnc_of_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (d : BHModelInst S ℓ) (hgs : ∀ gs ∈ d.gs, e2eGsDec (e2eGsEnc gs) = gs) :
    e2eModelInstDec (e2eModelInstEnc d) = d := by
  cases d with
  | mk sid hdr idA idB spkCoins gs =>
    cases gs with
    | none => simp [e2eModelInstEnc, e2eModelInstDec]
    | some g => simp [e2eModelInstEnc, e2eModelInstDec, hgs g rfl]

/-- `ReductionDsl` representation of `BHE2EDrvState S ℓ`. -/
@[reducible] def e2eDrvStateTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eMirrorBaseTy S ℓ)
    (.prod (.list (FinT S.N_id))
      (.prod (.list (.prod (FinT S.N_id) (FinT S.N_recv)))
        (.prod (.list (e2eModelInstTy S ℓ))
          (.prod (.list (e2eInstMetaTy S ℓ))
            (.prod (e2eKeyIndStateTy ℓ S)
              (.prod .bool .bool))))))

def e2eDrvStateEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateTy S ℓ).denote :=
  (e2eMirrorBaseEnc σ.toModelDriverBase,
   (σ.corrPrins,
    (σ.revealedSpks,
     (σ.insts.map e2eModelInstEnc,
      (σ.instMeta.map e2eInstMetaEnc,
       (e2eKeyIndStateToVal σ.st,
        (σ.b, σ.paused)))))))

def e2eDrvStateDec {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (e2eDrvStateTy S ℓ).denote) : BHE2EDrvState S ℓ :=
  { toModelDriverBase := e2eMirrorBaseDec v.1
    corrPrins := v.2.1
    revealedSpks := v.2.2.1
    insts := v.2.2.2.1.map e2eModelInstDec
    instMeta := v.2.2.2.2.1.map e2eInstMetaDec
    st := e2eValToKeyIndState v.2.2.2.2.2.1
    b := v.2.2.2.2.2.2.1
    paused := v.2.2.2.2.2.2.2 }

@[simp] theorem e2eDrvStateDec_toModelDriverBase {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateDec (e2eDrvStateEnc σ)).toModelDriverBase = σ.toModelDriverBase := by
  simp [e2eDrvStateEnc, e2eDrvStateDec]

@[simp] theorem e2eDrvStateDec_corrPrins {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateDec (e2eDrvStateEnc σ)).corrPrins = σ.corrPrins := rfl

@[simp] theorem e2eDrvStateDec_revealedSpks {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateDec (e2eDrvStateEnc σ)).revealedSpks = σ.revealedSpks := rfl

@[simp] theorem e2eDrvStateDec_instMeta {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateDec (e2eDrvStateEnc σ)).instMeta = σ.instMeta := by
  simp [e2eDrvStateEnc, e2eDrvStateDec, Function.comp_def]

@[simp] theorem e2eDrvStateDec_st {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateDec (e2eDrvStateEnc σ)).st = σ.st := by
  dsimp only [e2eDrvStateEnc, e2eDrvStateDec]
  exact e2eValToKeyIndState_toVal σ.st

@[simp] theorem e2eDrvStateDec_b {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateDec (e2eDrvStateEnc σ)).b = σ.b := rfl

@[simp] theorem e2eDrvStateDec_paused {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateDec (e2eDrvStateEnc σ)).paused = σ.paused := rfl

@[simp] theorem e2eDrvStateDec_won {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (b : Bool) :
    bhE2EDrvWon (e2eDrvStateDec (e2eDrvStateEnc σ)) b = bhE2EDrvWon σ b := by
  simp only [bhE2EDrvWon, e2eDrvStateEnc, e2eDrvStateDec, List.any_map]
  apply List.any_congr rfl; intro d
  rcases hgs : d.gs with _ | g <;> simp [e2eModelInstEnc, e2eModelInstDec, hgs]

@[simp] theorem e2eDrvStateDec_guard {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    bhE2EGuard (e2eDrvStateDec (e2eDrvStateEnc σ)) sid = bhE2EGuard σ sid := by
  simp only [bhE2EGuard, e2eDrvStateDec_toModelDriverBase]
  have h1 : (e2eDrvStateDec (e2eDrvStateEnc σ)).insts.any (fun d => d.sid == sid) =
      σ.insts.any (fun d => d.sid == sid) := by
    simp [e2eDrvStateEnc, e2eDrvStateDec, List.any_map, Function.comp_def]
  have h2 : ∀ ek, (e2eDrvStateDec (e2eDrvStateEnc σ)).insts.any (fun d => d.hdr.ekAPk == ek) =
      σ.insts.any (fun d => d.hdr.ekAPk == ek) := by
    intro ek; simp [e2eDrvStateEnc, e2eDrvStateDec, List.any_map, Function.comp_def]
  rw [h1]
  rcases hs : σ.sends.find? (fun x => x.1 == sid) with _ | ⟨_, bnd, hdr⟩
  · simp [hs]
  · simp only [hs, h2 hdr.ekAPk, e2eDrvStateDec_corrPrins]
    rfl

theorem e2eDrvStateDec_e2eDrvStateEnc_of_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ)
    (hgs : ∀ d ∈ σ.insts, ∀ gs ∈ d.gs, e2eGsDec (e2eGsEnc gs) = gs) :
    e2eDrvStateDec (e2eDrvStateEnc σ) = σ := by
  cases σ with
  | mk base corr advRev insts metaL st b paused =>
    have hinst : (insts.map e2eModelInstEnc).map e2eModelInstDec = insts := by
      rw [List.map_map]
      exact (List.map_congr_left fun d hd =>
        e2eModelInstDec_e2eModelInstEnc_of_gs d (hgs d hd)).trans (List.map_id insts)
    have hmeta : (metaL.map (e2eInstMetaEnc (ℓ := ℓ))).map e2eInstMetaDec = metaL := by
      simp [Function.comp_def]
    dsimp only [e2eDrvStateEnc, e2eDrvStateDec]
    rw [e2eMirrorBaseDec_e2eMirrorBaseEnc, hinst, hmeta, e2eValToKeyIndState_toVal]

/-- Length bounds on the mirror and session-instance lists of `BHE2EDrvState S ℓ`. -/
structure DrvMirrorBounded {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (nPrins nBundles nOpks nSends nCorr qStart : ℕ) (σ : BHE2EDrvState S ℓ) : Prop where
  prins_le : σ.prins.length ≤ nPrins
  bundles_le : σ.bundles.length ≤ nBundles
  opks_le : σ.opks.length ≤ nOpks
  sends_le : σ.sends.length ≤ nSends
  corrPrins_le : σ.corrPrins.length ≤ nCorr
  insts_le : σ.insts.length ≤ qStart
  instMeta_le : σ.instMeta.length ≤ qStart

abbrev DrvQueryBounded {S : SignalPqxdh.Setup} {ℓ : ℕ} (qMir qStart : ℕ)
    (σ : BHE2EDrvState S ℓ) : Prop :=
  DrvMirrorBounded qMir qMir qMir qMir qMir qStart σ

theorem DrvMirrorBounded.empty {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (nPrins nBundles nOpks nSends nCorr qStart : ℕ) (b : Bool) :
    DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart
      ({ st := SignalPqxdh.KeyIndState.empty S false, b := b } : BHE2EDrvState S ℓ) :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
   Nat.zero_le _, Nat.zero_le _⟩

theorem DrvMirrorBounded.bhE2EMirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {nPrins nBundles nOpks nSends nCorr qStart : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    DrvMirrorBounded (nPrins + 1) (nBundles + 1) (nOpks + 1) (nSends + 1) (nCorr + 1) qStart
      (CryptoVerification.E2E.bhE2EMirror σ kq kr) := by
  obtain ⟨hp, hb, ho, hs, hc, hi, hm⟩ := h
  have hbase :
      (CryptoVerification.E2E.bhBaseMirror σ.toModelDriverBase kq kr).prins.length ≤ nPrins + 1 ∧
      (CryptoVerification.E2E.bhBaseMirror σ.toModelDriverBase kq kr).bundles.length ≤
        nBundles + 1 ∧
      (CryptoVerification.E2E.bhBaseMirror σ.toModelDriverBase kq kr).opks.length ≤ nOpks + 1 ∧
      (CryptoVerification.E2E.bhBaseMirror σ.toModelDriverBase kq kr).sends.length ≤ nSends + 1 := by
    unfold CryptoVerification.E2E.bhBaseMirror
    split <;> (try simp only [List.length_cons]) <;> omega
  have hcorr :
      (CryptoVerification.E2E.bhE2EMirror σ kq kr).corrPrins.length ≤ nCorr + 1 := by
    unfold CryptoVerification.E2E.bhE2EMirror
    dsimp only
    split <;> (try simp only [List.length_cons]) <;> omega
  exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2, hcorr, hi, hm⟩

theorem DrvQueryBounded.bhE2EMirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {qMir qStart : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvQueryBounded qMir qStart σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    DrvQueryBounded (qMir + 1) qStart (CryptoVerification.E2E.bhE2EMirror σ kq kr) :=
  DrvMirrorBounded.bhE2EMirror h kq kr

end StateTypes

/-! ## Field projections and bounded list operations -/

section ProjectionsAndLists

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {O : Ops (e2eSig ℓ)}

def mbPrins {Γ} (ds : Expr O Γ (e2eMirrorBaseTy S ℓ)) :
    Expr O Γ (.list (e2eMirrorPrinEntryTy S)) := .fst ds
def mbBundles {Γ} (ds : Expr O Γ (e2eMirrorBaseTy S ℓ)) :
    Expr O Γ (.list (e2eMirrorBundleEntryTy S)) := .fst (.snd ds)
def mbOpks {Γ} (ds : Expr O Γ (e2eMirrorBaseTy S ℓ)) :
    Expr O Γ (.list (e2eMirrorOpkEntryTy S)) := .fst (.snd (.snd ds))
def mbSends {Γ} (ds : Expr O Γ (e2eMirrorBaseTy S ℓ)) :
    Expr O Γ (.list (e2eMirrorSendEntryTy S ℓ)) := .snd (.snd (.snd ds))

def imBobAccepted {Γ} (im : Expr O Γ (e2eInstMetaTy S ℓ)) : Expr O Γ .bool := .fst im
def imIkACorr {Γ} (im : Expr O Γ (e2eInstMetaTy S ℓ)) : Expr O Γ .bool := .fst (.snd im)
def imRespPrin {Γ} (im : Expr O Γ (e2eInstMetaTy S ℓ)) :
    Expr O Γ (.opt (FinT S.N_id)) := .fst (.snd (.snd im))
def imRespSpkIdx {Γ} (im : Expr O Γ (e2eInstMetaTy S ℓ)) :
    Expr O Γ (.opt (FinT S.N_recv)) := .fst (.snd (.snd (.snd im)))
def imOpkId {Γ} (im : Expr O Γ (e2eInstMetaTy S ℓ)) :
    Expr O Γ (.opt PU32) := .snd (.snd (.snd (.snd im)))

def miSid {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) : Expr O Γ (sidT S) := .fst d
def miHdr {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) : Expr O Γ hdrT := .fst (.snd d)
def miIdA {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) : Expr O Γ IdKey := .fst (.snd (.snd d))
def miIdB {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) : Expr O Γ IdKey := .fst (.snd (.snd (.snd d)))
def miSpkCoins {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) :
    Expr O Γ BV256 := .fst (.snd (.snd (.snd (.snd d))))
def miGs {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) :
    Expr O Γ (.opt (e2eGsTy ℓ)) := .snd (.snd (.snd (.snd (.snd d))))

def miSetGsE {Γ} (d : Expr O Γ (e2eModelInstTy S ℓ)) (gs? : Expr O Γ (.opt (e2eGsTy ℓ))) :
    Expr O Γ (e2eModelInstTy S ℓ) :=
  eLet (.pair d gs?) fun p =>
    .pair (miSid (.fst (v p))) (.pair (miHdr (.fst (v p))) (.pair (miIdA (.fst (v p)))
      (.pair (miIdB (.fst (v p))) (.pair (miSpkCoins (.fst (v p))) (.snd (v p))))))

def drvBase {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) : Expr O Γ (e2eMirrorBaseTy S ℓ) := .fst σ
def drvCorrPrins {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (.list (FinT S.N_id)) := .fst (.snd σ)
def drvRevSpks {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (.list (.prod (FinT S.N_id) (FinT S.N_recv))) := .fst (.snd (.snd σ))
def drvInsts {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (.list (e2eModelInstTy S ℓ)) := .fst (.snd (.snd (.snd σ)))
def drvInstMeta {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (.list (e2eInstMetaTy S ℓ)) := .fst (.snd (.snd (.snd (.snd σ))))
def drvSt {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ (e2eKeyIndStateTy ℓ S) := .fst (.snd (.snd (.snd (.snd (.snd σ)))))
def drvB {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd (.snd σ))))))
def drvPaused {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) :
    Expr O Γ .bool := .snd (.snd (.snd (.snd (.snd (.snd (.snd σ))))))

def drvSetInstsE {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ))
    (insts : Expr O Γ (.list (e2eModelInstTy S ℓ))) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σ insts) fun p =>
    .pair (drvBase (.fst (v p))) (.pair (drvCorrPrins (.fst (v p)))
      (.pair (drvRevSpks (.fst (v p)))
        (.pair (.snd (v p)) (.snd (.snd (.snd (.snd (.fst (v p)))))))))

def drvSetInstMetaE {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ))
    (metaL : Expr O Γ (.list (e2eInstMetaTy S ℓ))) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σ metaL) fun p =>
    .pair (drvBase (.fst (v p))) (.pair (drvCorrPrins (.fst (v p)))
      (.pair (drvRevSpks (.fst (v p))) (.pair (drvInsts (.fst (v p)))
        (.pair (.snd (v p)) (.snd (.snd (.snd (.snd (.snd (.fst (v p)))))))))))

def drvSetStE {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ))
    (st : Expr O Γ (e2eKeyIndStateTy ℓ S)) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σ st) fun p =>
    .pair (drvBase (.fst (v p))) (.pair (drvCorrPrins (.fst (v p)))
      (.pair (drvRevSpks (.fst (v p))) (.pair (drvInsts (.fst (v p)))
        (.pair (drvInstMeta (.fst (v p)))
          (.pair (.snd (v p)) (.snd (.snd (.snd (.snd (.snd (.snd (.fst (v p)))))))))))))

def drvSetBE {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) (bE : Expr O Γ .bool) :
    Expr O Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σ bE) fun p =>
    .pair (drvBase (.fst (v p))) (.pair (drvCorrPrins (.fst (v p)))
      (.pair (drvRevSpks (.fst (v p))) (.pair (drvInsts (.fst (v p)))
        (.pair (drvInstMeta (.fst (v p))) (.pair (drvSt (.fst (v p)))
          (.pair (.snd (v p)) (drvPaused (.fst (v p)))))))))

def drvSetPausedE {Γ} (σ : Expr O Γ (e2eDrvStateTy S ℓ)) (pE : Expr O Γ .bool) :
    Expr O Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σ pE) fun p =>
    .pair (drvBase (.fst (v p))) (.pair (drvCorrPrins (.fst (v p)))
      (.pair (drvRevSpks (.fst (v p))) (.pair (drvInsts (.fst (v p)))
        (.pair (drvInstMeta (.fst (v p))) (.pair (drvSt (.fst (v p)))
          (.pair (drvB (.fst (v p))) (.snd (v p))))))))

def emptyDrvStateE {Γ} (bE : Expr O Γ .bool) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  .pair (.pair .nil (.pair .nil (.pair .nil .nil)))
    (.pair .nil (.pair .nil (.pair .nil (.pair .nil
      (.pair (.pair (.bool false) (.pair .nil (.pair .nil (.pair .nil (.pair .nil
          (.pair .nil (.pair .nil (.pair .nil (.pair .nil (.pair .nil .nil))))))))))
        (.pair bE (.bool false)))))))

@[simp] theorem eval_emptyDrvStateE {Γ} (bE : Expr O Γ .bool) (ρ : Env Γ) :
    (emptyDrvStateE (S := S) bE).eval ρ =
      e2eDrvStateEnc ({ b := bE.eval ρ } : BHE2EDrvState S ℓ) := rfl

@[simp] theorem exprCostUB_emptyDrvStateE {Γ} (bE : Expr O Γ .bool) :
    exprCostUB (emptyDrvStateE (S := S) bE) = exprCostUB bE + 40 := by
  simp only [emptyDrvStateE, exprCostUB, Nat.reduceAdd]; omega

@[simp] theorem cost_emptyDrvStateE {Γ} (bE : Expr O Γ .bool) :
    (emptyDrvStateE (S := S) bE).cost = bE.cost + 40 := by
  simp only [emptyDrvStateE, Expr.cost, Nat.reduceAdd]; omega

@[simp] theorem size_emptyDrvStateE {Γ} (bE : Expr O Γ .bool) :
    (emptyDrvStateE (S := S) bE).size = bE.size + 40 := by
  simp only [emptyDrvStateE, Expr.size, Nat.reduceAdd]; omega

theorem eval_miSetGsE {Γ} (dE : Expr O Γ (e2eModelInstTy S ℓ))
    (gsE : Expr O Γ (.opt (e2eGsTy ℓ))) (ρ : Env Γ)
    {d : BHModelInst S ℓ} {gs? : Option (GameState (GhostState Bytes) (Plain ℓ) Bytes)}
    (hd : dE.eval ρ = e2eModelInstEnc d) (hgs : gsE.eval ρ = gs?.map e2eGsEnc) :
    (miSetGsE dE gsE).eval ρ = e2eModelInstEnc { d with gs := gs? } := by
  simp [miSetGsE, miSid, miHdr, miIdA, miIdB, miSpkCoins, e2eModelInstEnc,
    eLet, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hd, hgs]

theorem eval_drvSetInstsE {Γ} (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (instsE : Expr O Γ (.list (e2eModelInstTy S ℓ))) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {insts : List (BHModelInst S ℓ)}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hi : instsE.eval ρ = insts.map e2eModelInstEnc) :
    (drvSetInstsE σE instsE).eval ρ = e2eDrvStateEnc { σ with insts := insts } := by
  simp [drvSetInstsE, drvBase, drvCorrPrins, drvRevSpks,
    e2eDrvStateEnc, eLet, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hσ, hi]

theorem eval_drvSetInstMetaE {Γ} (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (metaE : Expr O Γ (.list (e2eInstMetaTy S ℓ))) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {metaL : List (ModelDriverInstanceMeta S)}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hm : metaE.eval ρ = metaL.map e2eInstMetaEnc) :
    (drvSetInstMetaE σE metaE).eval ρ = e2eDrvStateEnc { σ with instMeta := metaL } := by
  simp [drvSetInstMetaE, drvBase, drvCorrPrins, drvRevSpks, drvInsts,
    e2eDrvStateEnc, eLet, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hσ, hm]

theorem eval_drvSetStE {Γ} (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {st : SignalPqxdh.KeyIndState S}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hst : stE.eval ρ = e2eKeyIndStateToVal st) :
    (drvSetStE σE stE).eval ρ = e2eDrvStateEnc { σ with st := st } := by
  simp [drvSetStE, drvBase, drvCorrPrins, drvRevSpks, drvInsts, drvInstMeta,
    e2eDrvStateEnc, eLet, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hσ, hst]

theorem eval_drvSetBE {Γ} (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (bE : Expr O Γ .bool) (ρ : Env Γ) {σ : BHE2EDrvState S ℓ}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) :
    (drvSetBE σE bE).eval ρ = e2eDrvStateEnc { σ with b := bE.eval ρ } := by
  simp [drvSetBE, drvBase, drvCorrPrins, drvRevSpks, drvInsts, drvInstMeta, drvSt, drvPaused,
    e2eDrvStateEnc, eLet, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hσ]

theorem eval_drvSetPausedE {Γ} (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (pE : Expr O Γ .bool) (ρ : Env Γ) {σ : BHE2EDrvState S ℓ}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) :
    (drvSetPausedE σE pE).eval ρ = e2eDrvStateEnc { σ with paused := pE.eval ρ } := by
  simp [drvSetPausedE, drvBase, drvCorrPrins, drvRevSpks, drvInsts, drvInstMeta, drvSt, drvB,
    e2eDrvStateEnc, eLet, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hσ]

def sumL? {α β : Type} : α ⊕ β → Option α
  | .inl x => some x
  | .inr _ => none

def sumR? {α β : Type} : α ⊕ β → Option β
  | .inl _ => none
  | .inr y => some y

@[simp] theorem sumL?_inl {α β : Type} (x : α) : sumL? (.inl x : α ⊕ β) = some x := rfl
@[simp] theorem sumL?_inr {α β : Type} (y : β) : sumL? (.inr y : α ⊕ β) = none := rfl
@[simp] theorem sumR?_inl {α β : Type} (x : α) : sumR? (.inl x : α ⊕ β) = none := rfl
@[simp] theorem sumR?_inr {α β : Type} (y : β) : sumR? (.inr y : α ⊕ β) = some y := rfl

def sumLeft? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β)) : Expr O Γ (.opt α) :=
  .caseSum e (.some .v0) .none

def sumRight? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β)) : Expr O Γ (.opt β) :=
  .caseSum e .none (.some .v0)

def optSumLeft? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt (.sum α β))) : Expr O Γ (.opt α) :=
  .caseOpt e .none (.caseSum .v0 (.some .v0) .none)

def optSumRight? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.opt (.sum α β))) : Expr O Γ (.opt β) :=
  .caseOpt e .none (.caseSum .v0 .none (.some .v0))

def optZipE {Γ} {α β : Ty (e2eSig ℓ)}
    (a : Expr O Γ (.opt α)) (b : Expr O Γ (.opt β)) : Expr O Γ (.opt (.prod α β)) :=
  eLet (.pair a b) fun ab =>
    eCaseOpt (.fst (v ab)) .none fun x =>
      eCaseOpt (.snd (v ab)) .none fun y =>
        .some (.pair (v x) (v y))

@[simp] theorem eval_sumLeft? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.sum α β)) (ρ : Env Γ) :
    (sumLeft? e).eval ρ = sumL? (e.eval ρ) := by
  simp only [sumLeft?, Expr.eval, Expr.v0]; cases e.eval ρ <;> rfl

@[simp] theorem eval_sumRight? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.sum α β)) (ρ : Env Γ) :
    (sumRight? e).eval ρ = sumR? (e.eval ρ) := by
  simp only [sumRight?, Expr.eval, Expr.v0]; cases e.eval ρ <;> rfl

@[simp] theorem eval_optSumLeft? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt (.sum α β))) (ρ : Env Γ) :
    (optSumLeft? e).eval ρ = (e.eval ρ).bind sumL? := by
  simp only [optSumLeft?, Expr.eval, Expr.v0]; rcases e.eval ρ with _ | (_ | _) <;> rfl

@[simp] theorem eval_optSumRight? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt (.sum α β))) (ρ : Env Γ) :
    (optSumRight? e).eval ρ = (e.eval ρ).bind sumR? := by
  simp only [optSumRight?, Expr.eval, Expr.v0]; rcases e.eval ρ with _ | (_ | _) <;> rfl

@[simp] theorem eval_optZipE {Γ} {α β : Ty (e2eSig ℓ)}
    (a : Expr O Γ (.opt α)) (b : Expr O Γ (.opt β)) (ρ : Env Γ) :
    (optZipE a b).eval ρ =
      match a.eval ρ, b.eval ρ with | some x, some y => some (x, y) | _, _ => none := by
  simp only [optZipE, eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, Env.get]
  cases a.eval ρ <;> cases b.eval ρ <;> rfl

@[simp] theorem exprCostUB_sumLeft? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β)) :
    exprCostUB (sumLeft? e) = exprCostUB e + 4 := rfl

@[simp] theorem exprCostUB_sumRight? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β)) :
    exprCostUB (sumRight? e) = exprCostUB e + 4 := rfl

@[simp] theorem exprCostUB_optSumLeft? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt (.sum α β))) :
    exprCostUB (optSumLeft? e) = exprCostUB e + 7 := rfl

@[simp] theorem exprCostUB_optSumRight? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt (.sum α β))) :
    exprCostUB (optSumRight? e) = exprCostUB e + 7 := rfl

@[simp] theorem exprCostUB_optZipE {Γ} {α β : Ty (e2eSig ℓ)}
    (a : Expr O Γ (.opt α)) (b : Expr O Γ (.opt β)) :
    exprCostUB (optZipE a b) = exprCostUB a + exprCostUB b + 14 := by
  simp only [optZipE, eLet, eCaseOpt, exprCostUB, exprCostUB_v, Nat.reduceAdd]

@[simp] theorem cost_sumLeft? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β)) :
    (sumLeft? e).cost = e.cost + 3 := by
  simp only [sumLeft?, Expr.cost, Expr.v0, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]

@[simp] theorem cost_sumRight? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β)) :
    (sumRight? e).cost = e.cost + 3 := by
  simp only [sumRight?, Expr.cost, Expr.v0, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte,
    Nat.reduceAdd]

@[simp] theorem cost_optSumLeft? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt (.sum α β))) :
    (optSumLeft? e).cost = e.cost + 5 := by
  simp only [optSumLeft?, Expr.cost, Expr.v0, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte,
    Nat.reduceAdd]

@[simp] theorem cost_optSumRight? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt (.sum α β))) :
    (optSumRight? e).cost = e.cost + 5 := by
  simp only [optSumRight?, Expr.cost, Expr.v0, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte,
    Nat.reduceAdd]

@[simp] theorem cost_optZipE {Γ} {α β : Ty (e2eSig ℓ)}
    (a : Expr O Γ (.opt α)) (b : Expr O Γ (.opt β)) :
    (optZipE a b).cost = a.cost + b.cost + 12 := by
  simp only [optZipE, eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, Expr.cost,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]

@[simp] private theorem size_v {Γ Δ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    [h : Ext Γ Δ] (x : Var Γ τ) :
    (v (O := O) (Δ := Δ) x).size = 1 := rfl

@[simp] theorem size_sumLeft? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β)) :
    (sumLeft? e).size = e.size + 4 := rfl

@[simp] theorem size_sumRight? {Γ} {α β : Ty (e2eSig ℓ)} (e : Expr O Γ (.sum α β)) :
    (sumRight? e).size = e.size + 4 := rfl

@[simp] theorem size_optSumLeft? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt (.sum α β))) :
    (optSumLeft? e).size = e.size + 7 := rfl

@[simp] theorem size_optSumRight? {Γ} {α β : Ty (e2eSig ℓ)}
    (e : Expr O Γ (.opt (.sum α β))) :
    (optSumRight? e).size = e.size + 7 := rfl

@[simp] theorem size_optZipE {Γ} {α β : Ty (e2eSig ℓ)}
    (a : Expr O Γ (.opt α)) (b : Expr O Γ (.opt β)) :
    (optZipE a b).size = a.size + b.size + 14 := by
  simp only [optZipE, eLet, eCaseOpt, Expr.size, size_v, Nat.reduceAdd]

attribute [local irreducible] sumLeft? sumRight? optSumLeft? optSumRight? optZipE

def listSnocE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (x : Expr O Γ τ) : Expr O Γ (.list τ) :=
  .appendL (K + 1) l (.cons x .nil)

@[simp] theorem eval_listSnocE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (x : Expr O Γ τ) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (listSnocE K l x).eval ρ = l.eval ρ ++ [x.eval ρ] := by
  simp only [listSnocE, Expr.eval]
  apply List.take_of_length_le
  simp only [List.length_append, List.length_singleton]; omega

theorem exprCostUB_listSnocE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (x : Expr O Γ τ) :
    exprCostUB (listSnocE K l x) ≤ exprCostUB l + exprCostUB x + K + 4 := by
  simp only [listSnocE, exprCostUB]; omega

theorem cost_listSnocE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (x : Expr O Γ τ) :
    (listSnocE K l x).cost ≤ l.cost + x.cost + K + 4 := by
  simp only [listSnocE, Expr.cost]; omega

attribute [local irreducible] listSnocE

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

def listGetOptE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) : Expr O Γ (.opt τ) :=
  eLet (.pair l (.pair idx (.len l))) fun p =>
    .snd (.foldrB K (.fst (v p)) (.pair (.nat 0) .none)
      (.pair (.add (.fst .v1) (.nat 1))
        (.ite (.eqN (.add (.fst (.snd .v2)) (.add (.fst .v1) (.nat 1))) (.snd (.snd .v2)))
          (.some .v0) (.snd .v1))))

@[simp] theorem eval_listGetOptE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (listGetOptE K l idx).eval ρ = (l.eval ρ)[idx.eval ρ]? := by
  simp only [listGetOptE, eLet, v, Ext.wk, Ext.refl, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
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

theorem exprCostUB_listGetOptE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) :
    exprCostUB (listGetOptE K l idx) ≤ 2 * exprCostUB l + exprCostUB idx + 32 * K + 20 := by
  simp only [listGetOptE, eLet, exprCostUB, exprCostUB_v0, exprCostUB_v1,
    exprCostUB_v2, exprCostUB_v, bits_zero, bits_one, Nat.reduceAdd]
  omega

theorem cost_listGetOptE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) :
    (listGetOptE K l idx).cost ≤ 2 * l.cost + idx.cost + 32 * K + 20 := by
  simp only [listGetOptE, eLet, v, Ext.wk, Ext.refl, Expr.cost, Expr.v0, Expr.v1, Expr.v2, bits,
    show Nat.log 2 0 = 0 from rfl, show Nat.log 2 1 = 0 from rfl,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
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

def listSetE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (val : Expr O Γ τ) : Expr O Γ (.list τ) :=
  eLet (.pair l (.pair idx (.pair val (.len l)))) fun p =>
    .snd (.foldrB K (.fst (v p)) (.pair (.nat 0) .nil)
      (.pair (.add (.fst .v1) (.nat 1))
        (.cons
          (.ite (.eqN (.add (.fst (.snd .v2)) (.add (.fst .v1) (.nat 1)))
                      (.snd (.snd (.snd .v2))))
            (.fst (.snd (.snd .v2))) .v0)
          (.snd .v1))))

@[simp] theorem eval_listSetE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (val : Expr O Γ τ) (ρ : Env Γ)
    (hlen : (l.eval ρ).length ≤ K) :
    (listSetE K l idx val).eval ρ = (l.eval ρ).set (idx.eval ρ) (val.eval ρ) := by
  simp only [listSetE, eLet, v, Ext.wk, Ext.refl, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
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

theorem exprCostUB_listSetE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (val : Expr O Γ τ) :
    exprCostUB (listSetE K l idx val) ≤
      2 * exprCostUB l + exprCostUB idx + exprCostUB val + 40 * K + 24 := by
  simp only [listSetE, eLet, exprCostUB, exprCostUB_v0, exprCostUB_v1,
    exprCostUB_v2, exprCostUB_v, bits_zero, bits_one, Nat.reduceAdd]
  omega

theorem cost_listSetE (K : ℕ) {Γ} {τ : Ty (e2eSig ℓ)}
    (l : Expr O Γ (.list τ)) (idx : Expr O Γ .nat) (val : Expr O Γ τ) :
    (listSetE K l idx val).cost ≤ 2 * l.cost + idx.cost + val.cost + 36 * K + 24 := by
  simp only [listSetE, eLet, v, Ext.wk, Ext.refl, Expr.cost, Expr.v0, Expr.v1, Expr.v2, bits,
    show Nat.log 2 0 = 0 from rfl, show Nat.log 2 1 = 0 from rfl,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

attribute [local irreducible] listSetE

end ProjectionsAndLists

/-! ## Query extractors, mirror updates, and guards -/

section GuardsAndMirrors

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "E2EExpr" => Expr (e2eOps ℓ P C K decT encT)

@[simp] private theorem pnat32_val : (32 : ℕ+).val = 32 := rfl
@[simp] private theorem pnat1568_val : (1568 : ℕ+).val = 1568 := rfl

def initKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) {Γ} :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ (e2eDrvStateTy S ℓ) :=
  .bind (.sample (I := stepAIface ℓ I₀) UniformSamplerTag.bool .unit)
    (.ret (emptyDrvStateE .v0))

theorem eval_initKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) {Γ} (ρ : Env Γ) :
    (initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I₀).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun b : Bool => e2eDrvStateEnc ({ b := b } : BHE2EDrvState S ℓ)) <$>
          ($ᵗ Bool : ProbComp Bool)) := by
  have hsamp : (stepAIface ℓ I₀).smp.samp UniformSamplerTag.bool () = ($ᵗ Bool) := rfl
  simp only [initKindC, Comp.eval, Expr.eval, Expr.v0, Env.get, eval_emptyDrvStateE, hsamp,
    liftP_bind, liftP_pure, liftP_map, map_eq_bind_pure_comp, Function.comp_def]

@[simp] theorem queries_initKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) {Γ}
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    (initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ) I₀).queries w (fun _ => 0) = 0 := rfl

@[simp] theorem queriesUB_initKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) {Γ}
    (w : (stepAIface ℓ I₀).Tag → ℕ) :
    compQueriesUB w (fun _ => 0)
      (initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) (Γ := Γ) I₀) = 0 := rfl

theorem compCostUB_initKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) {Γ} :
    compCostUB (initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ) I₀) ≤ 48 := by
  simp only [initKindC, compCostUB, exprCostUB_emptyDrvStateE, exprCostUB_v0, exprCostUB,
    stepAIface]
  omega

theorem cost_initKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) {Γ} :
    (initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ) I₀).cost ≤ 48 :=
  le_trans (compCost_le_costUB _) (compCostUB_initKindC I₀)

theorem size_initKindC {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) {Γ} :
    (initKindC (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ) I₀).size ≤ 48 := by
  simp only [initKindC, Comp.size, size_emptyDrvStateE, Expr.v0, Expr.size, Nat.reduceAdd]
  omega

attribute [local irreducible] initKindC

def e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) : E2EExpr Γ .bool :=
  eLet (.pair a b) fun ab =>
    sidEqE (mkStepAPqxdhHooks ℓ P C K decT encT (e2eSessionTargetIface ℓ))
      (.fst (v ab)) (.snd (v ab))

@[simp] theorem eval_e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) (ρ : Env Γ) :
    (e2eSidEqE a b).eval ρ = (sidOfV (a.eval ρ) == sidOfV (b.eval ρ)) := by
  simp [e2eSidEqE, eLet, v, Ext.wk, Ext.refl, Expr.eval, Env.get,
    eval_sidEqE (I₀ := e2eSessionTargetIface ℓ)]

theorem exprCostUB_e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) :
    exprCostUB (e2eSidEqE a b) ≤ exprCostUB a + exprCostUB b + 800 := by
  simp only [e2eSidEqE, sidEqE, PqxdhSimTypes.nat4EqE, PqxdhSimTypes.nat3EqE,
    PqxdhSimTypes.nat2EqE, PqxdhSimTypes.sidKeyE, PqxdhSimTypes.finValE,
    mkStepAPqxdhHooks, eLet, eCaseSum, exprCostUB, exprCostUB_v,
    PqxdhSimTypes.exprCostUB_e2ePureOp, E2EPureOp.cost,
    bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
  omega

theorem cost_e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) :
    (e2eSidEqE a b).cost ≤ a.cost + b.cost + 280 := by
  simp only [e2eSidEqE, sidEqE, PqxdhSimTypes.nat4EqE, PqxdhSimTypes.nat3EqE,
    PqxdhSimTypes.nat2EqE, PqxdhSimTypes.sidKeyE, PqxdhSimTypes.finValE,
    mkStepAPqxdhHooks, eLet, eCaseSum, v, Ext.wk, Ext.refl, Expr.cost, cost_e2ePureOp,
    E2EPureOp.cost, bits, show Nat.log 2 0 = 0 from rfl, show Nat.log 2 1 = 0 from rfl,
    show Nat.log 2 2 = 1 from rfl, show Nat.log 2 3 = 1 from rfl,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem size_e2eSidEqE {Γ} (a b : E2EExpr Γ (sidT S)) :
    (e2eSidEqE a b).size ≤ a.size + b.size + 800 := by
  simp only [e2eSidEqE, sidEqE, PqxdhSimTypes.nat4EqE, PqxdhSimTypes.nat3EqE,
    PqxdhSimTypes.nat2EqE, PqxdhSimTypes.sidKeyE, PqxdhSimTypes.finValE,
    mkStepAPqxdhHooks, eLet, eCaseSum, Expr.size, size_v, size_e2ePureOp, E2EPureOp.opSize,
    bits_zero, bits_one, bits_two, bits_three, Nat.reduceAdd]
  omega

attribute [local irreducible] e2eSidEqE

def kqR1 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := sumRight? kq
def kqR2 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR1 kq)
def kqR3 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR2 kq)
def kqR4 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR3 kq)
def kqR5 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR4 kq)
def kqR6 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR5 kq)
def kqR7 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR6 kq)
def kqR8 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR7 kq)
def kqR9 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR8 kq)
def kqR10 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR9 kq)
def kqR11 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR10 kq)
def kqR12 {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR11 kq)

def kqAsInitPrin? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := sumLeft? kq
def kqAsCorruptIK? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR1 kq)
def kqAsGenSPK? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR2 kq)
def kqAsGenOPK? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR3 kq)
def kqAsInitiateOPK? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR4 kq)
def kqAsInitiateNoOPK? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR5 kq)
def kqAsAcceptOPK? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR6 kq)
def kqAsAcceptNoOPK? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR7 kq)
def kqAsTestSession? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR8 kq)
def kqAsRevealDhSecrets? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumLeft? (kqR10 kq)
def kqAsRevealSpkSk? {Γ} (kq : E2EExpr Γ (keyIndQT S)) := optSumRight? (kqR12 kq)

def krR1 {Γ} (kr : E2EExpr Γ keyIndRT) := sumRight? kr
def krR2 {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR1 kr)
def krR3 {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR2 kr)
def krR4 {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR3 kr)
def krR5 {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR4 kr)
def krR6 {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR5 kr)
def krR7 {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR6 kr)
def krR8 {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR7 kr)
def krR9 {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR8 kr)

def krAsInitPrinResp? {Γ} (kr : E2EExpr Γ keyIndRT) := optSumLeft? (krR1 kr)
def krAsPkResp? {Γ} (kr : E2EExpr Γ keyIndRT) := optSumLeft? (krR2 kr)
def krAsCorrResp? {Γ} (kr : E2EExpr Γ keyIndRT) := optSumLeft? (krR3 kr)
def krAsBundleResp? {Γ} (kr : E2EExpr Γ keyIndRT) := optSumLeft? (krR4 kr)
def krAsHdrResp? {Γ} (kr : E2EExpr Γ keyIndRT) := optSumLeft? (krR5 kr)
def krAsSpkSkResp? {Γ} (kr : E2EExpr Γ keyIndRT) := optSumRight? (krR9 kr)

private theorem eval_kqAsInitPrin? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsInitPrin? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with | .initPrin u => some u | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsInitPrin?, eval_sumLeft?, hq, keyIndQdec_keyIndQenc]; cases q <;> rfl

private theorem eval_kqAsCorruptIK? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsCorruptIK? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with | .corruptIK u => some u | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsCorruptIK?, kqR1, eval_optSumLeft?, eval_sumRight?, hq, keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsGenSPK? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsGenSPK? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with | .genSPK u j => some (u, j) | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsGenSPK?, kqR2, kqR1, eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hq,
    keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsGenOPK? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsGenOPK? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with | .genOPK u j o => some (u, (j, o)) | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsGenOPK?, kqR3, kqR2, kqR1, eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hq,
    keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsInitiateOPK? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsInitiateOPK? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with
      | .initiateOPK u i bnd => some (u, (i, bundleV bnd)) | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsInitiateOPK?, kqR4, kqR3, kqR2, kqR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hq, keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsInitiateNoOPK? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsInitiateNoOPK? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with
      | .initiateNoOPK u i bnd => some (u, (i, bundleV bnd)) | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsInitiateNoOPK?, kqR5, kqR4, kqR3, kqR2, kqR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hq, keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsAcceptOPK? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsAcceptOPK? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with
      | .acceptOPK u j o hdr => some (u, (j, (o, hdrV hdr))) | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsAcceptOPK?, kqR6, kqR5, kqR4, kqR3, kqR2, kqR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hq, keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsAcceptNoOPK? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsAcceptNoOPK? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with
      | .acceptNoOPK u j m hdr => some (u, (j, (m, hdrV hdr))) | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsAcceptNoOPK?, kqR7, kqR6, kqR5, kqR4, kqR3, kqR2, kqR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hq, keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsTestSession? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsTestSession? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with | .testSession sid => some (sidV sid) | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsTestSession?, kqR8, kqR7, kqR6, kqR5, kqR4, kqR3, kqR2, kqR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hq, keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsRevealDhSecrets? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsRevealDhSecrets? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with | .revealDhSecrets => some () | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsRevealDhSecrets?, kqR10, kqR9, kqR8, kqR7, kqR6, kqR5, kqR4, kqR3, kqR2, kqR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hq, keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_kqAsRevealSpkSk? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAsRevealSpkSk? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with | .revealSpkSk u j => some (u, j) | _ => none := by
  set q := keyIndQdec (kqE.eval ρ)
  have hq : kqE.eval ρ = keyIndQenc q := (keyIndQenc_keyIndQdec (kqE.eval ρ)).symm
  simp only [kqAsRevealSpkSk?, kqR12, kqR11, kqR10, kqR9, kqR8, kqR7, kqR6,
    kqR5, kqR4, kqR3, kqR2, kqR1, eval_optSumRight?, eval_sumRight?, hq, keyIndQdec_keyIndQenc]
  cases q <;> rfl

private theorem eval_krAsInitPrinResp? {Γ} (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ) :
    (krAsInitPrinResp? krE).eval ρ =
      match keyIndRdec (krE.eval ρ) with
      | .initPrinResp ikPk ikSignPk => some (ikPk, ikSignPk) | _ => none := by
  set r := keyIndRdec (krE.eval ρ)
  have hr : krE.eval ρ = keyIndRenc r := (keyIndRenc_keyIndRdec (krE.eval ρ)).symm
  simp only [krAsInitPrinResp?, krR1, eval_optSumLeft?, eval_sumRight?, hr, keyIndRdec_keyIndRenc]
  cases r <;> rfl

private theorem eval_krAsPkResp? {Γ} (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ) :
    (krAsPkResp? krE).eval ρ =
      match keyIndRdec (krE.eval ρ) with | .pkResp pk => some pk | _ => none := by
  set r := keyIndRdec (krE.eval ρ)
  have hr : krE.eval ρ = keyIndRenc r := (keyIndRenc_keyIndRdec (krE.eval ρ)).symm
  simp only [krAsPkResp?, krR2, krR1, eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hr,
    keyIndRdec_keyIndRenc]
  cases r <;> rfl

private theorem eval_krAsCorrResp? {Γ} (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ) :
    (krAsCorrResp? krE).eval ρ =
      match keyIndRdec (krE.eval ρ) with
      | .corrResp ik0 ikSign => some (ik0, ikSign) | _ => none := by
  set r := keyIndRdec (krE.eval ρ)
  have hr : krE.eval ρ = keyIndRenc r := (keyIndRenc_keyIndRdec (krE.eval ρ)).symm
  simp only [krAsCorrResp?, krR3, krR2, krR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hr, keyIndRdec_keyIndRenc]
  cases r <;> rfl

private theorem eval_krAsBundleResp? {Γ} (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ) :
    (krAsBundleResp? krE).eval ρ =
      match keyIndRdec (krE.eval ρ) with
      | .bundleResp bnd => some (bundleV bnd) | _ => none := by
  set r := keyIndRdec (krE.eval ρ)
  have hr : krE.eval ρ = keyIndRenc r := (keyIndRenc_keyIndRdec (krE.eval ρ)).symm
  simp only [krAsBundleResp?, krR4, krR3, krR2, krR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hr, keyIndRdec_keyIndRenc]
  cases r <;> rfl

private theorem eval_krAsHdrResp? {Γ} (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ) :
    (krAsHdrResp? krE).eval ρ =
      match keyIndRdec (krE.eval ρ) with
      | .hdrResp hdr => some (hdrV hdr) | _ => none := by
  set r := keyIndRdec (krE.eval ρ)
  have hr : krE.eval ρ = keyIndRenc r := (keyIndRenc_keyIndRdec (krE.eval ρ)).symm
  simp only [krAsHdrResp?, krR5, krR4, krR3, krR2, krR1,
    eval_optSumLeft?, eval_optSumRight?, eval_sumRight?, hr, keyIndRdec_keyIndRenc]
  cases r <;> rfl

private theorem eval_krAsSpkSkResp? {Γ} (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ) :
    (krAsSpkSkResp? krE).eval ρ =
      match keyIndRdec (krE.eval ρ) with | .spkSkResp sk => some sk | _ => none := by
  set r := keyIndRdec (krE.eval ρ)
  have hr : krE.eval ρ = keyIndRenc r := (keyIndRenc_keyIndRdec (krE.eval ρ)).symm
  simp only [krAsSpkSkResp?, krR9, krR8, krR7, krR6, krR5, krR4, krR3, krR2, krR1,
    eval_optSumRight?, eval_sumRight?, hr, keyIndRdec_keyIndRenc]
  cases r <;> rfl

def bhDrvAcceptIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (hdrE : E2EExpr Γ hdrT) : E2EExpr Γ .bool :=
  eLet (.pair (mbPrins dsE) (hdrIkA hdrE)) fun p =>
    eAny nPrins (.fst (v p)) fun e =>
      e2ePureOp (.pbytesEq 32 32) (.pair (.snd (v e)) (.snd (v p)))

theorem eval_bhDrvAcceptIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (hdrE : E2EExpr Γ hdrT) (ρ : Env Γ)
    {ds : ModelDriverBase S}
    (hds : dsE.eval ρ = e2eMirrorBaseEnc ds) (hlen : ds.prins.length ≤ nPrins) :
    (bhDrvAcceptIkOkE nPrins dsE hdrE).eval ρ =
      bhDrvAcceptIkOk ds (hdrOfV (hdrE.eval ρ)) := by
  set hdr := hdrOfV (hdrE.eval ρ)
  have hhdr : hdrE.eval ρ = hdrV hdr := (hdrV_hdrOfV (hdrE.eval ρ)).symm
  simp [bhDrvAcceptIkOkE, bhDrvAcceptIkOk, eLet, eAny, mbPrins, hdrIkA, hdrV, e2eMirrorBaseEnc,
    v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get,
    hds, hhdr, List.take_of_length_le hlen]

theorem exprCostUB_bhDrvAcceptIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (hdrE : E2EExpr Γ hdrT) :
    exprCostUB (bhDrvAcceptIkOkE nPrins dsE hdrE) ≤
      exprCostUB dsE + exprCostUB hdrE + 80 * nPrins + 16 := by
  simp only [bhDrvAcceptIkOkE, mbPrins, hdrIkA, eLet, eAny, exprCostUB, exprCostUB_v,
    PqxdhSimTypes.exprCostUB_e2ePureOp, E2EPureOp.cost, pnat32_val, Nat.reduceAdd]
  omega

theorem cost_bhDrvAcceptIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (hdrE : E2EExpr Γ hdrT) :
    (bhDrvAcceptIkOkE nPrins dsE hdrE).cost ≤ dsE.cost + hdrE.cost + 80 * nPrins + 16 := by
  simp only [bhDrvAcceptIkOkE, mbPrins, hdrIkA, eLet, eAny, v, Ext.wk, Ext.refl, Ext.step,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost, pnat32_val, Nat.reduceAdd]
  omega

theorem size_bhDrvAcceptIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (hdrE : E2EExpr Γ hdrT) :
    (bhDrvAcceptIkOkE nPrins dsE hdrE).size ≤ dsE.size + hdrE.size + bits nPrins + 24 := by
  simp only [bhDrvAcceptIkOkE, mbPrins, hdrIkA, eLet, eAny, Expr.size, size_v,
    size_e2ePureOp, E2EPureOp.opSize, Nat.reduceAdd]
  omega

attribute [local irreducible] bhDrvAcceptIkOkE

def bhDrvInitiateIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (bndE : E2EExpr Γ bundleT) : E2EExpr Γ .bool :=
  eLet (.pair (mbPrins dsE) (.pair (bndIkB bndE) (e2eCryptoOp .pow8 (bndIkB bndE)))) fun p =>
    .not (eAny nPrins (.fst (v p)) fun e =>
      .and
        (e2ePureOp (.pbytesEq 32 32)
          (.pair (e2eCryptoOp .pow8 (.snd (v e))) (.snd (.snd (v p)))))
        (.not (e2ePureOp (.pbytesEq 32 32)
          (.pair (.snd (v e)) (.fst (.snd (v p)))))))

theorem eval_bhDrvInitiateIkOkE (nPrins : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (bndE : E2EExpr Γ bundleT) (ρ : Env Γ)
    {ds : ModelDriverBase S}
    (hds : dsE.eval ρ = e2eMirrorBaseEnc ds) (hlen : ds.prins.length ≤ nPrins) :
    (bhDrvInitiateIkOkE nPrins dsE bndE).eval ρ =
      bhDrvInitiateIkOk P ds (bundleOfV (bndE.eval ρ)) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbnd : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  have hpBnd := e2eCryptoOps_eval_pow8_lossless ℓ hP C K bnd.ikB
  dsimp only [e2eCryptoOps] at hpBnd
  simp only [bhDrvInitiateIkOkE, bhDrvInitiateIkOk, eLet, eAny, mbPrins, bndIkB, bundleV,
    e2eMirrorBaseEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    eval_e2eCryptoOp, Env.get, hds, hbnd, hpBnd, List.take_of_length_le hlen]
  congr 1
  apply List.any_congr rfl
  rintro ⟨_, pk⟩
  have hpPk := e2eCryptoOps_eval_pow8_lossless ℓ hP C K pk
  dsimp only [e2eCryptoOps] at hpPk
  simp [hpPk, bne]

theorem exprCostUB_bhDrvInitiateIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (bndE : E2EExpr Γ bundleT) :
    exprCostUB (bhDrvInitiateIkOkE nPrins dsE bndE) ≤
      exprCostUB dsE + 2 * exprCostUB bndE + 168 * nPrins + 28 := by
  simp only [bhDrvInitiateIkOkE, mbPrins, bndIkB, eLet, eAny, exprCostUB, exprCostUB_v,
    PqxdhSimTypes.exprCostUB_e2ePureOp, PqxdhSimTypes.exprCostUB_e2eCryptoOp,
    E2EPureOp.cost, E2ECryptoOp.cost, pnat32_val, Nat.reduceAdd]
  omega

theorem cost_bhDrvInitiateIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (bndE : E2EExpr Γ bundleT) :
    (bhDrvInitiateIkOkE nPrins dsE bndE).cost ≤
      dsE.cost + 2 * bndE.cost + 168 * nPrins + 28 := by
  simp only [bhDrvInitiateIkOkE, mbPrins, bndIkB, eLet, eAny, v, Ext.wk, Ext.refl, Ext.step,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost, cost_e2eCryptoOp, E2ECryptoOp.cost,
    pnat32_val, Nat.reduceAdd]
  omega

theorem size_bhDrvInitiateIkOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (bndE : E2EExpr Γ bundleT) :
    (bhDrvInitiateIkOkE nPrins dsE bndE).size ≤
      dsE.size + 2 * bndE.size + bits nPrins + 36 := by
  simp only [bhDrvInitiateIkOkE, mbPrins, bndIkB, eLet, eAny, Expr.size, size_v,
    size_e2ePureOp, E2EPureOp.opSize, size_e2eCryptoOp, Nat.reduceAdd]
  omega

attribute [local irreducible] bhDrvInitiateIkOkE

def kqAcceptHdr? {Γ} (kq : E2EExpr Γ (keyIndQT S)) : E2EExpr Γ (.opt hdrT) :=
  eLet kq fun q =>
    eCaseOpt (kqAsAcceptOPK? (v q))
      (optMapE (kqAsAcceptNoOPK? (v q)) fun x => .snd (.snd (.snd (v x))))
      (fun x => .some (.snd (.snd (.snd (v x)))))

private theorem eval_kqAcceptHdr? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqAcceptHdr? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with
      | .acceptOPK _ _ _ hdr => some (hdrV hdr)
      | .acceptNoOPK _ _ _ hdr => some (hdrV hdr)
      | _ => none := by
  simp only [kqAcceptHdr?, eLet, eCaseOpt, eval_optMapE, Expr.eval]
  rw [eval_kqAsAcceptOPK?, eval_kqAsAcceptNoOPK?]
  have hv : (v (O := e2eOps ℓ P C K decT encT) (.zero : Var (keyIndQT S :: Γ) (keyIndQT S))).eval
      (.cons (kqE.eval ρ) ρ) = kqE.eval ρ := rfl
  rw [hv]
  cases keyIndQdec (kqE.eval ρ) <;> simp [v, Ext.wk, Ext.refl, Expr.eval, Env.get]

def bhDrvKiQueryOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) : E2EExpr Γ .bool :=
  eLet (.pair dsE kqE) fun dq =>
    .ite (orE (isSomeE (kqAsTestSession? (.snd (v dq))))
              (isSomeE (kqAsRevealDhSecrets? (.snd (v dq)))))
      (.bool false)
      (eCaseOpt (kqAsInitiateOPK? (.snd (v dq)))
        (eCaseOpt (kqAsInitiateNoOPK? (.snd (v dq)))
          (eCaseOpt (kqAcceptHdr? (.snd (v dq)))
            (.bool true)
            (fun hdr => bhDrvAcceptIkOkE nPrins (.fst (v dq)) (v hdr)))
          (fun uib => .and (isNoneE (bndOpkB (.snd (.snd (v uib)))))
            (bhDrvInitiateIkOkE nPrins (.fst (v dq)) (.snd (.snd (v uib))))))
        (fun uib => .and (isSomeE (bndOpkB (.snd (.snd (v uib)))))
          (bhDrvInitiateIkOkE nPrins (.fst (v dq)) (.snd (.snd (v uib))))))

theorem eval_bhDrvKiQueryOkE (nPrins : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ)
    {ds : ModelDriverBase S}
    (hds : dsE.eval ρ = e2eMirrorBaseEnc ds) (hlen : ds.prins.length ≤ nPrins) :
    (bhDrvKiQueryOkE nPrins dsE kqE).eval ρ =
      bhDrvKiQueryOk P ds (keyIndQdec (kqE.eval ρ)) := by
  set ρ1 : Env ((e2eMirrorBaseTy S ℓ).prod (keyIndQT S) :: Γ) :=
    .cons (dsE.eval ρ, kqE.eval ρ) ρ
  have hq1 : (ρ1.get .zero).2 = kqE.eval ρ := rfl
  simp only [bhDrvKiQueryOkE, eLet, Expr.eval, eval_orE, eval_isSomeE]
  change (if ((kqAsTestSession? _).eval ρ1).isSome || ((kqAsRevealDhSecrets? _).eval ρ1).isSome then
      false else _) = _
  rw [eval_kqAsTestSession?, eval_kqAsRevealDhSecrets?]
  simp only [eCaseOpt, Expr.eval]
  rw [eval_kqAsInitiateOPK?, eval_kqAsInitiateNoOPK?, eval_kqAcceptHdr?]
  simp only [v, Ext.wk, Ext.refl, Expr.eval, Env.get, hq1]
  cases keyIndQdec (kqE.eval ρ) with
  | initiateOPK u i bnd =>
    simp only [bhDrvKiQueryOk, Option.isSome, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      Expr.eval, eval_isSomeE, bndOpkB, v, Ext.wk, Ext.refl, Ext.step, Env.get]
    rw [eval_bhDrvInitiateIkOkE nPrins hP _ _ _ (by simp [ρ1, Expr.eval, Env.get, hds]) hlen]
    cases bnd; rfl
  | initiateNoOPK u i bnd =>
    simp only [bhDrvKiQueryOk, Option.isSome, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      Expr.eval, eval_isNoneE, bndOpkB, v, Ext.wk, Ext.refl, Ext.step, Env.get]
    rw [eval_bhDrvInitiateIkOkE nPrins hP _ _ _ (by simp [ρ1, Expr.eval, Env.get, hds]) hlen]
    cases bnd; rfl
  | acceptOPK u j o hdr =>
    simp only [bhDrvKiQueryOk, Option.isSome, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      Expr.eval, v, Ext.wk, Ext.refl, Ext.step, Env.get]
    rw [eval_bhDrvAcceptIkOkE nPrins _ _ _ (by simp [ρ1, Expr.eval, Env.get, hds]) hlen]
    simp [Expr.eval, Env.get, hdrOfV_hdrV]
  | acceptNoOPK u j m hdr =>
    simp only [bhDrvKiQueryOk, Option.isSome, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      Expr.eval, v, Ext.wk, Ext.refl, Ext.step, Env.get]
    rw [eval_bhDrvAcceptIkOkE nPrins _ _ _ (by simp [ρ1, Expr.eval, Env.get, hds]) hlen]
    simp [Expr.eval, Env.get, hdrOfV_hdrV]
  | _ =>
    simp [bhDrvKiQueryOk]

theorem exprCostUB_bhDrvKiQueryOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) :
    exprCostUB (bhDrvKiQueryOkE nPrins dsE kqE) ≤
      exprCostUB dsE + exprCostUB kqE + 416 * nPrins + 600 := by
  let Δ0 := (e2eMirrorBaseTy S ℓ).prod (keyIndQT S) :: Γ
  let uibOpkT : Ty (e2eSig ℓ) := (FinT S.N_id).prod ((FinT S.N_send_opk).prod bundleT)
  let uibNoOpkT : Ty (e2eSig ℓ) := (FinT S.N_id).prod ((FinT S.N_send_no_opk).prod bundleT)
  have hAcc := exprCostUB_bhDrvAcceptIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := hdrT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.var .zero)
  have hInit1 := exprCostUB_bhDrvInitiateIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := uibOpkT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.snd (.snd (.var .zero)))
  have hInit2 := exprCostUB_bhDrvInitiateIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := uibNoOpkT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.snd (.snd (.var .zero)))
  simp only [exprCostUB, Nat.reduceAdd] at hAcc hInit1 hInit2
  unfold bhDrvKiQueryOkE
  simp only [kqAcceptHdr?, kqAsTestSession?, kqAsRevealDhSecrets?, kqAsInitiateOPK?,
    kqAsInitiateNoOPK?, kqAsAcceptOPK?, kqAsAcceptNoOPK?,
    kqR1, kqR2, kqR3, kqR4, kqR5, kqR6, kqR7, kqR8, kqR9, kqR10,
    exprCostUB_sumRight?, exprCostUB_optSumLeft?, exprCostUB_optSumRight?,
    orE, isSomeE, isNoneE, optMapE, bndOpkB, v, Ext.wk, Ext.refl, Ext.step,
    eLet, eCaseOpt, exprCostUB, exprCostUB_v0, Nat.reduceAdd]
  omega

theorem cost_bhDrvKiQueryOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) :
    (bhDrvKiQueryOkE nPrins dsE kqE).cost ≤ dsE.cost + kqE.cost + 168 * nPrins + 500 := by
  let Δ0 := (e2eMirrorBaseTy S ℓ).prod (keyIndQT S) :: Γ
  let uibOpkT : Ty (e2eSig ℓ) := (FinT S.N_id).prod ((FinT S.N_send_opk).prod bundleT)
  let uibNoOpkT : Ty (e2eSig ℓ) := (FinT S.N_id).prod ((FinT S.N_send_no_opk).prod bundleT)
  have hAcc := cost_bhDrvAcceptIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := hdrT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.var .zero)
  have hInit1 := cost_bhDrvInitiateIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := uibOpkT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.snd (.snd (.var .zero)))
  have hInit2 := cost_bhDrvInitiateIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := uibNoOpkT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.cost, Nat.reduceAdd] at hAcc hInit1 hInit2
  unfold bhDrvKiQueryOkE
  simp only [kqAcceptHdr?, kqAsTestSession?, kqAsRevealDhSecrets?, kqAsInitiateOPK?,
    kqAsInitiateNoOPK?, kqAsAcceptOPK?, kqAsAcceptNoOPK?,
    kqR1, kqR2, kqR3, kqR4, kqR5, kqR6, kqR7, kqR8, kqR9, kqR10,
    cost_sumRight?, cost_optSumLeft?, cost_optSumRight?,
    orE, isSomeE, isNoneE, optMapE, bndOpkB,
    eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, Expr.cost, Expr.v0, Nat.reduceAdd]
  omega

theorem size_bhDrvKiQueryOkE (nPrins : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) :
    (bhDrvKiQueryOkE nPrins dsE kqE).size ≤
      dsE.size + kqE.size + 3 * bits nPrins + 620 := by
  let Δ0 := (e2eMirrorBaseTy S ℓ).prod (keyIndQT S) :: Γ
  let uibOpkT : Ty (e2eSig ℓ) := (FinT S.N_id).prod ((FinT S.N_send_opk).prod bundleT)
  let uibNoOpkT : Ty (e2eSig ℓ) := (FinT S.N_id).prod ((FinT S.N_send_no_opk).prod bundleT)
  have hAcc := size_bhDrvAcceptIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := hdrT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.var .zero)
  have hInit1 := size_bhDrvInitiateIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := uibOpkT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.snd (.snd (.var .zero)))
  have hInit2 := size_bhDrvInitiateIkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := uibNoOpkT :: Δ0) nPrins
    (.fst (.var (.succ .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.size, Nat.reduceAdd] at hAcc hInit1 hInit2
  unfold bhDrvKiQueryOkE
  simp only [kqAcceptHdr?, kqAsTestSession?, kqAsRevealDhSecrets?, kqAsInitiateOPK?,
    kqAsInitiateNoOPK?, kqAsAcceptOPK?, kqAsAcceptNoOPK?,
    kqR1, kqR2, kqR3, kqR4, kqR5, kqR6, kqR7, kqR8, kqR9, kqR10,
    size_sumRight?, size_optSumLeft?, size_optSumRight?,
    orE, isSomeE, isNoneE, optMapE, bndOpkB, v, Ext.wk, Ext.refl, Ext.step,
    eLet, eCaseOpt, Expr.size, Expr.v0, Nat.reduceAdd]
  omega

attribute [local irreducible] bhDrvKiQueryOkE

def bhNoOpkRespPromotedE (qStart : ℕ) {Γ}
    (metaE : E2EExpr Γ (.list (e2eInstMetaTy S ℓ)))
    (uE : E2EExpr Γ (FinT S.N_id)) : E2EExpr Γ .bool :=
  eLet (.pair metaE uE) fun p =>
    eAny qStart (.fst (v p)) fun im =>
      .and
        (eCaseOpt (imRespPrin (v im))
          (.bool false)
          (fun rp => e2ePureOp (.finEq S.N_id) (.pair (v rp) (.snd (v p)))))
        (isNoneE (imOpkId (v im)))

theorem eval_bhNoOpkRespPromotedE (qStart : ℕ) {Γ}
    (metaE : E2EExpr Γ (.list (e2eInstMetaTy S ℓ)))
    (uE : E2EExpr Γ (FinT S.N_id)) (ρ : Env Γ)
    {instMeta : List (ModelDriverInstanceMeta S)} {u : Fin S.N_id}
    (hm : metaE.eval ρ = instMeta.map (e2eInstMetaEnc (ℓ := ℓ)))
    (hu : uE.eval ρ = u)
    (hlen : instMeta.length ≤ qStart) :
    (bhNoOpkRespPromotedE qStart metaE uE).eval ρ = bhNoOpkRespPromoted instMeta u := by
  have hmap_len : (instMeta.map (e2eInstMetaEnc (ℓ := ℓ))).length ≤ qStart := by
    simpa [List.length_map] using hlen
  simp only [bhNoOpkRespPromotedE, bhNoOpkRespPromoted, eLet, eAny, eCaseOpt,
    imRespPrin, imOpkId, v, Ext.wk, Ext.refl, Ext.step,
    Expr.eval, eval_isNoneE, eval_e2ePureOp, E2EPureOp.eval, Env.get, hm, hu,
    List.take_of_length_le hmap_len, List.any_map]
  apply List.any_congr rfl
  intro im
  rcases im with ⟨_, _, _ | rp, _, _ | opk⟩ <;> rfl

theorem exprCostUB_bhNoOpkRespPromotedE (qStart : ℕ) {Γ}
    (metaE : E2EExpr Γ (.list (e2eInstMetaTy S ℓ)))
    (uE : E2EExpr Γ (FinT S.N_id)) :
    exprCostUB (bhNoOpkRespPromotedE qStart metaE uE) ≤
      exprCostUB metaE + exprCostUB uE + 24 * qStart + 10 := by
  unfold bhNoOpkRespPromotedE
  simp only [eLet, eAny, eCaseOpt, imRespPrin, imOpkId, isNoneE,
    v, Ext.wk, Ext.refl, Ext.step, exprCostUB, exprCostUB_v0,
    PqxdhSimTypes.exprCostUB_e2ePureOp, E2EPureOp.cost, Nat.reduceAdd]
  omega

theorem cost_bhNoOpkRespPromotedE (qStart : ℕ) {Γ}
    (metaE : E2EExpr Γ (.list (e2eInstMetaTy S ℓ)))
    (uE : E2EExpr Γ (FinT S.N_id)) :
    (bhNoOpkRespPromotedE qStart metaE uE).cost ≤
      metaE.cost + uE.cost + 24 * qStart + 10 := by
  unfold bhNoOpkRespPromotedE
  simp only [eLet, eAny, eCaseOpt, imRespPrin, imOpkId, isNoneE,
    v, Ext.wk, Ext.refl, Ext.step, Expr.cost, Expr.v0,
    cost_e2ePureOp, E2EPureOp.cost, Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem size_bhNoOpkRespPromotedE (qStart : ℕ) {Γ}
    (metaE : E2EExpr Γ (.list (e2eInstMetaTy S ℓ)))
    (uE : E2EExpr Γ (FinT S.N_id)) :
    (bhNoOpkRespPromotedE qStart metaE uE).size ≤
      metaE.size + uE.size + bits qStart + 32 := by
  unfold bhNoOpkRespPromotedE
  simp only [eLet, eAny, eCaseOpt, imRespPrin, imOpkId, isNoneE,
    Expr.size, Expr.v0, size_v, size_e2ePureOp, E2EPureOp.opSize, Nat.reduceAdd]
  omega

attribute [local irreducible] bhNoOpkRespPromotedE

/-- Driver-state `KeyIndQuery` admissibility filter over `e2eDrvStateTy S ℓ`. -/
def kiQueryOkE (nPrins qStart : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) : E2EExpr Γ .bool :=
  eLet (.pair σE kqE) fun p =>
    .and
      (bhDrvKiQueryOkE nPrins (drvBase (.fst (v p))) (.snd (v p)))
      (eCaseOpt (kqAsCorruptIK? (.snd (v p)))
        (.bool true)
        (fun u => .not (bhNoOpkRespPromotedE qStart (drvInstMeta (.fst (v p))) (v u))))

theorem eval_kiQueryOkE (nPrins qStart : ℕ)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {kq : SignalPqxdh.KeyIndQuery S}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hkq : kqE.eval ρ = keyIndQenc kq)
    (hlen : σ.prins.length ≤ nPrins) (hMeta : σ.instMeta.length ≤ qStart) :
    (kiQueryOkE nPrins qStart σE kqE).eval ρ =
      (bhDrvKiQueryOk P σ.toModelDriverBase kq &&
        !(match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false)) := by
  set ρ1 : Env ((e2eDrvStateTy S ℓ).prod (keyIndQT S) :: Γ) :=
    .cons (σE.eval ρ, kqE.eval ρ) ρ
  simp only [kiQueryOkE, eLet, Expr.eval]
  rw [eval_bhDrvKiQueryOkE nPrins hP _ _ ρ1
    (by simp [ρ1, drvBase, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hσ, e2eDrvStateEnc]) hlen]
  simp only [eCaseOpt, Expr.eval]
  rw [eval_kqAsCorruptIK?]
  simp only [ρ1, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hkq, keyIndQdec_keyIndQenc]
  cases kq with
  | corruptIK u =>
    simp only [Expr.eval, v, Ext.wk, Ext.refl, Ext.step, Env.get]
    rw [eval_bhNoOpkRespPromotedE qStart _ _ _
      (by simp [drvInstMeta, Expr.eval, Env.get, hσ, e2eDrvStateEnc]) (u := u) rfl hMeta]
  | _ =>
    simp

theorem exprCostUB_kiQueryOkE (nPrins qStart : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) :
    exprCostUB (kiQueryOkE nPrins qStart σE kqE) ≤
      exprCostUB σE + exprCostUB kqE + 416 * nPrins + 24 * qStart + 660 := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (keyIndQT S) :: Γ
  have h1 := exprCostUB_bhDrvKiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nPrins
    (drvBase (.fst (.var .zero))) (.snd (.var .zero))
  have h2 := exprCostUB_bhNoOpkRespPromotedE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := FinT S.N_id :: Δ0) qStart
    (drvInstMeta (.fst (.var (.succ .zero)))) (.var .zero)
  simp only [drvBase, drvInstMeta, exprCostUB, Nat.reduceAdd] at h1 h2
  unfold kiQueryOkE
  simp only [drvBase, drvInstMeta, kqAsCorruptIK?, kqR1, exprCostUB_optSumLeft?, exprCostUB_sumRight?,
    eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, exprCostUB, exprCostUB_v0, Nat.reduceAdd]
  omega

theorem cost_kiQueryOkE (nPrins qStart : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) :
    (kiQueryOkE nPrins qStart σE kqE).cost ≤
      σE.cost + kqE.cost + 168 * nPrins + 24 * qStart + 560 := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (keyIndQT S) :: Γ
  have h1 := cost_bhDrvKiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nPrins
    (drvBase (.fst (.var .zero))) (.snd (.var .zero))
  have h2 := cost_bhNoOpkRespPromotedE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := FinT S.N_id :: Δ0) qStart
    (drvInstMeta (.fst (.var (.succ .zero)))) (.var .zero)
  simp only [drvBase, drvInstMeta, Expr.cost, Nat.reduceAdd] at h1 h2
  unfold kiQueryOkE
  simp only [drvBase, drvInstMeta, kqAsCorruptIK?, kqR1, cost_optSumLeft?, cost_sumRight?,
    eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, Expr.cost, Expr.v0, Nat.reduceAdd]
  omega

theorem size_kiQueryOkE (nPrins qStart : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (kqE : E2EExpr Γ (keyIndQT S)) :
    (kiQueryOkE nPrins qStart σE kqE).size ≤
      σE.size + kqE.size + 3 * bits nPrins + bits qStart + 720 := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (keyIndQT S) :: Γ
  have h1 := size_bhDrvKiQueryOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ0) nPrins
    (drvBase (.fst (.var .zero))) (.snd (.var .zero))
  have h2 := size_bhNoOpkRespPromotedE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := FinT S.N_id :: Δ0) qStart
    (drvInstMeta (.fst (.var (.succ .zero)))) (.var .zero)
  simp only [drvBase, drvInstMeta, Expr.size, Nat.reduceAdd] at h1 h2
  unfold kiQueryOkE
  simp only [drvBase, drvInstMeta, kqAsCorruptIK?, kqR1, size_optSumLeft?, size_sumRight?,
    eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, Expr.size, Expr.v0, Nat.reduceAdd]
  omega

attribute [local irreducible] kiQueryOkE

def kqInitSend? {Γ} (kq : E2EExpr Γ (keyIndQT S)) :
    E2EExpr Γ (.opt (.prod (sidT S) bundleT)) :=
  eLet kq fun q =>
    eCaseOpt (kqAsInitiateOPK? (v q))
      (optMapE (kqAsInitiateNoOPK? (v q)) fun uib =>
        .pair (.inr (.inl (.pair (.fst (v uib)) (.fst (.snd (v uib))))))
              (.snd (.snd (v uib))))
      (fun uib =>
        .some (.pair (.inl (.pair (.fst (v uib)) (.fst (.snd (v uib)))))
                     (.snd (.snd (v uib)))))

private theorem eval_kqInitSend? {Γ} (kqE : E2EExpr Γ (keyIndQT S)) (ρ : Env Γ) :
    (kqInitSend? kqE).eval ρ =
      match keyIndQdec (kqE.eval ρ) with
      | .initiateOPK u i bnd => some (sidV (.sendOPK u i), bundleV bnd)
      | .initiateNoOPK u i bnd => some (sidV (.sendNoOPK u i), bundleV bnd)
      | _ => none := by
  simp only [kqInitSend?, eLet, eCaseOpt, eval_optMapE, Expr.eval]
  rw [eval_kqAsInitiateOPK?, eval_kqAsInitiateNoOPK?]
  have hv : (v (O := e2eOps ℓ P C K decT encT) (.zero : Var (keyIndQT S :: Γ) (keyIndQT S))).eval
      (.cons (kqE.eval ρ) ρ) = kqE.eval ρ := rfl
  rw [hv]
  cases keyIndQdec (kqE.eval ρ) <;> simp [sidV, v, Ext.wk, Ext.refl, Expr.eval, Env.get]

def bhBaseMirrorE {Γ} (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) :
    E2EExpr Γ (e2eMirrorBaseTy S ℓ) :=
  eLet (.pair dsE (.pair kqE krE)) fun p =>
    .pair
      (eCaseOpt (optZipE (kqAsInitPrin? (.fst (.snd (v p))))
                         (krAsInitPrinResp? (.snd (.snd (v p)))))
        (mbPrins (.fst (v p)))
        (fun uik => .cons (.pair (.fst (v uik)) (.fst (.snd (v uik))))
                          (mbPrins (.fst (v p)))))
      (.pair
        (eCaseOpt (optZipE (kqAsGenSPK? (.fst (.snd (v p))))
                           (krAsBundleResp? (.snd (.snd (v p)))))
          (mbBundles (.fst (v p)))
          (fun ujb => .cons (.pair (.fst (v ujb))
                              (.pair (bndSpkB (.snd (v ujb))) (bndPqB (.snd (v ujb)))))
                            (mbBundles (.fst (v p)))))
        (.pair
          (eCaseOpt (optZipE (kqAsGenOPK? (.fst (.snd (v p))))
                             (krAsPkResp? (.snd (.snd (v p)))))
            (mbOpks (.fst (v p)))
            (fun ujo => .cons (.pair (.fst (v ujo)) (.snd (v ujo)))
                              (mbOpks (.fst (v p)))))
          (eCaseOpt (optZipE (kqInitSend? (.fst (.snd (v p))))
                             (krAsHdrResp? (.snd (.snd (v p)))))
            (mbSends (.fst (v p)))
            (fun sbh => .cons (.pair (.fst (.fst (v sbh)))
                                (.pair (.snd (.fst (v sbh))) (.snd (v sbh))))
                              (mbSends (.fst (v p)))))))

theorem eval_bhBaseMirrorE {Γ} (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ)
    {ds : ModelDriverBase S} (hds : dsE.eval ρ = e2eMirrorBaseEnc ds) :
    (bhBaseMirrorE dsE kqE krE).eval ρ =
      e2eMirrorBaseEnc (bhBaseMirror ds (keyIndQdec (kqE.eval ρ)) (keyIndRdec (krE.eval ρ))) := by
  let Δ := (e2eMirrorBaseTy S ℓ).prod ((keyIndQT S).prod keyIndRT) :: Γ
  let ρ1 : Env Δ := .cons (dsE.eval ρ, (kqE.eval ρ, krE.eval ρ)) ρ
  have hq1 : (Expr.fst (.snd (v (O := e2eOps ℓ P C K decT encT) (.zero : Var Δ _)))).eval ρ1 =
      kqE.eval ρ := rfl
  have hr1 : (Expr.snd (.snd (v (O := e2eOps ℓ P C K decT encT) (.zero : Var Δ _)))).eval ρ1 =
      krE.eval ρ := rfl
  simp only [bhBaseMirrorE, eLet, eCaseOpt, Expr.eval, eval_optZipE]
  rw [eval_kqAsInitPrin?, eval_krAsInitPrinResp?,
      eval_kqAsGenSPK?, eval_krAsBundleResp?,
      eval_kqAsGenOPK?, eval_krAsPkResp?,
      eval_kqInitSend?, eval_krAsHdrResp?, hq1, hr1]
  cases keyIndQdec (kqE.eval ρ) with
  | initPrin u =>
    cases keyIndRdec (krE.eval ρ) <;> simp [bhBaseMirror, mbPrins, mbBundles, mbOpks, mbSends,
      e2eMirrorBaseEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, Env.get, hds]
  | genSPK u j =>
    cases keyIndRdec (krE.eval ρ) <;> simp [bhBaseMirror, mbPrins, mbBundles, mbOpks, mbSends,
      bndSpkB, bndPqB, bundleV, e2eMirrorBaseEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval,
      Env.get, hds]
  | genOPK u j o =>
    cases keyIndRdec (krE.eval ρ) <;> simp [bhBaseMirror, mbPrins, mbBundles, mbOpks, mbSends,
      e2eMirrorBaseEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, Env.get, hds]
  | initiateOPK u i bnd =>
    cases keyIndRdec (krE.eval ρ) <;> simp [bhBaseMirror, mbPrins, mbBundles, mbOpks, mbSends,
      sidV, e2eMirrorBaseEnc, e2eMirrorSendEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval,
      Env.get, hds]
  | initiateNoOPK u i bnd =>
    cases keyIndRdec (krE.eval ρ) <;> simp [bhBaseMirror, mbPrins, mbBundles, mbOpks, mbSends,
      sidV, e2eMirrorBaseEnc, e2eMirrorSendEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval,
      Env.get, hds]
  | _ =>
    simp [bhBaseMirror, mbPrins, mbBundles, mbOpks, mbSends, e2eMirrorBaseEnc,
      v, Ext.wk, Ext.refl, Ext.step, Expr.eval, Env.get, hds]

theorem exprCostUB_bhBaseMirrorE {Γ} (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) :
    exprCostUB (bhBaseMirrorE dsE kqE krE) ≤
      exprCostUB dsE + exprCostUB kqE + exprCostUB krE + 600 := by
  simp only [bhBaseMirrorE, kqInitSend?, kqAsInitPrin?, kqAsGenSPK?, kqAsGenOPK?,
    kqAsInitiateOPK?, kqAsInitiateNoOPK?, kqR1, kqR2, kqR3, kqR4, kqR5,
    krAsInitPrinResp?, krAsPkResp?, krAsBundleResp?, krAsHdrResp?,
    krR1, krR2, krR3, krR4, krR5,
    exprCostUB_sumLeft?, exprCostUB_sumRight?, exprCostUB_optSumLeft?, exprCostUB_optSumRight?,
    exprCostUB_optZipE, optMapE, mbPrins, mbBundles, mbOpks, mbSends, bndSpkB, bndPqB,
    eLet, eCaseOpt, exprCostUB, exprCostUB_v0, exprCostUB_v, Nat.reduceAdd]
  omega

theorem cost_bhBaseMirrorE {Γ} (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) :
    (bhBaseMirrorE dsE kqE krE).cost ≤ dsE.cost + kqE.cost + krE.cost + 512 := by
  simp only [bhBaseMirrorE, kqInitSend?, kqAsInitPrin?, kqAsGenSPK?, kqAsGenOPK?,
    kqAsInitiateOPK?, kqAsInitiateNoOPK?, kqR1, kqR2, kqR3, kqR4, kqR5,
    krAsInitPrinResp?, krAsPkResp?, krAsBundleResp?, krAsHdrResp?,
    krR1, krR2, krR3, krR4, krR5,
    cost_sumLeft?, cost_sumRight?, cost_optSumLeft?, cost_optSumRight?, cost_optZipE, optMapE,
    mbPrins, mbBundles, mbOpks, mbSends, bndSpkB, bndPqB,
    eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, Expr.cost, Expr.v0,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem size_bhBaseMirrorE {Γ} (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) :
    (bhBaseMirrorE dsE kqE krE).size ≤ dsE.size + kqE.size + krE.size + 600 := by
  simp only [bhBaseMirrorE, kqInitSend?, kqAsInitPrin?, kqAsGenSPK?, kqAsGenOPK?,
    kqAsInitiateOPK?, kqAsInitiateNoOPK?, kqR1, kqR2, kqR3, kqR4, kqR5,
    krAsInitPrinResp?, krAsPkResp?, krAsBundleResp?, krAsHdrResp?,
    krR1, krR2, krR3, krR4, krR5,
    size_sumLeft?, size_sumRight?, size_optSumLeft?, size_optSumRight?, size_optZipE, optMapE,
    mbPrins, mbBundles, mbOpks, mbSends, bndSpkB, bndPqB,
    eLet, eCaseOpt, Expr.size, Expr.v0, size_v, Nat.reduceAdd]
  omega

attribute [local irreducible] bhBaseMirrorE

/-- Mirrors a `(KeyIndQuery S, KeyIndResponse)` pair into `e2eDrvStateTy S ℓ`. -/
def bhE2EMirrorE {Γ} (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) :
    E2EExpr Γ (e2eDrvStateTy S ℓ) :=
  eLet (.pair σE (.pair kqE krE)) fun p =>
    .pair
      (bhBaseMirrorE (drvBase (.fst (v p))) (.fst (.snd (v p))) (.snd (.snd (v p))))
      (.pair
        (eCaseOpt (optZipE (kqAsCorruptIK? (.fst (.snd (v p))))
                           (krAsCorrResp? (.snd (.snd (v p)))))
          (drvCorrPrins (.fst (v p)))
          (fun uc => .cons (.fst (v uc)) (drvCorrPrins (.fst (v p)))))
        (.pair
          (eCaseOpt (optZipE (kqAsRevealSpkSk? (.fst (.snd (v p))))
                             (krAsSpkSkResp? (.snd (.snd (v p)))))
            (drvRevSpks (.fst (v p)))
            (fun us => .cons (.fst (v us)) (drvRevSpks (.fst (v p)))))
          (.snd (.snd (.snd (.fst (v p)))))))

theorem eval_bhE2EMirrorE {Γ} (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ) :
    (bhE2EMirrorE σE kqE krE).eval ρ =
      e2eDrvStateEnc (bhE2EMirror σ (keyIndQdec (kqE.eval ρ)) (keyIndRdec (krE.eval ρ))) := by
  let Δ := (e2eDrvStateTy S ℓ).prod ((keyIndQT S).prod keyIndRT) :: Γ
  let ρ1 : Env Δ := .cons (σE.eval ρ, (kqE.eval ρ, krE.eval ρ)) ρ
  have hq1 : (Expr.fst (.snd (v (O := e2eOps ℓ P C K decT encT) (.zero : Var Δ _)))).eval ρ1 =
      kqE.eval ρ := rfl
  have hr1 : (Expr.snd (.snd (v (O := e2eOps ℓ P C K decT encT) (.zero : Var Δ _)))).eval ρ1 =
      krE.eval ρ := rfl
  simp only [bhE2EMirrorE, eLet, eCaseOpt, Expr.eval, eval_optZipE, eval_isSomeE]
  rw [eval_bhBaseMirrorE (ds := σ.toModelDriverBase) _ _ _ _
        (by simp [ρ1, drvBase, v, Ext.wk, Ext.refl, Expr.eval, Env.get, hσ, e2eDrvStateEnc]),
      eval_kqAsCorruptIK?, eval_krAsCorrResp?,
      eval_kqAsRevealSpkSk?, eval_krAsSpkSkResp?, hq1, hr1]
  cases keyIndQdec (kqE.eval ρ) with
  | corruptIK u =>
    cases keyIndRdec (krE.eval ρ) <;> simp [bhE2EMirror, drvCorrPrins, drvRevSpks,
      e2eDrvStateEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, Env.get, hσ]
  | revealSpkSk u j =>
    cases keyIndRdec (krE.eval ρ) <;> simp [bhE2EMirror, drvCorrPrins, drvRevSpks,
      e2eDrvStateEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, Env.get, hσ]
  | _ =>
    simp [bhE2EMirror, drvCorrPrins, drvRevSpks, e2eDrvStateEnc,
      v, Ext.wk, Ext.refl, Ext.step, Expr.eval, Env.get, hσ]

theorem eval_bhE2EMirrorE_enc {Γ} (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) (ρ : Env Γ)
    (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hkq : kqE.eval ρ = keyIndQenc kq)
    (hkr : krE.eval ρ = keyIndRenc kr) :
    (bhE2EMirrorE σE kqE krE).eval ρ = e2eDrvStateEnc (bhE2EMirror σ kq kr) := by
  rw [eval_bhE2EMirrorE σE kqE krE ρ hσ, hkq, hkr, keyIndQdec_keyIndQenc, keyIndRdec_keyIndRenc]

theorem exprCostUB_bhE2EMirrorE {Γ} (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) :
    exprCostUB (bhE2EMirrorE σE kqE krE) ≤
      exprCostUB σE + exprCostUB kqE + exprCostUB krE + 1000 := by
  let Δ := (e2eDrvStateTy S ℓ).prod ((keyIndQT S).prod keyIndRT) :: Γ
  have hBase := exprCostUB_bhBaseMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ)
    (.fst (.fst (.var .zero))) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [exprCostUB, Nat.reduceAdd] at hBase
  unfold bhE2EMirrorE
  simp only [kqAsCorruptIK?, kqAsRevealSpkSk?,
    kqR1, kqR2, kqR3, kqR4, kqR5, kqR6, kqR7, kqR8, kqR9, kqR10, kqR11, kqR12,
    krAsCorrResp?, krAsSpkSkResp?,
    krR1, krR2, krR3, krR4, krR5, krR6, krR7, krR8, krR9,
    exprCostUB_sumRight?, exprCostUB_optSumLeft?, exprCostUB_optSumRight?, exprCostUB_optZipE,
    isSomeE, drvCorrPrins, drvRevSpks, drvBase, v, Ext.wk, Ext.refl, Ext.step,
    eLet, eCaseOpt, exprCostUB, exprCostUB_v0, Nat.reduceAdd]
  omega

theorem cost_bhE2EMirrorE {Γ} (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) :
    (bhE2EMirrorE σE kqE krE).cost ≤ σE.cost + kqE.cost + krE.cost + 800 := by
  let Δ := (e2eDrvStateTy S ℓ).prod ((keyIndQT S).prod keyIndRT) :: Γ
  have hBase := cost_bhBaseMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ)
    (.fst (.fst (.var .zero))) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.cost, Nat.reduceAdd] at hBase
  unfold bhE2EMirrorE
  simp only [kqAsCorruptIK?, kqAsRevealSpkSk?,
    kqR1, kqR2, kqR3, kqR4, kqR5, kqR6, kqR7, kqR8, kqR9, kqR10, kqR11, kqR12,
    krAsCorrResp?, krAsSpkSkResp?,
    krR1, krR2, krR3, krR4, krR5, krR6, krR7, krR8, krR9,
    cost_sumRight?, cost_optSumLeft?, cost_optSumRight?, cost_optZipE,
    isSomeE, drvCorrPrins, drvRevSpks, drvBase,
    eLet, eCaseOpt, v, Ext.wk, Ext.refl, Ext.step, Expr.cost, Expr.v0,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem size_bhE2EMirrorE {Γ} (σE : E2EExpr Γ (e2eDrvStateTy S ℓ))
    (kqE : E2EExpr Γ (keyIndQT S)) (krE : E2EExpr Γ keyIndRT) :
    (bhE2EMirrorE σE kqE krE).size ≤ σE.size + kqE.size + krE.size + 1000 := by
  let Δ := (e2eDrvStateTy S ℓ).prod ((keyIndQT S).prod keyIndRT) :: Γ
  have hBase := size_bhBaseMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ)
    (.fst (.fst (.var .zero))) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.size, Nat.reduceAdd] at hBase
  unfold bhE2EMirrorE
  simp only [kqAsCorruptIK?, kqAsRevealSpkSk?,
    kqR1, kqR2, kqR3, kqR4, kqR5, kqR6, kqR7, kqR8, kqR9, kqR10, kqR11, kqR12,
    krAsCorrResp?, krAsSpkSkResp?,
    krR1, krR2, krR3, krR4, krR5, krR6, krR7, krR8, krR9,
    size_sumRight?, size_optSumLeft?, size_optSumRight?, size_optZipE,
    isSomeE, drvCorrPrins, drvRevSpks, drvBase, v, Ext.wk, Ext.refl, Ext.step,
    eLet, eCaseOpt, Expr.size, Expr.v0, Nat.reduceAdd]
  omega

attribute [local irreducible] bhE2EMirrorE

def bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (uE : E2EExpr Γ (FinT S.N_id))
    (jE : E2EExpr Γ (FinT S.N_recv)) (bndE : E2EExpr Γ bundleT) : E2EExpr Γ .bool :=
  eLet (.pair (mbOpks dsE) (.pair uE (.pair jE (bndOpkB bndE)))) fun p =>
    eCaseOpt (.snd (.snd (.snd (v p))))
      (.bool true)
      (fun opk =>
        eAny nOpks (.fst (v p)) fun e =>
          .and
            (.and
              (.and
                (.and
                  (e2ePureOp (.finEq S.N_id)
                    (.pair (.fst (.fst (v e))) (.fst (.snd (v p)))))
                  (e2ePureOp (.finEq S.N_recv)
                    (.pair (.fst (.snd (.fst (v e)))) (.fst (.snd (.snd (v p)))))))
                (e2ePureOp .pu32Eq
                  (.pair (e2ePureOp .pu32OfNat
                    (e2ePureOp (.finVal S.N_opk) (.snd (.snd (.fst (v e))))))
                    (.fst (v opk)))))
              (.eqN (e2ePureOp (.finVal S.N_opk) (.snd (.snd (.fst (v e)))))
                    (e2ePureOp .pu32ToNat (.fst (v opk)))))
            (e2ePureOp (.pbytesEq 32 32) (.pair (.snd (v e)) (.snd (v opk)))))

theorem eval_bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (uE : E2EExpr Γ (FinT S.N_id))
    (jE : E2EExpr Γ (FinT S.N_recv)) (bndE : E2EExpr Γ bundleT) (ρ : Env Γ)
    {ds : ModelDriverBase S}
    (hds : dsE.eval ρ = e2eMirrorBaseEnc ds) (hlen : ds.opks.length ≤ nOpks) :
    (bhBaseOpkOkE nOpks dsE uE jE bndE).eval ρ =
      bhBaseOpkOk ds (uE.eval ρ) (jE.eval ρ) (bundleOfV (bndE.eval ρ)) := by
  set bnd := bundleOfV (bndE.eval ρ)
  have hbnd : bndE.eval ρ = bundleV bnd := (bundleV_bundleOfV (bndE.eval ρ)).symm
  simp only [bhBaseOpkOkE, bhBaseOpkOk, eLet, eCaseOpt, eAny, mbOpks, bndOpkB, bundleV,
    e2eMirrorBaseEnc, v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Env.get, hds, hbnd]
  rcases bnd.opkB? with _ | ⟨opkId, opkPk⟩
  · rfl
  · simp only [List.take_of_length_le hlen]
    apply List.any_congr rfl
    rintro ⟨⟨u', j', o⟩, pk⟩
    by_cases h4 : o.val = opkId.toNat <;> simp [h4]

theorem exprCostUB_bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (uE : E2EExpr Γ (FinT S.N_id))
    (jE : E2EExpr Γ (FinT S.N_recv)) (bndE : E2EExpr Γ bundleT) :
    exprCostUB (bhBaseOpkOkE nOpks dsE uE jE bndE) ≤
      exprCostUB dsE + exprCostUB uE + exprCostUB jE + exprCostUB bndE + 160 * nOpks + 40 := by
  simp only [bhBaseOpkOkE, mbOpks, bndOpkB, eLet, eCaseOpt, eAny, exprCostUB, exprCostUB_v,
    PqxdhSimTypes.exprCostUB_e2ePureOp, E2EPureOp.cost, pnat32_val, Nat.reduceAdd]
  omega

theorem cost_bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (uE : E2EExpr Γ (FinT S.N_id))
    (jE : E2EExpr Γ (FinT S.N_recv)) (bndE : E2EExpr Γ bundleT) :
    (bhBaseOpkOkE nOpks dsE uE jE bndE).cost ≤
      dsE.cost + uE.cost + jE.cost + bndE.cost + 160 * nOpks + 32 := by
  simp only [bhBaseOpkOkE, mbOpks, bndOpkB, eLet, eCaseOpt, eAny, v, Ext.wk, Ext.refl, Ext.step,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost, pnat32_val,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem size_bhBaseOpkOkE (nOpks : ℕ) {Γ}
    (dsE : E2EExpr Γ (e2eMirrorBaseTy S ℓ)) (uE : E2EExpr Γ (FinT S.N_id))
    (jE : E2EExpr Γ (FinT S.N_recv)) (bndE : E2EExpr Γ bundleT) :
    (bhBaseOpkOkE nOpks dsE uE jE bndE).size ≤
      dsE.size + uE.size + jE.size + bndE.size + bits nOpks + 120 := by
  simp only [bhBaseOpkOkE, mbOpks, bndOpkB, eLet, eCaseOpt, eAny,
    Expr.size, size_v, size_e2ePureOp, E2EPureOp.opSize, Nat.reduceAdd]
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
            (.and
              (e2ePureOp (.pbytesEq 32 32)
                (.pair (.fst (.snd (v e))) (bndSpkB (.fst (.snd (v p))))))
              (e2ePureOp (.pbytesEq 1568 1568)
                (.pair (.snd (.snd (v e))) (bndPqB (.fst (.snd (v p)))))))
            (e2ePureOp .pu32Eq
              (.pair (hdrSpkId (.snd (.snd (v p))))
                     (e2ePureOp .pu32OfNat
                       (e2ePureOp (.finVal S.N_recv) (.snd (.fst (v e))))))))
          (e2ePureOp .pu32Eq
            (.pair (hdrPqId (.snd (.snd (v p))))
                   (e2ePureOp .pu32OfNat
                     (e2ePureOp (.finVal S.N_recv) (.snd (.fst (v e))))))))
      (fun e => .fst (v e))

private theorem eval_guardFindBundleE (nBundles : ℕ) {Γ}
    (bundlesE : E2EExpr Γ (.list (e2eMirrorBundleEntryTy S)))
    (bndE : E2EExpr Γ bundleT) (hdrE : E2EExpr Γ hdrT) (ρ : Env Γ)
    {bundles : List ((Fin S.N_id × Fin S.N_recv) × (SignalPqxdh.Bytes × SignalPqxdh.Bytes))}
    {bnd : SignalPqxdh.PreKeyBundleInput} {hdr : SignalPqxdh.HandshakeHdr}
    (hB : bundlesE.eval ρ = bundles) (hbnd : bndE.eval ρ = bundleV bnd)
    (hhdr : hdrE.eval ρ = hdrV hdr) (hlen : bundles.length ≤ nBundles) :
    (guardFindBundleE nBundles bundlesE bndE hdrE).eval ρ =
      (bundles.find? (fun x =>
        x.2.1 == bnd.spkB && x.2.2 == bnd.pqspkB &&
        hdr.spkId == UInt32.ofNat x.1.2.val &&
        hdr.pqspkId == UInt32.ofNat x.1.2.val)).map Prod.fst := by
  simp only [guardFindBundleE, eLet, eval_optMapE, eFind, bndSpkB, bndPqB,
    hdrSpkId, hdrPqId, hdrV, bundleV, v, Ext.wk, Ext.refl, Ext.step,
    Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get, hB, hbnd, hhdr]
  rw [List.take_of_length_le hlen]

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

private theorem eval_guardCheckPrinOpkE (nPrins nOpks : ℕ) {Γ}
    (baseE : E2EExpr Γ (e2eMirrorBaseTy S ℓ))
    (ujE : E2EExpr Γ (.prod (FinT S.N_id) (FinT S.N_recv)))
    (bndE : E2EExpr Γ bundleT) (ρ : Env Γ)
    {ds : ModelDriverBase S} {uj : Fin S.N_id × Fin S.N_recv}
    {bnd : SignalPqxdh.PreKeyBundleInput}
    (hds : baseE.eval ρ = e2eMirrorBaseEnc ds) (huj : ujE.eval ρ = uj)
    (hbnd : bndE.eval ρ = bundleV bnd)
    (hPrins : ds.prins.length ≤ nPrins) (hOpks : ds.opks.length ≤ nOpks) :
    (guardCheckPrinOpkE nPrins nOpks baseE ujE bndE).eval ρ =
      (ds.prins.any (fun (u', pk) => u' == uj.1 && pk == bnd.ikB) &&
       bhBaseOpkOk ds uj.1 uj.2 bnd) := by
  simp only [guardCheckPrinOpkE, eLet, Expr.eval]
  rw [eval_bhBaseOpkOkE nOpks _ _ _ _ _
    (by simp [v, Ext.wk, Ext.refl, Expr.eval, Env.get, hds]) hOpks]
  simp only [eAny, mbPrins, bndIkB, bundleV, e2eMirrorBaseEnc,
    v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Env.get, hds, huj, hbnd, bundleOfV_bundleV]
  rw [List.take_of_length_le hPrins]
  cases bnd; rfl

def guardCorrOkE (nCorr : ℕ) {Γ}
    (corrE : E2EExpr Γ (.list (FinT S.N_id))) (uE : E2EExpr Γ (FinT S.N_id))
    (bndE : E2EExpr Γ bundleT) : E2EExpr Γ .bool :=
  eLet (.pair corrE (.pair uE (bndOpkB bndE))) fun p =>
    eCaseOpt (.snd (.snd (v p)))
      (.not (eAny nCorr (.fst (v p)) fun c =>
        e2ePureOp (.finEq S.N_id) (.pair (.fst (.snd (v p))) (v c))))
      (fun _ => .bool true)

private theorem eval_guardCorrOkE (nCorr : ℕ) {Γ}
    (corrE : E2EExpr Γ (.list (FinT S.N_id))) (uE : E2EExpr Γ (FinT S.N_id))
    (bndE : E2EExpr Γ bundleT) (ρ : Env Γ)
    {corr : List (Fin S.N_id)} {u : Fin S.N_id} {bnd : SignalPqxdh.PreKeyBundleInput}
    (hc : corrE.eval ρ = corr) (hu : uE.eval ρ = u) (hbnd : bndE.eval ρ = bundleV bnd)
    (hlen : corr.length ≤ nCorr) :
    (guardCorrOkE nCorr corrE uE bndE).eval ρ = (bnd.opkB?.isSome || !corr.contains u) := by
  simp only [guardCorrOkE, eLet, eCaseOpt, eAny, bndOpkB, bundleV,
    v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Env.get, hc, hu, hbnd]
  rw [List.take_of_length_le hlen, List.contains_eq_any_beq]
  rcases bnd.opkB? with _ | ⟨_, _⟩ <;> rfl

private theorem eval_and_eq {Γ : List (Ty (e2eSig ℓ))} (a b : E2EExpr Γ .bool) (ρ : Env Γ) :
    (Expr.and a b).eval ρ = (a.eval ρ && b.eval ρ) := rfl

attribute [local irreducible] guardFindBundleE guardCheckPrinOpkE guardCorrOkE

/-- Session-promotion guard `bhE2EGuard` over `e2eDrvStateTy S ℓ`. -/
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

private theorem eval_ite_cond {Γ : List (Ty (e2eSig ℓ))} {τ : Ty (e2eSig ℓ)}
    (c : E2EExpr Γ .bool) (a b : E2EExpr Γ τ) (ρ : Env Γ) :
    (Expr.ite c a b).eval ρ = cond (c.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [Expr.eval]; cases c.eval ρ <;> rfl

private theorem eval_eLet_eq {Γ : List (Ty (e2eSig ℓ))} {α β : Ty (e2eSig ℓ)}
    (x : E2EExpr Γ α) (f : Var (α :: Γ) α → E2EExpr (α :: Γ) β) (ρ : Env Γ) :
    (eLet x f).eval ρ = (f .zero).eval (.cons (x.eval ρ) ρ) := rfl

private theorem eval_eCaseOpt_eq {Γ : List (Ty (e2eSig ℓ))} {α β : Ty (e2eSig ℓ)}
    (x : E2EExpr Γ (.opt α)) (n : E2EExpr Γ β)
    (s : Var (α :: Γ) α → E2EExpr (α :: Γ) β) (ρ : Env Γ) :
    (eCaseOpt x n s).eval ρ =
      match x.eval ρ with
      | none => n.eval ρ
      | some a => (s .zero).eval (.cons a ρ) := by
  simp only [eCaseOpt, Expr.eval]; cases x.eval ρ <;> rfl

private theorem eval_eAny_eq {Γ : List (Ty (e2eSig ℓ))} {α : Ty (e2eSig ℓ)}
    (B : ℕ) (l : E2EExpr Γ (.list α))
    (p : Var (α :: Γ) α → E2EExpr (α :: Γ) .bool) (ρ : Env Γ) :
    (eAny B l p).eval ρ =
      ((l.eval ρ).take B).any (fun x => (p .zero).eval (.cons x ρ)) := rfl

private theorem eval_eFind_eq {Γ : List (Ty (e2eSig ℓ))} {α : Ty (e2eSig ℓ)}
    (B : ℕ) (l : E2EExpr Γ (.list α))
    (p : Var (α :: Γ) α → E2EExpr (α :: Γ) .bool) (ρ : Env Γ) :
    (eFind B l p).eval ρ =
      ((l.eval ρ).take B).find? (fun x => (p .zero).eval (.cons x ρ)) := rfl

theorem eval_bhE2EGuardE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
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
  set ρ0 : Env ((e2eDrvStateTy S ℓ).prod (sidT S) :: Γ) :=
    .cons (e2eDrvStateEnc σ, sidE.eval ρ) ρ with hρ0
  have hpair0 : (Expr.pair σE sidE).eval ρ = (e2eDrvStateEnc σ, sidE.eval ρ) := by
    simp only [Expr.eval, hσ]
  have hsid0 : (ρ0.get .zero).2 = sidE.eval ρ := rfl
  have hInstsEval :
      (drvInsts (O := e2eOps ℓ P C K decT encT) (.fst (.var .zero))).eval ρ0 =
        σ.insts.map e2eModelInstEnc := rfl
  have hSendsEval :
      (mbSends (O := e2eOps ℓ P C K decT encT)
        (drvBase (.fst (.var .zero)))).eval ρ0 =
        σ.sends.map e2eMirrorSendEnc := rfl
  have hany1 :
      σ.insts.any ((fun x => (e2eSidEqE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (miSid (.var .zero)) (.snd (.var (.succ .zero)))).eval (.cons x ρ0)) ∘ e2eModelInstEnc) =
      σ.insts.any (fun d => d.sid == sid) := by
    apply List.any_congr rfl; intro d
    simp only [Function.comp_apply, eval_e2eSidEqE, miSid, e2eModelInstEnc,
      Expr.eval, Env.get, hsid0, sidOfV_sidV, sid]
  have hfindS :
      σ.sends.find? ((fun x => (e2eSidEqE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (.fst (.var .zero)) (.snd (.var (.succ .zero)))).eval (.cons x ρ0)) ∘ e2eMirrorSendEnc) =
      σ.sends.find? (fun x => x.1 == sid) := by
    congr 1; funext ⟨s, bnd, hdr⟩
    simp only [Function.comp_apply, eval_e2eSidEqE, e2eMirrorSendEnc,
      Expr.eval, Env.get, hsid0, sidOfV_sidV, sid]
  unfold bhE2EGuardE bhE2EGuard
  rw [eval_eLet_eq, hpair0, ← hρ0, eval_ite_cond, eval_eAny_eq]
  dsimp only [v, Ext.wk, Ext.refl, Ext.step]
  rw [hInstsEval, List.take_of_length_le hInsts', List.any_map, hany1]
  cases hdup : σ.insts.any (fun d => d.sid == sid)
  · simp only [cond, Bool.false_eq_true, ↓reduceIte]
    rw [eval_eCaseOpt_eq, eval_eFind_eq]
    rw [hSendsEval, List.take_of_length_le hSends', List.find?_map, hfindS]
    rcases hs : σ.sends.find? (fun x => x.1 == sid) with _ | ⟨s0, bnd, hdr⟩
    · rw [hs]; rfl
    · rw [hs]; dsimp only [Option.map]
      set ρ1 : Env (e2eMirrorSendEntryTy S ℓ :: (e2eDrvStateTy S ℓ).prod (sidT S) :: Γ) :=
        .cons (e2eMirrorSendEnc (s0, bnd, hdr)) ρ0
      have hhdr1 : (ρ1.get .zero).2.2 = hdrV hdr := rfl
      have hbnd1 : (ρ1.get .zero).2.1 = bundleV bnd := rfl
      have hInstsEval1 :
          (drvInsts (O := e2eOps ℓ P C K decT encT) (.fst (.var (.succ .zero)))).eval ρ1 =
            σ.insts.map e2eModelInstEnc := rfl
      have hany2 :
          σ.insts.any ((fun x =>
            (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (.pbytesEq 32 32)
              (.pair (hdrEkA (miHdr (.var .zero)))
                     (hdrEkA (.snd (.snd (.var (.succ .zero))))))).eval (.cons x ρ1)) ∘
            e2eModelInstEnc) =
          σ.insts.any (fun d => d.hdr.ekAPk == hdr.ekAPk) := by
        apply List.any_congr rfl; intro d
        simp only [Function.comp_apply, miHdr, hdrEkA, hdrV, e2eModelInstEnc,
          eval_e2ePureOp, E2EPureOp.eval, Expr.eval, Env.get, hhdr1]
      rw [eval_ite_cond, eval_eAny_eq]
      rw [hInstsEval1, List.take_of_length_le hInsts', List.any_map, hany2]
      cases hek : σ.insts.any (fun d => d.hdr.ekAPk == hdr.ekAPk)
      · simp only [cond, Bool.false_eq_true, ↓reduceIte]
        rw [eval_eCaseOpt_eq]
        rw [eval_guardFindBundleE (bundles := σ.bundles) (bnd := bnd) (hdr := hdr)
          nBundles (mbBundles (drvBase (.fst (.var (.succ .zero)))))
          (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero))) ρ1 rfl rfl rfl hBundles]
        rcases hb : σ.bundles.find? (fun x =>
            x.2.1 == bnd.spkB && x.2.2 == bnd.pqspkB &&
            hdr.spkId == UInt32.ofNat x.1.2.val &&
            hdr.pqspkId == UInt32.ofNat x.1.2.val) with _ | ⟨⟨u, j⟩, _⟩
        · rw [hb]; rfl
        · rw [hb]; dsimp only [Option.map]
          rw [eval_ite_cond]
          have hPrins0 : σ.toModelDriverBase.prins.length ≤ nPrins := hPrins
          have hOpks0 : σ.toModelDriverBase.opks.length ≤ nOpks := hOpks
          rw [eval_and_eq,
            eval_guardCheckPrinOpkE (ds := σ.toModelDriverBase) (uj := (u, j)) (bnd := bnd)
              nPrins nOpks (drvBase (.fst (.var (.succ (.succ .zero)))))
              (.var .zero) (.fst (.snd (.var (.succ .zero)))) (.cons (u, j) ρ1)
              rfl rfl rfl hPrins0 hOpks0,
            eval_guardCorrOkE (corr := σ.corrPrins) (u := u) (bnd := bnd)
              (Γ := (FinT S.N_id).prod (FinT S.N_recv) :: e2eMirrorSendEntryTy S ℓ ::
                (e2eDrvStateTy S ℓ).prod (sidT S) :: Γ)
              nPrins (drvCorrPrins (.fst (.var (.succ (.succ .zero)))))
              (.fst (.var .zero)) (.fst (.snd (.var (.succ .zero)))) (.cons (u, j) ρ1)
              rfl rfl rfl hCorr]
          have hPrinsEq : σ.toModelDriverBase.prins = σ.prins := rfl
          rw [hPrinsEq, Bool.and_assoc]
          cases hchk :
            ((σ.prins.any fun (u', pk) => u' == u && pk == bnd.ikB) &&
              (bhBaseOpkOk σ.toModelDriverBase u j bnd &&
                (bnd.opkB?.isSome || !σ.corrPrins.contains u)))
          · rfl
          · simp only [cond, ↓reduceIte, Option.map, Expr.eval, Env.get, hhdr1, hbnd1]
      · rfl
  · rfl

theorem exprCostUB_bhE2EGuardE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    exprCostUB (bhE2EGuardE qStart nPrins nBundles nOpks nSends σE sidE) ≤
      exprCostUB σE + exprCostUB sidE + 1800 * qStart + 900 * nSends + 3400 * nBundles +
        144 * nPrins + 220 * nOpks + 440 := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (sidT S) :: Γ
  let Δ1 := e2eModelInstTy S ℓ :: Δ0
  let Δ2 := e2eMirrorSendEntryTy S ℓ :: Δ0
  let Δ3 := ((e2eMirrorBaseTy S ℓ).prod (((FinT S.N_id).prod (FinT S.N_recv)).prod bundleT)) ::
    (FinT S.N_id).prod (FinT S.N_recv) :: Δ2
  have hs1 := exprCostUB_e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ1)
    (.fst (.var .zero)) (.snd (.var (.succ .zero)))
  have hs2 := exprCostUB_e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ2)
    (.fst (.var .zero)) (.snd (.var (.succ .zero)))
  have hopk := exprCostUB_bhBaseOpkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ3) nOpks
    (.fst (.var .zero)) (.fst (.fst (.snd (.var .zero))))
    (.snd (.fst (.snd (.var .zero)))) (.snd (.snd (.var .zero)))
  simp only [exprCostUB, Nat.reduceAdd] at hs1 hs2 hopk
  unfold bhE2EGuardE guardFindBundleE guardCheckPrinOpkE guardCorrOkE
  simp only [drvInsts, drvBase, drvCorrPrins, mbSends, mbBundles, mbPrins, miSid, miHdr,
    bndSpkB, bndPqB, bndIkB, bndOpkB, hdrEkA, hdrSpkId, hdrPqId, optMapE,
    eLet, eCaseOpt, eAny, eFind, v, Ext.wk, Ext.refl, Ext.step,
    exprCostUB, exprCostUB_v0,
    PqxdhSimTypes.exprCostUB_e2ePureOp, E2EPureOp.cost, pnat32_val, pnat1568_val, Nat.reduceAdd]
  have hs1B : exprCostUB (e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Δ1)
      (.fst (.var .zero)) (.snd (.var (.succ .zero)))) + 1 ≤ 820 := by omega
  have hs1M : qStart * (exprCostUB (e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Δ1)
      (.fst (.var .zero)) (.snd (.var (.succ .zero)))) + 1) ≤ 820 * qStart := by
    rw [Nat.mul_comm 820 qStart]; exact Nat.mul_le_mul_left qStart hs1B
  have hs2B : exprCostUB (e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Δ2)
      (.fst (.var .zero)) (.snd (.var (.succ .zero)))) + 1 ≤ 850 := by omega
  have hs2M : nSends * (exprCostUB (e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Δ2)
      (.fst (.var .zero)) (.snd (.var (.succ .zero)))) + 1) ≤ 850 * nSends := by
    rw [Nat.mul_comm 850 nSends]; exact Nat.mul_le_mul_left nSends hs2B
  omega

theorem cost_bhE2EGuardE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    (bhE2EGuardE qStart nPrins nBundles nOpks nSends σE sidE).cost ≤
      σE.cost + sidE.cost + 361 * qStart + 300 * nSends + 3300 * nBundles +
        112 * nPrins + 160 * nOpks + 220 := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (sidT S) :: Γ
  let Δ1 := e2eModelInstTy S ℓ :: Δ0
  let Δ2 := e2eMirrorSendEntryTy S ℓ :: Δ0
  let Δ3 := ((e2eMirrorBaseTy S ℓ).prod (((FinT S.N_id).prod (FinT S.N_recv)).prod bundleT)) ::
    (FinT S.N_id).prod (FinT S.N_recv) :: Δ2
  have hs1 := cost_e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ1)
    (.fst (.var .zero)) (.snd (.var (.succ .zero)))
  have hs2 := cost_e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ2)
    (.fst (.var .zero)) (.snd (.var (.succ .zero)))
  have hopk := cost_bhBaseOpkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ3) nOpks
    (.fst (.var .zero)) (.fst (.fst (.snd (.var .zero))))
    (.snd (.fst (.snd (.var .zero)))) (.snd (.snd (.var .zero)))
  simp only [Expr.cost, Nat.reduceAdd] at hs1 hs2 hopk
  unfold bhE2EGuardE guardFindBundleE guardCheckPrinOpkE guardCorrOkE
  simp only [drvInsts, drvBase, drvCorrPrins, mbSends, mbBundles, mbPrins, miSid, miHdr,
    bndSpkB, bndPqB, bndIkB, bndOpkB, hdrEkA, hdrSpkId, hdrPqId, optMapE,
    eLet, eCaseOpt, eAny, eFind, v, Ext.wk, Ext.refl, Ext.step,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost, pnat32_val, pnat1568_val,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  have hs1B : (e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Δ1)
      (.fst (.var .zero)) (.snd (.var (.succ .zero)))).cost + 1 ≤ 285 := by omega
  have hs1M : qStart * ((e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Δ1)
      (.fst (.var .zero)) (.snd (.var (.succ .zero)))).cost + 1) ≤ 285 * qStart := by
    rw [Nat.mul_comm 285 qStart]; exact Nat.mul_le_mul_left qStart hs1B
  have hs2B : (e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Δ2)
      (.fst (.var .zero)) (.snd (.var (.succ .zero)))).cost + 1 ≤ 300 := by omega
  have hs2M : nSends * ((e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Δ2)
      (.fst (.var .zero)) (.snd (.var (.succ .zero)))).cost + 1) ≤ 300 * nSends := by
    rw [Nat.mul_comm 300 nSends]; exact Nat.mul_le_mul_left nSends hs2B
  omega

theorem size_bhE2EGuardE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    (bhE2EGuardE qStart nPrins nBundles nOpks nSends σE sidE).size ≤
      σE.size + sidE.size + 2 * bits qStart + 2 * bits nPrins +
        bits nBundles + bits nOpks + bits nSends + 2100 := by
  let Δ0 := (e2eDrvStateTy S ℓ).prod (sidT S) :: Γ
  let Δ1 := e2eModelInstTy S ℓ :: Δ0
  let Δ2 := e2eMirrorSendEntryTy S ℓ :: Δ0
  let Δ3 := ((e2eMirrorBaseTy S ℓ).prod (((FinT S.N_id).prod (FinT S.N_recv)).prod bundleT)) ::
    (FinT S.N_id).prod (FinT S.N_recv) :: Δ2
  have hs1 := size_e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ1)
    (.fst (.var .zero)) (.snd (.var (.succ .zero)))
  have hs2 := size_e2eSidEqE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ2)
    (.fst (.var .zero)) (.snd (.var (.succ .zero)))
  have hopk := size_bhBaseOpkOkE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Δ3) nOpks
    (.fst (.var .zero)) (.fst (.fst (.snd (.var .zero))))
    (.snd (.fst (.snd (.var .zero)))) (.snd (.snd (.var .zero)))
  simp only [Expr.size, Nat.reduceAdd] at hs1 hs2 hopk
  unfold bhE2EGuardE guardFindBundleE guardCheckPrinOpkE guardCorrOkE
  simp only [drvInsts, drvBase, drvCorrPrins, mbSends, mbBundles, mbPrins, miSid, miHdr,
    bndSpkB, bndPqB, bndIkB, bndOpkB, hdrEkA, hdrSpkId, hdrPqId, optMapE,
    eLet, eCaseOpt, eAny, eFind, v, Ext.wk, Ext.refl, Ext.step,
    Expr.size, size_e2ePureOp, E2EPureOp.opSize, Nat.reduceAdd]
  omega

attribute [local irreducible] bhE2EGuardE

def prepStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    E2EExpr Γ (.opt (.prod (FinT S.N_id) (FinT S.N_recv))) :=
  optMapE (bhE2EGuardE qStart nPrins nBundles nOpks nSends σE sidE)
    (fun x => .snd (.snd (v x)))

theorem eval_prepStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
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
    simp [v, Ext.wk, Ext.refl, Expr.eval, Env.get]

theorem eval_prepStartSpkE_mirrorBounded (qStart nPrins nBundles nOpks nSends nCorr : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) (ρ : Env Γ)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hsid : sidE.eval ρ = sidV sid)
    (hBnd : DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ)
    (hCorrN : nCorr ≤ nPrins) :
    (prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE).eval ρ =
      (bhE2EGuard σ sid).map (fun (_, _, uj) => uj) := by
  rw [eval_prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE ρ hσ
    hBnd.insts_le hBnd.prins_le hBnd.bundles_le hBnd.opks_le hBnd.sends_le
    (hBnd.corrPrins_le.trans hCorrN), hsid, sidOfV_sidV]

theorem exprCostUB_prepStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    exprCostUB (prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE) ≤
      exprCostUB σE + exprCostUB sidE + 1800 * qStart + 900 * nSends + 3400 * nBundles +
        144 * nPrins + 220 * nOpks + 448 := by
  have hg := exprCostUB_bhE2EGuardE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends σE sidE
  simp only [prepStartSpkE, optMapE, eCaseOpt, exprCostUB, exprCostUB_v, Nat.reduceAdd]
  omega

theorem cost_prepStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    (prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE).cost ≤
      σE.cost + sidE.cost + 361 * qStart + 300 * nSends + 3300 * nBundles +
        112 * nPrins + 160 * nOpks + 228 := by
  have hg := cost_bhE2EGuardE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends σE sidE
  simp only [prepStartSpkE, optMapE, eCaseOpt, v, Ext.wk, Ext.refl, Expr.cost,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem size_prepStartSpkE (qStart nPrins nBundles nOpks nSends : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (sidE : E2EExpr Γ (sidT S)) :
    (prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE).size ≤
      σE.size + sidE.size + 2 * bits qStart + 2 * bits nPrins +
        bits nBundles + bits nOpks + bits nSends + 2110 := by
  have hg := size_bhE2EGuardE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) qStart nPrins nBundles nOpks nSends σE sidE
  simp only [prepStartSpkE, optMapE, eCaseOpt, Expr.size, size_v, Nat.reduceAdd]
  omega

attribute [local irreducible] prepStartSpkE

def bhDrvSessionInitPrinE {Γ} (sidE : E2EExpr Γ (sidT S)) : E2EExpr Γ (.opt (FinT S.N_id)) :=
  eCaseSum sidE
    (fun ui => .some (.fst (v ui)))
    (fun r => eCaseSum (v r) (fun ui => .some (.fst (v ui))) (fun _ => .none))

@[simp] theorem eval_bhDrvSessionInitPrinE {Γ} (sidE : E2EExpr Γ (sidT S)) (ρ : Env Γ) :
    (bhDrvSessionInitPrinE sidE).eval ρ = bhDrvSessionInitPrin? (sidOfV (sidE.eval ρ)) := by
  rcases h : sidE.eval ρ with ⟨u, _⟩ | ⟨u, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
    simp [bhDrvSessionInitPrinE, bhDrvSessionInitPrin?, sidOfV, eCaseSum,
      v, Ext.wk, Ext.refl, Expr.eval, Env.get, h]

theorem exprCostUB_bhDrvSessionInitPrinE {Γ} (sidE : E2EExpr Γ (sidT S)) :
    exprCostUB (bhDrvSessionInitPrinE sidE) ≤ exprCostUB sidE + 12 := by
  simp only [bhDrvSessionInitPrinE, eCaseSum, exprCostUB, exprCostUB_v, Nat.reduceAdd]
  omega

theorem cost_bhDrvSessionInitPrinE {Γ} (sidE : E2EExpr Γ (sidT S)) :
    (bhDrvSessionInitPrinE sidE).cost ≤ sidE.cost + 8 := by
  simp only [bhDrvSessionInitPrinE, eCaseSum, v, Ext.wk, Ext.refl, Expr.cost,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

def bhInitRegIdE {Γ} (sidE : E2EExpr Γ (sidT S)) : E2EExpr Γ U32 :=
  eCaseOpt (bhDrvSessionInitPrinE sidE)
    (e2ePureOp (.u32Lit 0#32) .unit)
    (fun u => e2ePureOp .u32OfNat (e2ePureOp (.finVal S.N_id) (v u)))

@[simp] theorem eval_bhInitRegIdE {Γ} (sidE : E2EExpr Γ (sidT S)) (ρ : Env Γ) :
    (bhInitRegIdE sidE).eval ρ = bhInitRegId (sidOfV (sidE.eval ρ)) := by
  simp only [bhInitRegIdE, bhInitRegId, eCaseOpt, Expr.eval, eval_bhDrvSessionInitPrinE]
  rcases bhDrvSessionInitPrin? (sidOfV (sidE.eval ρ)) with _ | u <;>
    simp [v, Ext.wk, Ext.refl, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Env.get]

theorem exprCostUB_bhInitRegIdE {Γ} (sidE : E2EExpr Γ (sidT S)) :
    exprCostUB (bhInitRegIdE sidE) ≤ exprCostUB sidE + 24 := by
  simp only [bhInitRegIdE, bhDrvSessionInitPrinE, eCaseOpt, eCaseSum, exprCostUB, exprCostUB_v,
    PqxdhSimTypes.exprCostUB_e2ePureOp, E2EPureOp.cost, Nat.reduceAdd]
  omega

theorem cost_bhInitRegIdE {Γ} (sidE : E2EExpr Γ (sidT S)) :
    (bhInitRegIdE sidE).cost ≤ sidE.cost + 16 := by
  simp only [bhInitRegIdE, bhDrvSessionInitPrinE, eCaseOpt, eCaseSum, v, Ext.wk, Ext.refl,
    Expr.cost, cost_e2ePureOp, E2EPureOp.cost,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

theorem list_not_any_not {α : Type} (l : List α) (p : α → Bool) :
    (!l.any (fun x => !p x)) = l.all p := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.any_cons, List.all_cons, Bool.not_or, ih]


def corrPrinsTblE (nCorr : ℕ) {Γ}
    (corrE : E2EExpr Γ (.list (FinT S.N_id))) : E2EExpr Γ (.tbl .bool) :=
  .foldrB nCorr corrE (.tconst (.bool false))
    (.tset .v1 (e2ePureOp (.finVal S.N_id) .v0) (.bool true))

private theorem foldr_corrTbl_apply {N : ℕ} (l : List (Fin N)) (u : Fin N) :
    (l.foldr (fun (x : Fin N) (tbl : ℕ → Bool) (j : ℕ) =>
        if j = x.val then true else tbl j)
      (fun _ => false)) u.val = l.contains u := by
  rw [List.contains_eq_any_beq]
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, List.any_cons]
    by_cases h : u.val = x.val
    · have hux : u = x := Fin.ext h
      simp [h, hux]
    · have hne : (u == x) = false := beq_false_of_ne (fun hux => h (congrArg Fin.val hux))
      simp only [h, ↓reduceIte, hne, Bool.false_or]
      exact ih

theorem eval_corrPrinsTblE (nCorr : ℕ) {Γ}
    (corrE : E2EExpr Γ (.list (FinT S.N_id))) (ρ : Env Γ)
    {corr : List (Fin S.N_id)} (hc : corrE.eval ρ = corr) (hlen : corr.length ≤ nCorr)
    (u : Fin S.N_id) :
    (corrPrinsTblE nCorr corrE).eval ρ u.val = corr.contains u := by
  simp only [corrPrinsTblE, Expr.eval, Expr.v0, Expr.v1, eval_e2ePureOp, E2EPureOp.eval,
    Env.get, hc, List.take_of_length_le hlen]
  exact foldr_corrTbl_apply corr u

def bhE2EInstIkACorrTblE (nPrins : ℕ) {Γ}
    (corrTblE : E2EExpr Γ (.tbl .bool))
    (prinsE : E2EExpr Γ (.list (e2eMirrorPrinEntryTy S)))
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ)) : E2EExpr Γ .bool :=
  eLet (.pair corrTblE (.pair prinsE dE)) fun p =>
    orE
      (eCaseOpt (bhDrvSessionInitPrinE (miSid (.snd (.snd (v p)))))
        (.bool true)
        (fun u => .tget (.fst (v p)) (e2ePureOp (.finVal S.N_id) (v u))))
      (eAny nPrins (.fst (.snd (v p))) fun e =>
        .and
          (e2ePureOp (.pbytesEq 32 32)
            (.pair (.snd (v e)) (hdrIkA (miHdr (.snd (.snd (v p)))))))
          (.tget (.fst (v p)) (e2ePureOp (.finVal S.N_id) (.fst (v e)))))

def bhE2EInstIkACorrE (nCorr nPrins : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (dE : E2EExpr Γ (e2eModelInstTy S ℓ)) : E2EExpr Γ .bool :=
  eLet (.pair σE dE) fun p =>
    bhE2EInstIkACorrTblE nPrins
      (corrPrinsTblE nCorr (drvCorrPrins (.fst (v p))))
      (mbPrins (drvBase (.fst (v p))))
      (.snd (v p))

theorem eval_bhE2EInstIkACorrTblE (nPrins : ℕ) {Γ}
    (corrTblE : E2EExpr Γ (.tbl .bool))
    (prinsE : E2EExpr Γ (.list (e2eMirrorPrinEntryTy S)))
    (dE : E2EExpr Γ (e2eModelInstTy S ℓ)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {d : BHModelInst S ℓ}
    (hTbl : ∀ u : Fin S.N_id, corrTblE.eval ρ u.val = σ.corrPrins.contains u)
    (hPrinsE : prinsE.eval ρ = σ.prins)
    (hd : dE.eval ρ = e2eModelInstEnc d)
    (hPrins : σ.prins.length ≤ nPrins) :
    (bhE2EInstIkACorrTblE nPrins corrTblE prinsE dE).eval ρ = bhE2EInstIkACorr σ d := by
  simp only [bhE2EInstIkACorrTblE, bhE2EInstIkACorr, eLet, eval_orE, eCaseOpt, eAny,
    miSid, miHdr, hdrIkA, hdrV, e2eModelInstEnc,
    v, Ext.wk, Ext.refl, Ext.step, Expr.eval, eval_bhDrvSessionInitPrinE,
    eval_e2ePureOp, E2EPureOp.eval, Env.get, hPrinsE, hd, sidOfV_sidV]
  rw [List.take_of_length_le hPrins]
  congr 1
  · rcases bhDrvSessionInitPrin? d.sid with _ | u
    · rfl
    · exact hTbl u
  · apply List.any_congr rfl
    rintro ⟨u, pk⟩
    congr 1
    exact hTbl u

theorem eval_bhE2EInstIkACorrE (nCorr nPrins : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (dE : E2EExpr Γ (e2eModelInstTy S ℓ)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {d : BHModelInst S ℓ}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hd : dE.eval ρ = e2eModelInstEnc d)
    (hCorr : σ.corrPrins.length ≤ nCorr) (hPrins : σ.prins.length ≤ nPrins) :
    (bhE2EInstIkACorrE nCorr nPrins σE dE).eval ρ = bhE2EInstIkACorr σ d := by
  simp only [bhE2EInstIkACorrE, eLet, v, Ext.wk, Ext.refl, Expr.eval, Env.get]
  let ρ1 : Env ((e2eDrvStateTy S ℓ).prod (e2eModelInstTy S ℓ) :: Γ) :=
    .cons (σE.eval ρ, dE.eval ρ) ρ
  apply eval_bhE2EInstIkACorrTblE nPrins _ _ _ ρ1
  · intro u
    exact eval_corrPrinsTblE nCorr _ ρ1
      (by simp [ρ1, drvCorrPrins, Expr.eval, Env.get, hσ, e2eDrvStateEnc]) hCorr u
  · simp [ρ1, mbPrins, drvBase, Expr.eval, Env.get, hσ, e2eDrvStateEnc, e2eMirrorBaseEnc]
  · simp [ρ1, Expr.eval, Env.get, hd]
  · exact hPrins

theorem exprCostUB_bhE2EInstIkACorrE (nCorr nPrins : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (dE : E2EExpr Γ (e2eModelInstTy S ℓ)) :
    exprCostUB (bhE2EInstIkACorrE nCorr nPrins σE dE) ≤
      exprCostUB σE + exprCostUB dE + 140 * nCorr + 160 * nPrins + 130 := by
  simp only [bhE2EInstIkACorrE, bhE2EInstIkACorrTblE, corrPrinsTblE,
    bhDrvSessionInitPrinE, orE, drvCorrPrins, drvBase, mbPrins,
    miSid, miHdr, hdrIkA, eLet, eCaseOpt, eCaseSum, eAny,
    exprCostUB, exprCostUB_v0, exprCostUB_v1, exprCostUB_v,
    PqxdhSimTypes.exprCostUB_e2ePureOp, E2EPureOp.cost, pnat32_val, Nat.reduceAdd]
  omega

theorem cost_bhE2EInstIkACorrE (nCorr nPrins : ℕ) {Γ}
    (σE : E2EExpr Γ (e2eDrvStateTy S ℓ)) (dE : E2EExpr Γ (e2eModelInstTy S ℓ)) :
    (bhE2EInstIkACorrE nCorr nPrins σE dE).cost ≤
      σE.cost + dE.cost + 136 * nCorr + 156 * nPrins + 120 := by
  simp only [bhE2EInstIkACorrE, bhE2EInstIkACorrTblE, corrPrinsTblE,
    bhDrvSessionInitPrinE, orE, drvCorrPrins, drvBase, mbPrins,
    miSid, miHdr, hdrIkA, eLet, eCaseOpt, eCaseSum, eAny, v, Ext.wk, Ext.refl, Ext.step,
    Expr.cost, Expr.v0, Expr.v1, cost_e2ePureOp, E2EPureOp.cost, pnat32_val,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte, Nat.reduceAdd]
  omega

attribute [local irreducible] corrPrinsTblE bhE2EInstIkACorrTblE bhE2EInstIkACorrE

end GuardsAndMirrors

end Computational.Proofs.E2E.Dsl.E2EStateRepr
