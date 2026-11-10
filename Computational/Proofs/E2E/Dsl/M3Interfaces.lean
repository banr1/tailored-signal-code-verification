/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.M2Interfaces
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers

/-!
# Sub-Program Interface Contracts for Driver State, Session Step, and Promotion

Defines the `ReductionDsl` driver-state representation (`e2eDrvStateTy`), inductive list-bound
and session-reachability invariants, and the sub-program interface contracts (`M3SubprogramsIface`
and `M3SubprogramsSizeIface`) consumed by the E2E `KeyInd` and single-session `SM.spec` reductions.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.M3Interfaces

open OracleSpec OracleComp
open ReductionDsl (Ty Env Iface Expr Comp)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (GameState initState oracleImplR)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes ModelDriverBase ModelDriverInstanceMeta BHModelInst
  BHE2EDrvState BHE2ESmResp BHPrefixCtx bhIdKeyOf bhDrvSessionInitPrin? bhInitRegId
  bhDrvKiQueryOk bhNoOpkRespPromoted bhBaseMirror bhE2EMirror bhE2EGuard bhE2EDrvInstClean
  bhE2EDrvWon bhE2EInstIkACorr
  bhIsBobRecvSMQuery bhIsBobAcceptSMResp bhDecodePreKeyMsgE bhExpectedPreKeyMsg bhHdrOfPreKeyMsg
  shortCiphertext wirePrekey bhPackSmResp bhUnpackSmResp bhE2EStepLocalSm bhE2EFinishStartSpk
  compositionLocalStart bhShallowFinishPrefix paramsIdsWithSpqr sessionSchemeFixedSpk
  configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Costed (e2eSig PB PU32 B BV256 FinT IdKey GhostStT
  bundleT bundleV bundleOfV hdrT hdrV hdrOfV sidT sidV sidOfV prefixCtxT
  recvResultEnc recvResultDec smQT smQenc smRT smRdec
  keyIndQT keyIndQenc keyIndQdec keyIndRT keyIndRenc keyIndRdec
  E2EPureOp e2eOps E2ESessionTag e2eKeyIndTargetIface e2eSessionTargetIface)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp eval_e2ePureOp cost_e2ePureOp
  size_e2ePureOp bundleOfV_bundleV bundleV_bundleOfV hdrOfV_hdrV hdrV_hdrOfV
  sidOfV_sidV sidV_sidOfV recvResultDec_recvResultEnc recvResultEnc_recvResultDec
  keyIndQdec_keyIndQenc keyIndQenc_keyIndQdec keyIndRdec_keyIndRenc keyIndRenc_keyIndRdec)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface e2eKeyIndStateTy e2eKeyIndStateToVal
  e2eValToKeyIndState e2eValToKeyIndState_toVal e2eKeyIndStateToVal_ofVal
  KeyIndSetupBounded pqxdhKeyIndImpl1KeyReal_preserves_setupBounded)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp GameReachInv SmListBounded SmReachBounded
  gameReachInv_initState smReachBounded_oracleImplR)
open Computational.Proofs.E2E.Dsl.M2Interfaces (smQdec smQdec_smQenc smQenc_smQdec smRenc
  e2eGsTy e2eGsEnc e2eGsDec PqxdhSimIface DrSessionSimIface)

/-! ## Driver-State Representation, Codecs, and Projections -/

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

/-- Bounded-list representation of `ModelDriverBase S`: `(prins, (bundles, (opks, sends)))`. -/
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

/-- Representation of `ModelDriverInstanceMeta S`:
`(bobAccepted, (ikACorrAtAccept, (respPrin, (respSpkIdx, instOpkId?))))`. -/
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

/-- Representation of `BHModelInst S ℓ`: `(sid, (hdr, (idA, (idB, (spkCoins, gs)))))`. -/
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

/-- Bounded-list `ReductionDsl` representation of `BHE2EDrvState S ℓ`:
`(base, (corrPrins, (revealedSpks, (insts, (instMeta, (st, (b, paused)))))))`. -/
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

@[simp] theorem e2eDrvStateDec_insts_length {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) :
    (e2eDrvStateDec (e2eDrvStateEnc σ)).insts.length = σ.insts.length := by
  simp [e2eDrvStateEnc, e2eDrvStateDec]

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
  simp only [Function.comp_apply]
  cases hgs : d.gs <;> simp [hgs, e2eModelInstEnc, e2eModelInstDec]

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
  · have h3 : (e2eDrvStateDec (e2eDrvStateEnc σ)).corrPrins = σ.corrPrins := rfl
    simp only [hs, h2 hdr.ekAPk, h3]

theorem e2eDrvStateDec_e2eDrvStateEnc_of_gs {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ)
    (hgs : ∀ d ∈ σ.insts, ∀ gs ∈ d.gs, e2eGsDec (e2eGsEnc gs) = gs) :
    e2eDrvStateDec (e2eDrvStateEnc σ) = σ := by
  cases σ with
  | mk base corr advRev insts metaL st b paused =>
    have hinst :
        ∀ (l : List (BHModelInst S ℓ)),
          (∀ d ∈ l, ∀ gs ∈ d.gs, e2eGsDec (e2eGsEnc gs) = gs) →
          (l.map e2eModelInstEnc).map e2eModelInstDec = l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons d rest ih =>
        simp only [List.map_cons]
        rw [e2eModelInstDec_e2eModelInstEnc_of_gs d (hl d List.mem_cons_self),
            ih (fun d' hd' => hl d' (List.mem_cons_of_mem d hd'))]
    dsimp only [e2eDrvStateEnc, e2eDrvStateDec]
    rw [e2eMirrorBaseDec_e2eMirrorBaseEnc, hinst insts hgs, e2eValToKeyIndState_toVal]
    simp [Function.comp_def]

section StateProjections

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {O : ReductionDsl.Ops (e2eSig ℓ)}
  {Γ : List (Ty (e2eSig ℓ))}

def drvStE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) : Expr O Γ (e2eKeyIndStateTy ℓ S) :=
  .fst (.snd (.snd (.snd (.snd (.snd σE)))))

def drvBitE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) : Expr O Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd σE))))))

def drvPausedE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) : Expr O Γ .bool :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd σE))))))

def drvSetStE (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S)) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  .letE (.pair σE stE)
    (let s : Expr O _ (e2eDrvStateTy S ℓ) := .fst (.var .zero)
     let st : Expr O _ (e2eKeyIndStateTy ℓ S) := .snd (.var .zero)
     let r1 := Expr.snd s
     let r2 := Expr.snd r1
     let r3 := Expr.snd r2
     let r4 := Expr.snd r3
     let r5 := Expr.snd r4
     .pair (.fst s)
       (.pair (.fst r1)
         (.pair (.fst r2)
           (.pair (.fst r3)
             (.pair (.fst r4)
               (.pair st (.snd r5)))))))

def drvSetBitE (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (bE : Expr O Γ .bool) : Expr O Γ (e2eDrvStateTy S ℓ) :=
  .letE (.pair σE bE)
    (let s : Expr O _ (e2eDrvStateTy S ℓ) := .fst (.var .zero)
     let b : Expr O _ .bool := .snd (.var .zero)
     let r1 := Expr.snd s
     let r2 := Expr.snd r1
     let r3 := Expr.snd r2
     let r4 := Expr.snd r3
     let r5 := Expr.snd r4
     let r6 := Expr.snd r5
     .pair (.fst s)
       (.pair (.fst r1)
         (.pair (.fst r2)
           (.pair (.fst r3)
             (.pair (.fst r4)
               (.pair (.fst r5) (.pair b (.snd r6))))))))

@[simp] theorem eval_drvStE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ) :
    (drvStE σE).eval ρ = e2eKeyIndStateToVal σ.st := by
  simp [drvStE, Expr.eval, hσ, e2eDrvStateEnc]

@[simp] theorem eval_drvBitE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ) :
    (drvBitE σE).eval ρ = σ.b := by
  simp [drvBitE, Expr.eval, hσ, e2eDrvStateEnc]

@[simp] theorem eval_drvPausedE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ) :
    (drvPausedE σE).eval ρ = σ.paused := by
  simp [drvPausedE, Expr.eval, hσ, e2eDrvStateEnc]

@[simp] theorem eval_drvSetStE (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S)) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} {st' : SignalPqxdh.KeyIndState S}
    (hσ : σE.eval ρ = e2eDrvStateEnc σ) (hst : stE.eval ρ = e2eKeyIndStateToVal st') :
    (drvSetStE σE stE).eval ρ = e2eDrvStateEnc { σ with st := st' } := by
  simp [drvSetStE, Expr.eval, hσ, hst, e2eDrvStateEnc]

@[simp] theorem eval_drvSetBitE (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (bE : Expr O Γ .bool) (ρ : Env Γ)
    {σ : BHE2EDrvState S ℓ} (hσ : σE.eval ρ = e2eDrvStateEnc σ) :
    (drvSetBitE σE bE).eval ρ = e2eDrvStateEnc { σ with b := bE.eval ρ } := by
  simp [drvSetBitE, Expr.eval, hσ, e2eDrvStateEnc]

theorem cost_drvStE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) :
    (drvStE σE).cost = σE.cost + 6 := by
  simp [drvStE, Expr.cost]

theorem cost_drvBitE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) :
    (drvBitE σE).cost = σE.cost + 7 := by
  simp [drvBitE, Expr.cost]

theorem cost_drvPausedE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) :
    (drvPausedE σE).cost = σE.cost + 7 := by
  simp [drvPausedE, Expr.cost]

theorem cost_drvSetStE (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (drvSetStE σE stE).cost ≤ σE.cost + stE.cost + 60 := by
  simp only [drvSetStE, Expr.cost]; omega

theorem cost_drvSetBitE (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (bE : Expr O Γ .bool) :
    (drvSetBitE σE bE).cost ≤ σE.cost + bE.cost + 70 := by
  simp only [drvSetBitE, Expr.cost]; omega

theorem size_drvStE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) :
    (drvStE σE).size = σE.size + 6 := by
  simp [drvStE, Expr.size]

theorem size_drvBitE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) :
    (drvBitE σE).size = σE.size + 7 := by
  simp [drvBitE, Expr.size]

theorem size_drvPausedE (σE : Expr O Γ (e2eDrvStateTy S ℓ)) :
    (drvPausedE σE).size = σE.size + 7 := by
  simp [drvPausedE, Expr.size]

theorem size_drvSetStE (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (stE : Expr O Γ (e2eKeyIndStateTy ℓ S)) :
    (drvSetStE σE stE).size ≤ σE.size + stE.size + 60 := by
  simp only [drvSetStE, Expr.size]; omega

theorem size_drvSetBitE (σE : Expr O Γ (e2eDrvStateTy S ℓ))
    (bE : Expr O Γ .bool) :
    (drvSetBitE σE bE).size ≤ σE.size + bE.size + 70 := by
  simp only [drvSetBitE, Expr.size]; omega

end StateProjections

section RespNotRevealed

open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v cost_v eLet eCaseOpt eAny)

variable {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
  {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

/-- Per-instance reveal check (`DEV-C17`): `(respPrin, respSpkIdx)` is known and not in
`revealedSpks`. -/
def respNotRevealed {S : SignalPqxdh.Setup} (im : ModelDriverInstanceMeta S)
    (revSpks : List (Fin S.N_id × Fin S.N_recv)) : Bool :=
  match im.respPrin, im.respSpkIdx with
  | some u, some j => !revSpks.contains (u, j)
  | _, _ => false

def respNotRevealedE (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (imE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInstMetaTy S ℓ))
    (revE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (FinT S.N_id) (FinT S.N_recv)))) :
    Expr (e2eOps ℓ P C K decT encT) Γ .bool :=
  eLet (.pair imE revE) fun p =>
    eCaseOpt (.fst (.snd (.snd (.fst (v p))))) (.bool false) fun u =>
      eCaseOpt (.fst (.snd (.snd (.snd (.fst (v p)))))) (.bool false) fun j =>
        .not (eAny nCorr (.snd (v p)) fun e =>
          .and (e2ePureOp (.finEq S.N_id) (.pair (.fst (v e)) (v u)))
            (e2ePureOp (.finEq S.N_recv) (.pair (.snd (v e)) (v j))))

private theorem any_finEq_pair_eq_contains {n m : ℕ} (l : List (Fin n × Fin m))
    (u : Fin n) (j : Fin m) :
    l.any (fun e => (e.1 == u) && (e.2 == j)) = l.contains (u, j) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases a with ⟨a1, a2⟩
    rw [List.any_cons, List.contains_cons, ih]
    congr 1
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩

theorem eval_respNotRevealedE (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (imE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInstMetaTy S ℓ))
    (revE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (FinT S.N_id) (FinT S.N_recv))))
    (ρ : ReductionDsl.Env Γ) {im : ModelDriverInstanceMeta S}
    {revSpks : List (Fin S.N_id × Fin S.N_recv)}
    (him : imE.eval ρ = e2eInstMetaEnc im) (hrev : revE.eval ρ = revSpks)
    (hlen : revSpks.length ≤ nCorr) :
    (respNotRevealedE nCorr imE revE).eval ρ = respNotRevealed im revSpks := by
  unfold respNotRevealedE respNotRevealed
  simp only [eLet, eCaseOpt, eAny, v, Ext.wk, Expr.eval, ReductionDsl.Env.get, him, hrev,
    e2eInstMetaEnc, List.take_of_length_le hlen]
  rcases im.respPrin with _ | u <;> rcases im.respSpkIdx with _ | j <;>
    simp only [eval_e2ePureOp, E2EPureOp.eval, Expr.eval, ReductionDsl.Env.get]
  exact congrArg (fun b => !b) (any_finEq_pair_eq_contains revSpks u j)

theorem cost_respNotRevealedE (nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (imE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eInstMetaTy S ℓ))
    (revE : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod (FinT S.N_id) (FinT S.N_recv)))) :
    (respNotRevealedE nCorr imE revE).cost ≤ imE.cost + revE.cost + 20 * nCorr + 30 := by
  unfold respNotRevealedE
  dsimp only [v, Ext.wk]
  simp only [eLet, eCaseOpt, eAny, Expr.cost, cost_e2ePureOp, E2EPureOp.cost]
  omega

end RespNotRevealed

def prefixCtxEnc {ℓ : ℕ} (c : BHPrefixCtx) : (prefixCtxT (ℓ := ℓ)).denote :=
  (c.idA, (c.idB, c.spkCoins))

def prefixCtxDec {ℓ : ℕ} (v : (prefixCtxT (ℓ := ℓ)).denote) : BHPrefixCtx :=
  { idA := v.1, idB := v.2.1, spkCoins := v.2.2 }

@[simp] theorem prefixCtxDec_prefixCtxEnc {ℓ : ℕ} (c : BHPrefixCtx) :
    prefixCtxDec (prefixCtxEnc (ℓ := ℓ) c) = c := by
  cases c; rfl

@[simp] theorem prefixCtxEnc_prefixCtxDec {ℓ : ℕ} (v : (prefixCtxT (ℓ := ℓ)).denote) :
    prefixCtxEnc (prefixCtxDec v) = v := by
  rcases v with ⟨_, _, _⟩; rfl

def packSmRespEnc {ℓ : ℕ} (br : BHE2ESmResp ℓ) : (smRT (ℓ := ℓ) GhostStT).denote :=
  (br.1, (br.2.1.map recvResultEnc, br.2.2))

def unpackSmRespDec {ℓ : ℕ} (v : (smRT (ℓ := ℓ) GhostStT).denote) : BHE2ESmResp ℓ :=
  (v.1, v.2.1.map recvResultDec, v.2.2)

@[simp] theorem unpackSmRespDec_packSmRespEnc {ℓ : ℕ} (br : BHE2ESmResp ℓ) :
    unpackSmRespDec (packSmRespEnc br) = br := by
  rcases br with ⟨w, rr, st⟩
  cases rr <;> simp [packSmRespEnc, unpackSmRespDec, recvResultDec_recvResultEnc]

@[simp] theorem packSmRespEnc_unpackSmRespDec {ℓ : ℕ} (v : (smRT (ℓ := ℓ) GhostStT).denote) :
    packSmRespEnc (unpackSmRespDec v) = v := by
  rcases v with ⟨w, rr, st⟩
  cases rr <;> simp [packSmRespEnc, unpackSmRespDec, recvResultEnc_recvResultDec]

@[simp] theorem smRenc_id_eq_packSmRespEnc {ℓ : ℕ}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    smRenc (stT := GhostStT) id sq r = packSmRespEnc (bhPackSmResp sq r) := by
  rcases sq with (((_ | _) | _) | _) | _ <;> simp [smRenc, packSmRespEnc, bhPackSmResp]

@[simp] theorem smRdec_id_packSmRespEnc {ℓ : ℕ}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (br : BHE2ESmResp ℓ) :
    smRdec (stT := GhostStT) id sq (packSmRespEnc br) = bhUnpackSmResp sq br := by
  rcases br with ⟨w, rr, st⟩
  rcases sq with (((_ | _) | _) | _) | _
  · rfl
  · rfl
  · cases rr <;> simp [packSmRespEnc, smRdec, bhUnpackSmResp, recvResultDec_recvResultEnc]
  · cases rr <;> simp [packSmRespEnc, smRdec, bhUnpackSmResp, recvResultDec_recvResultEnc]
  · cases st <;> rfl

@[reducible] def e2eGameQT (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .sum (.sum (keyIndQT S) (sidT S)) (.prod .nat smQT)

@[reducible] def e2eGameRT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .sum (.sum keyIndRT (.opt .nat)) (smRT GhostStT)

def e2eGameDefaultRespE {ℓ : ℕ} {S : SignalPqxdh.Setup} {O : ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} (qE : Expr O Γ (e2eGameQT S ℓ)) : Expr O Γ (e2eGameRT ℓ) :=
  .caseSum qE
    (.caseSum (.var .zero)
      (.inl (.inl (.inl .unit)))
      (.inl (.inr .none)))
    (.inr (.pair .none (.pair .none .none)))

def mkTestSessionE {ℓ : ℕ} {S : SignalPqxdh.Setup} {O : ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} (sidE : Expr O Γ (sidT S)) : Expr O Γ (keyIndQT S) :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl sidE))))))))

def mkRevealSpkSkE {ℓ : ℕ} {S : SignalPqxdh.Setup} {O : ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))}
    (ujE : Expr O Γ (.prod (FinT S.N_id) (FinT S.N_recv))) : Expr O Γ (keyIndQT S) :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ujE))))))))))))

def defaultPrefixCtxE {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} :
    Expr (e2eOps ℓ P C K decT encT) Γ prefixCtxT :=
  let zeroId : Expr (e2eOps ℓ P C K decT encT) Γ IdKey :=
    e2ePureOp .idKeyOfPbytes (e2ePureOp (.pbytesLit 32 []) .unit)
  .pair zeroId (.pair zeroId (e2ePureOp (.bv256Lit 0#256) .unit))

@[simp] theorem eval_mkTestSessionE {ℓ : ℕ} {S : SignalPqxdh.Setup}
    {O : ReductionDsl.Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (sidE : Expr O Γ (sidT S)) (ρ : Env Γ) :
    (mkTestSessionE sidE).eval ρ = keyIndQenc (.testSession (sidOfV (sidE.eval ρ))) := by
  simp [mkTestSessionE, Expr.eval, keyIndQenc]

@[simp] theorem eval_mkRevealSpkSkE {ℓ : ℕ} {S : SignalPqxdh.Setup}
    {O : ReductionDsl.Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (ujE : Expr O Γ (.prod (FinT S.N_id) (FinT S.N_recv))) (ρ : Env Γ) :
    (mkRevealSpkSkE ujE).eval ρ =
      keyIndQenc (.revealSpkSk (ujE.eval ρ).1 (ujE.eval ρ).2) := by
  rcases h : ujE.eval ρ with ⟨u, j⟩
  simp [mkRevealSpkSkE, Expr.eval, keyIndQenc, h]

@[simp] theorem eval_defaultPrefixCtxE {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ) :
    (defaultPrefixCtxE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT)).eval ρ =
      prefixCtxEnc { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 } := by
  simp [defaultPrefixCtxE, prefixCtxEnc, bhIdKeyOf, Expr.eval, eval_e2ePureOp, E2EPureOp.eval]

theorem size_e2eGameDefaultRespE {ℓ : ℕ} {S : SignalPqxdh.Setup} {O : ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} (qE : Expr O Γ (e2eGameQT S ℓ)) :
    (e2eGameDefaultRespE qE).size ≤ qE.size + 20 := by
  simp only [e2eGameDefaultRespE, Expr.size]; omega

theorem size_mkTestSessionE {ℓ : ℕ} {S : SignalPqxdh.Setup} {O : ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} (sidE : Expr O Γ (sidT S)) :
    (mkTestSessionE sidE).size = sidE.size + 9 := by
  simp [mkTestSessionE, Expr.size]

theorem size_mkRevealSpkSkE {ℓ : ℕ} {S : SignalPqxdh.Setup} {O : ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))}
    (ujE : Expr O Γ (.prod (FinT S.N_id) (FinT S.N_recv))) :
    (mkRevealSpkSkE ujE).size = ujE.size + 13 := by
  simp [mkRevealSpkSkE, Expr.size]

theorem size_defaultPrefixCtxE {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} :
    (defaultPrefixCtxE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)).size ≤ 44 := by
  simp only [defaultPrefixCtxE, size_e2ePureOp, E2EPureOp.opSize, List.length_nil, Expr.size]
  omega

@[simp] theorem stepAIface_keyIndTargetIface (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    stepAIface ℓ (e2eKeyIndTargetIface S ℓ) = e2eKeyIndTargetIface S ℓ := rfl

@[simp] theorem stepAIface_sessionTargetIface (ℓ : ℕ) :
    stepAIface ℓ (e2eSessionTargetIface ℓ) = e2eSessionTargetIface ℓ := rfl

/-! ## Inductive Driver Invariants and Semantic Helpers -/

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
  /-- Adversarial `revealSpkSk` mirror list (`DEV-C17`), bounded by the same mirror budget. -/
  revSpks_le : σ.revealedSpks.length ≤ nCorr

/-- Single-budget specialization of `DrvMirrorBounded` after `qMir` mirrored queries and `qStart`
promoted instances. -/
abbrev DrvQueryBounded {S : SignalPqxdh.Setup} {ℓ : ℕ} (qMir qStart : ℕ)
    (σ : BHE2EDrvState S ℓ) : Prop :=
  DrvMirrorBounded qMir qMir qMir qMir qMir qStart σ

def DrvMetaAligned {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ) : Prop :=
  σ.instMeta.length = σ.insts.length

/-- Asserts `SmReachBounded C K qBound` for every active local instance in `σ`. -/
def DrvSessionsBounded {S : SignalPqxdh.Setup} {ℓ : ℕ} (C : Crypto) (K : MlKem)
    (qBound : ℕ) (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ d ∈ σ.insts, ∀ gs ∈ d.gs, SmReachBounded C K qBound gs

/-- Combined `KeyIndSetupBounded` and adversary-registered key-list bound on `KeyIndState S`. -/
structure KeyIndReachBounded (S : SignalPqxdh.Setup) (nAdv : ℕ)
    (st : SignalPqxdh.KeyIndState S) : Prop where
  setup : KeyIndSetupBounded S st
  advKeys_le : st.advKeys.length ≤ nAdv

theorem KeyIndReachBounded.empty (S : SignalPqxdh.Setup) (nAdv : ℕ) (secb : Bool) :
    KeyIndReachBounded S nAdv (SignalPqxdh.KeyIndState.empty S secb) :=
  ⟨KeyIndSetupBounded.empty S secb, by simp [SignalPqxdh.KeyIndState.empty]⟩

theorem KeyIndReachBounded.mono {S : SignalPqxdh.Setup} {nAdv nAdv' : ℕ}
    {st : SignalPqxdh.KeyIndState S}
    (h : KeyIndReachBounded S nAdv st) (hle : nAdv ≤ nAdv') :
    KeyIndReachBounded S nAdv' st :=
  ⟨h.setup, h.advKeys_le.trans hle⟩

theorem KeyIndReachBounded.pqxdhStep {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    {nAdv : ℕ} (kq : SignalPqxdh.KeyIndQuery S) {st : SignalPqxdh.KeyIndState S}
    (h : KeyIndReachBounded S nAdv st)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st)) :
    KeyIndReachBounded S (nAdv + 1) out.2 := by
  have ⟨hs, hadv, _⟩ := pqxdhKeyIndImpl1KeyReal_preserves_setupBounded kq h.setup hmem
  exact ⟨hs, hadv.trans (Nat.succ_le_succ h.advKeys_le)⟩

theorem DrvMirrorBounded.empty {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (nPrins nBundles nOpks nSends nCorr qStart : ℕ) (b : Bool) :
    DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart
      ({ b := b } : BHE2EDrvState S ℓ) :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
   Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem DrvMirrorBounded.mono {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {nP nP' nB nB' nO nO' nS nS' nC nC' qS qS' : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvMirrorBounded nP nB nO nS nC qS σ)
    (hP : nP ≤ nP') (hB : nB ≤ nB') (hO : nO ≤ nO') (hS : nS ≤ nS')
    (hC : nC ≤ nC') (hQ : qS ≤ qS') :
    DrvMirrorBounded nP' nB' nO' nS' nC' qS' σ :=
  ⟨h.prins_le.trans hP, h.bundles_le.trans hB, h.opks_le.trans hO,
   h.sends_le.trans hS, h.corrPrins_le.trans hC, h.insts_le.trans hQ,
   h.instMeta_le.trans hQ, h.revSpks_le.trans hC⟩

theorem drvMetaAligned_empty {S : SignalPqxdh.Setup} {ℓ : ℕ} (b : Bool) :
    DrvMetaAligned ({ b := b } : BHE2EDrvState S ℓ) := rfl

theorem DrvSessionsBounded.empty {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (qBound : ℕ) (b : Bool) :
    DrvSessionsBounded C K qBound ({ b := b } : BHE2EDrvState S ℓ) := by
  intro _ hd; cases hd

theorem DrvSessionsBounded.mono {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {qBound qBound' : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvSessionsBounded C K qBound σ) (hle : qBound ≤ qBound') :
    DrvSessionsBounded C K qBound' σ :=
  fun d hd gs hgs => (h d hd gs hgs).mono hle

theorem DrvMirrorBounded.mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {nP nB nO nS nC qS : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvMirrorBounded nP nB nO nS nC qS σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    DrvMirrorBounded (nP + 1) (nB + 1) (nO + 1) (nS + 1) (nC + 1) qS (bhE2EMirror σ kq kr) := by
  have hbase :
      (bhBaseMirror σ.toModelDriverBase kq kr).prins.length ≤ σ.prins.length + 1 ∧
      (bhBaseMirror σ.toModelDriverBase kq kr).bundles.length ≤ σ.bundles.length + 1 ∧
      (bhBaseMirror σ.toModelDriverBase kq kr).opks.length ≤ σ.opks.length + 1 ∧
      (bhBaseMirror σ.toModelDriverBase kq kr).sends.length ≤ σ.sends.length + 1 := by
    cases kq <;> cases kr <;> simp [bhBaseMirror]
  have hcorr : (bhE2EMirror σ kq kr).corrPrins.length ≤ σ.corrPrins.length + 1 := by
    cases kq <;> cases kr <;> simp [bhE2EMirror]
  have hrev : (bhE2EMirror σ kq kr).revealedSpks.length ≤ σ.revealedSpks.length + 1 := by
    cases kq <;> cases kr <;> simp [bhE2EMirror]
  exact ⟨hbase.1.trans (Nat.succ_le_succ h.prins_le),
         hbase.2.1.trans (Nat.succ_le_succ h.bundles_le),
         hbase.2.2.1.trans (Nat.succ_le_succ h.opks_le),
         hbase.2.2.2.trans (Nat.succ_le_succ h.sends_le),
         hcorr.trans (Nat.succ_le_succ h.corrPrins_le),
         h.insts_le, h.instMeta_le, hrev.trans (Nat.succ_le_succ h.revSpks_le)⟩

theorem drvMetaAligned_mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {σ : BHE2EDrvState S ℓ} (h : DrvMetaAligned σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    DrvMetaAligned (bhE2EMirror σ kq kr) := h

theorem DrvSessionsBounded.mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {C : Crypto} {K : MlKem} {qBound : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvSessionsBounded C K qBound σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    DrvSessionsBounded C K qBound (bhE2EMirror σ kq kr) := h

theorem DrvMirrorBounded.finishStartSpk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {nP nB nO nS nC qS : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvMirrorBounded nP nB nO nS nC qS σ)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (ac : BitVec 256) :
    DrvMirrorBounded nP nB nO nS nC (qS + 1)
      (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2 := by
  unfold bhE2EFinishStartSpk
  split
  · split_ifs
    · exact ⟨h.prins_le, h.bundles_le, h.opks_le, h.sends_le, h.corrPrins_le,
             by simp only [List.length_append, List.length_singleton]
                exact Nat.succ_le_succ h.insts_le,
             by simp only [List.length_append, List.length_singleton]
                exact Nat.succ_le_succ h.instMeta_le, h.revSpks_le⟩
    · exact h.mono (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _) (Nat.le_succ _)
  · exact h.mono (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _) (Nat.le_succ _)

theorem drvMetaAligned_finishStartSpk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {σ : BHE2EDrvState S ℓ} (h : DrvMetaAligned σ)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (ac : BitVec 256) :
    DrvMetaAligned (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2 := by
  unfold bhE2EFinishStartSpk
  split
  · split_ifs
    · simp [DrvMetaAligned] at h ⊢; omega
    · exact h
  · exact h

theorem DrvSessionsBounded.finishStartSpk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {qBound : ℕ} {σ : BHE2EDrvState S ℓ}
    (h : DrvSessionsBounded C K qBound σ)
    (sid : SignalPqxdh.SessionId S) (kr1 kr2 : SignalPqxdh.KeyIndResponse)
    (ac : BitVec 256) :
    DrvSessionsBounded C K qBound (bhE2EFinishStartSpk C K bMode? σ sid kr1 kr2 ac).2 := by
  unfold bhE2EFinishStartSpk
  split
  · split_ifs
    · intro d hd gs hgs
      rcases List.mem_append.mp hd with hd0 | hd1
      · exact h d hd0 gs hgs
      · simp only [List.mem_singleton] at hd1
        subst hd1
        rcases Option.mem_map.mp hgs with ⟨b, -, rfl⟩
        exact ⟨gameReachInv_initState C K _ _ ℓ _ _ b,
          ⟨by simp [initState], by simp [initState], by simp [initState],
           by simp [initState], by simp [initState], by simp [initState]⟩⟩
    · exact h
  · exact h

/-- Post-`startDR` slot-`k` check and promotion matching `bhShallowStepPreCtl`. -/
def bhPromoteSlotK {S : SignalPqxdh.Setup} {ℓ : ℕ} (k : ℕ) (idx? : Option ℕ)
    (σ' : BHE2EDrvState S ℓ) :
    (Option ℕ × BHE2EDrvState S ℓ) ⊕ (BHPrefixCtx × Option ℕ × BHE2EDrvState S ℓ) :=
  if k < σ'.insts.length then
    let ctx : BHPrefixCtx := match σ'.insts[k]? with
      | some d => { idA := d.idA, idB := d.idB, spkCoins := d.spkCoins }
      | none => { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }
    let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
    .inr (ctx, (idx?, { σ' with insts := insts', paused := true }))
  else .inl (idx?, σ')

def promoteSlotKEnc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (res : (Option ℕ × BHE2EDrvState S ℓ) ⊕ (BHPrefixCtx × Option ℕ × BHE2EDrvState S ℓ)) :
    (Ty.sum (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
      (.prod prefixCtxT (.prod (.opt .nat) (e2eDrvStateTy S ℓ)))).denote :=
  match res with
  | .inl (idx?, σ1) => .inl (idx?, e2eDrvStateEnc σ1)
  | .inr (ctx, (idx?, σ1)) => .inr (prefixCtxEnc ctx, (idx?, e2eDrvStateEnc σ1))

/-- Pre-query wire filter on a single session instance `(d, im)`. -/
def bhFilterSmQuery {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (d : BHModelInst S ℓ) (im : ModelDriverInstanceMeta S)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    Option ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :=
  match sq with
  | .inl (.inl (.inr (.A, c))) =>
    if (bhDecodePreKeyMsgE c).isSome then none else some sq
  | .inl (.inr (.A, c)) =>
    if (bhDecodePreKeyMsgE c).isSome then none else some sq
  | .inl (.inl (.inr (.B, c))) =>
    if !im.bobAccepted then
      match bhDecodePreKeyMsgE c with
      | some m =>
        if c == wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
          some (.inl (.inl (.inr (.B, m.inner))))
        else none
      | none => none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == d.hdr then
          some (.inl (.inl (.inr (.B, m.inner))))
        else none
      | none => some (.inl (.inl (.inr (.B, c))))
  | .inl (.inr (.B, c)) =>
    if !im.bobAccepted then none
    else
      match bhDecodePreKeyMsgE c with
      | some m =>
        if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
           decide (m.inner.length + 2048 < 2 ^ 32) then
          some (.inl (.inr (.B, m.inner)))
        else none
      | none => some (.inl (.inr (.B, c)))
  | _ => some sq

/-- Semantic specification of the Stage-2 external promoted-session `SM.spec` step on slot `k`. -/
def bhExtSmStep {S : SignalPqxdh.Setup} {ℓ : ℕ} (k : ℕ) (σ : BHE2EDrvState S ℓ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    OracleComp (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) :=
  if !bhE2EDrvInstClean σ k then
    pure ((none, none, none), σ)
  else
    match σ.insts[k]?, σ.instMeta[k]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d then
        let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
        pure ((none, none, none), { σ with instMeta := σ.instMeta.set k imCorr })
      else
        match bhFilterSmQuery d im sq with
        | none => pure ((none, none, none), σ)
        | some sq' => do
          let r ← query
            (spec := unifSpec +
              CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
            (.inr sq')
          let im' := if !im.bobAccepted && bhIsBobAcceptSMResp sq' r then
              { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
            else im
          pure (bhPackSmResp sq' r, { σ with instMeta := σ.instMeta.set k im' })
    | _, _ => pure ((none, none, none), σ)

private theorem mem_set_or {α : Type} :
    ∀ (l : List α) (i : ℕ) (x y : α), y ∈ l.set i x → y = x ∨ y ∈ l
  | [], _, _, _, hy => nomatch hy
  | _ :: as, 0, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ hmem)
  | a :: as, i + 1, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inr List.mem_cons_self
    · rcases mem_set_or as i x y hmem with rfl | hmem'
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a hmem')

theorem bhE2EStepLocalSm_preserves {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {nP nB nO nS nC qS qBound : ℕ} {σ : BHE2EDrvState S ℓ}
    (hMir : DrvMirrorBounded nP nB nO nS nC qS σ)
    (hMeta : DrvMetaAligned σ)
    (hSess : DrvSessionsBounded C K qBound σ)
    (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    DrvMirrorBounded nP nB nO nS nC qS out.2 ∧
      DrvMetaAligned out.2 ∧
      DrvSessionsBounded C K (qBound + 1) out.2 ∧
      out.2.st = σ.st := by
  have hpure : out ∈ support (pure ((none, none, none), σ) :
      ProbComp (BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) →
      DrvMirrorBounded nP nB nO nS nC qS out.2 ∧
        DrvMetaAligned out.2 ∧
        DrvSessionsBounded C K (qBound + 1) out.2 ∧
        out.2.st = σ.st := by
    simp only [support_pure, Set.mem_singleton_iff]
    intro heq; subst heq
    exact ⟨hMir, hMeta, hSess.mono (Nat.le_succ _), rfl⟩
  unfold bhE2EStepLocalSm at hout
  by_cases hcl : !bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte] at hout; exact hpure hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp only [hd] at hout; exact hpure hout
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp only [hd, him] at hout; exact hpure hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout
          exact ⟨⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le,
                  hMir.corrPrins_le, hMir.insts_le, by simp [hMir.instMeta_le], hMir.revSpks_le⟩,
                 by simp [DrvMetaAligned] at hMeta ⊢; exact hMeta,
                 hSess.mono (Nat.le_succ _), rfl⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => simp only [hgs] at hout; exact hpure hout
          | some gs =>
            simp only [hgs] at hout
            have hgsInv : SmReachBounded C K qBound gs :=
              hSess d (List.mem_of_getElem? hd) gs hgs
            have hrunStd :
                ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ)
                    (BitVec 512) Bytes).Domain),
                out ∈ support (do
                  let (r, gs') ← (oracleImplR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins) (2 + 1) qep
                    (configRefuseEarlyBobCorr decT encT) q').run gs
                  let accepted := bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (bhPackSmResp q' r, σ1)) →
                DrvMirrorBounded nP nB nO nS nC qS out.2 ∧
                  DrvMetaAligned out.2 ∧
                  DrvSessionsBounded C K (qBound + 1) out.2 ∧
                  out.2.st = σ.st := by
              intro q' hrun
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrun
              rcases hrun with ⟨⟨r, gs'⟩, hstep, rfl⟩
              have hgs' : SmReachBounded C K (qBound + 1) gs' :=
                smReachBounded_oracleImplR C K d.idA d.idB ℓ (2 + 1) qep qBound d.spkCoins _ q'
                  hgsInv hstep
              refine ⟨⟨hMir.prins_le, hMir.bundles_le, hMir.opks_le, hMir.sends_le,
                       hMir.corrPrins_le, by simp [hMir.insts_le], by simp [hMir.instMeta_le],
                       hMir.revSpks_le⟩,
                      by simp [DrvMetaAligned] at hMeta ⊢; exact hMeta, ?_, rfl⟩
              intro d' hd' gs0 hgs0
              rcases mem_set_or σ.insts i { d with gs := some gs' } d' hd' with rfl | hmem
              · simp only [Option.mem_def, Option.some.injEq] at hgs0
                subst hgs0; exact hgs'
              · exact (hSess d' hmem gs0 hgs0).mono (Nat.le_succ _)
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · dsimp only at hout; exact hrunStd _ hout
            · dsimp only at hout; exact hrunStd _ hout
            · cases pDl
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunStd _ hout
              · dsimp only at hout
                split_ifs at hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; dsimp only at hout; exact hrunStd _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
            · cases pIj
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunStd _ hout
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · cases hdec : bhDecodePreKeyMsgE cIj
                  · rw [hdec] at hout; dsimp only at hout; exact hrunStd _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
            · dsimp only at hout; exact hrunStd _ hout

/-! ## `DrvStateGuardFreshIface`: Driver Guards, Mirrors, and Freshness Contract -/

/-- Interface contract for driver-state initialization, admissibility guards, mirror updates,
cleanliness/win predicates, and end-of-game freshness evaluation. -/
structure DrvStateGuardFreshIface (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  emptyDrvStateE : ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ .bool →
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ)
  emptyDrvStateCost : ℕ
  emptyDrvStateE_cost : ∀ {Γ : List (Ty (e2eSig ℓ))}
    (bE : Expr (e2eOps ℓ P C K decT encT) Γ .bool),
    (emptyDrvStateE bE).cost ≤ bE.cost + emptyDrvStateCost
  emptyDrvStateE_eval : ∀ {Γ : List (Ty (e2eSig ℓ))}
    (bE : Expr (e2eOps ℓ P C K decT encT) Γ .bool) (ρ : Env Γ),
    (emptyDrvStateE bE).eval ρ = e2eDrvStateEnc ({ b := bE.eval ρ } : BHE2EDrvState S ℓ)

  initKindC : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))},
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ (e2eDrvStateTy S ℓ)
  initKindCost : ℕ
  initKindC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))},
    (initKindC (Γ := Γ) I₀).cost ≤ initKindCost
  initKindC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))} (w : (stepAIface ℓ I₀).Tag → ℕ),
    (initKindC (Γ := Γ) I₀).queries w (fun _ => 0) = 0
  initKindC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ),
    (initKindC (Γ := Γ) I₀).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun b : Bool => e2eDrvStateEnc ({ b := b } : BHE2EDrvState S ℓ)) <$>
          ($ᵗ Bool : ProbComp Bool))

  /-- `KeyIndQuery` admissibility filter combining `bhDrvKiQueryOk` and `!bhNoOpkRespPromoted`
  on `.corruptIK u`. -/
  kiQueryOkE : ℕ → ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S) →
    Expr (e2eOps ℓ P C K decT encT) Γ .bool
  kiQueryOkCost : ℕ → ℕ → ℕ
  kiQueryOkE_cost : ∀ (nPrins qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)),
    (kiQueryOkE nPrins qStart σE kqE).cost ≤ σE.cost + kqE.cost + kiQueryOkCost nPrins qStart
  kiQueryOkE_eval : ∀ (nPrins qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S),
    SignalPqxdh.WellFormedPrimitivesδ P →
    σE.eval ρ = e2eDrvStateEnc σ →
    kqE.eval ρ = keyIndQenc kq →
    σ.prins.length ≤ nPrins →
    σ.instMeta.length ≤ qStart →
    (kiQueryOkE nPrins qStart σE kqE).eval ρ =
      (bhDrvKiQueryOk P σ.toModelDriverBase kq &&
        !(match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false))

  mirrorE : ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S) →
    Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT →
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ)
  mirrorCost : ℕ
  mirrorE_cost : ∀ {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (krE : Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT),
    (mirrorE σE kqE krE).cost ≤ σE.cost + kqE.cost + krE.cost + mirrorCost
  mirrorE_eval : ∀ {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (krE : Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse),
    σE.eval ρ = e2eDrvStateEnc σ →
    kqE.eval ρ = keyIndQenc kq →
    krE.eval ρ = keyIndRenc kr →
    (mirrorE σE kqE krE).eval ρ = e2eDrvStateEnc (bhE2EMirror σ kq kr)

  prepStartSpkE : ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ (sidT S) →
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt (.prod (FinT S.N_id) (FinT S.N_recv)))
  prepStartSpkCost : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  prepStartSpkE_cost : ∀ (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)),
    (prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE).cost ≤
      σE.cost + sidE.cost + prepStartSpkCost qStart nPrins nBundles nOpks nSends
  prepStartSpkE_eval : ∀ (qStart nPrins nBundles nOpks nSends nCorr : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S),
    σE.eval ρ = e2eDrvStateEnc σ →
    sidE.eval ρ = sidV sid →
    DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ →
    nCorr ≤ nPrins →
    (prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE).eval ρ =
      (bhE2EGuard σ sid).map (fun (_, _, uj) => uj)

  drvWonE : ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ .bool →
    Expr (e2eOps ℓ P C K decT encT) Γ .bool
  drvWonCost : ℕ → ℕ
  drvWonE_cost : ∀ (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (bE : Expr (e2eOps ℓ P C K decT encT) Γ .bool),
    (drvWonE qStart σE bE).cost ≤ σE.cost + bE.cost + drvWonCost qStart
  drvWonE_eval : ∀ (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (bE : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ),
    σE.eval ρ = e2eDrvStateEnc σ →
    σ.insts.length ≤ qStart →
    (drvWonE qStart σE bE).eval ρ = bhE2EDrvWon σ (bE.eval ρ)

  finishKindE : ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ .bool →
    Expr (e2eOps ℓ P C K decT encT) Γ .bool
  finishKindCost : ℕ → ℕ
  finishKindE_cost : ∀ (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E : Expr (e2eOps ℓ P C K decT encT) Γ .bool),
    (finishKindE qStart σE b'E).cost ≤ σE.cost + b'E.cost + finishKindCost qStart
  finishKindE_eval : ∀ (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ),
    σE.eval ρ = e2eDrvStateEnc σ →
    σ.insts.length ≤ qStart →
    (finishKindE qStart σE b'E).eval ρ = (b'E.eval ρ == σ.b || bhE2EDrvWon σ σ.b)

  finishPrefixC : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T),
    ℕ → ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ .bool →
    Expr (e2eOps ℓ P C K decT encT) Γ .bool →
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ .bool
  finishPrefixCost : ℕ → ℕ → ℕ
  finishPrefixC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : Expr (e2eOps ℓ P C K decT encT) Γ .bool),
    (finishPrefixC I₀ qStart nAdv σE b'E flipE).cost ≤
      σE.cost + b'E.cost + flipE.cost + finishPrefixCost qStart nAdv
  finishPrefixC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (w : (stepAIface ℓ I₀).Tag → ℕ),
    (finishPrefixC I₀ qStart nAdv σE b'E flipE).queries w (fun _ => 0) = 0
  finishPrefixC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ)
    (_ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (_qep : ℕ),
    SignalPqxdh.WellFormedPrimitivesδ P →
    σE.eval ρ = e2eDrvStateEnc σ →
    σ.insts.length ≤ qStart →
    KeyIndReachBounded S nAdv σ.st →
    (finishPrefixC I₀ qStart nAdv σE b'E flipE).eval ρ =
      (stepAIface ℓ I₀).liftP
        (bhShallowFinishPrefix P σ (b'E.eval ρ) (flipE.eval ρ))

/-! ## `LocalSessionStepIface`: Local Multi-Session `bhE2EStepLocalSm` Contract -/

/-- Interface contract for simulating `bhE2EStepLocalSm` inside `ReductionDsl`. -/
structure LocalSessionStepIface (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  stepLocalSmC : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T),
    ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ .nat →
    Expr (e2eOps ℓ P C K decT encT) Γ smQT →
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod (smRT GhostStT) (e2eDrvStateTy S ℓ))
  stepLocalSmCost : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  stepLocalSmC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (idxE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT),
    (stepLocalSmC I₀ qStart nCorr nPrins qBound qep σE idxE qE).cost ≤
      σE.cost + idxE.cost + qE.cost + stepLocalSmCost qStart nCorr nPrins qBound qep
  stepLocalSmC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (idxE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (w : (stepAIface ℓ I₀).Tag → ℕ),
    (stepLocalSmC I₀ qStart nCorr nPrins qBound qep σE idxE qE).queries w (fun _ => 0) = 0
  stepLocalSmC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (idxE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
    σE.eval ρ = e2eDrvStateEnc σ →
    idxE.eval ρ = i →
    qE.eval ρ = smQenc sq →
    σ.insts.length ≤ qStart →
    DrvMetaAligned σ →
    σ.corrPrins.length ≤ nCorr →
    σ.revealedSpks.length ≤ nCorr →
    σ.prins.length ≤ nPrins →
    DrvSessionsBounded C K qBound σ →
    (stepLocalSmC I₀ qStart nCorr nPrins qBound qep σE idxE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (packSmRespEnc out.1, e2eDrvStateEnc out.2)) <$>
          bhE2EStepLocalSm C K qep decT encT σ i sq)

theorem LocalSessionStepIface.stepLocalSmC_eval_qdec {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (sim : LocalSessionStepIface ℓ S P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (idxE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ)
    (hσE : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart)
    (hMeta : DrvMetaAligned σ)
    (hCorr : σ.corrPrins.length ≤ nCorr)
    (hRev : σ.revealedSpks.length ≤ nCorr)
    (hPrins : σ.prins.length ≤ nPrins)
    (hSess : DrvSessionsBounded C K qBound σ) :
    let sq := smQdec (ℓ := ℓ) (St := GhostState Bytes) (qE.eval ρ)
    (sim.stepLocalSmC I₀ qStart nCorr nPrins qBound qep σE idxE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (packSmRespEnc out.1, e2eDrvStateEnc out.2)) <$>
          bhE2EStepLocalSm C K qep decT encT σ (idxE.eval ρ) sq) :=
  sim.stepLocalSmC_eval I₀ qStart nCorr nPrins qBound qep σE idxE qE ρ σ (idxE.eval ρ)
    (smQdec (ℓ := ℓ) (St := GhostState Bytes) (qE.eval ρ))
    hσE rfl (smQenc_smQdec (qE.eval ρ)).symm hInsts hMeta hCorr hRev hPrins hSess

/-! ## `StartAndExtSmIface`: Session Promotion and External `SM.spec` Routing Contract -/

/-- Interface contract for `bhE2EFinishStartSpk` session initialization, slot-`k` promotion
(`bhPromoteSlotK`), and Stage-2 external `SM.spec` query routing (`bhExtSmStep`). -/
structure StartAndExtSmIface (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  finishStartSpkC : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T),
    ℕ → ℕ → ℕ → ℕ → ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt .bool) →
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ (sidT S) →
    Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT →
    Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT →
    Expr (e2eOps ℓ P C K decT encT) Γ BV256 →
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
  finishStartSpkCost : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  finishStartSpkC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt .bool))
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (kr1E kr2E : Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT)
    (acE : Expr (e2eOps ℓ P C K decT encT) Γ BV256),
    (finishStartSpkC I₀ qStart nPrins nBundles nOpks nSends bModeE σE sidE kr1E kr2E acE).cost ≤
      bModeE.cost + σE.cost + sidE.cost + kr1E.cost + kr2E.cost + acE.cost +
        finishStartSpkCost qStart nPrins nBundles nOpks nSends
  finishStartSpkC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt .bool))
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (kr1E kr2E : Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT)
    (acE : Expr (e2eOps ℓ P C K decT encT) Γ BV256)
    (w : (stepAIface ℓ I₀).Tag → ℕ),
    (finishStartSpkC I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E acE).queries w (fun _ => 0) = 0
  finishStartSpkC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends nCorr : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt .bool))
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (kr1E kr2E : Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT)
    (acE : Expr (e2eOps ℓ P C K decT encT) Γ BV256)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S)
    (kr1 kr2 : SignalPqxdh.KeyIndResponse),
    σE.eval ρ = e2eDrvStateEnc σ →
    sidE.eval ρ = sidV sid →
    kr1E.eval ρ = keyIndRenc kr1 →
    kr2E.eval ρ = keyIndRenc kr2 →
    DrvMirrorBounded nPrins nBundles nOpks nSends nCorr qStart σ →
    nCorr ≤ nPrins →
    (finishStartSpkC I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E acE).eval ρ =
      let res := bhE2EFinishStartSpk C K (bModeE.eval ρ) σ sid kr1 kr2 (acE.eval ρ)
      pure (res.1, e2eDrvStateEnc res.2)

  promoteSlotKC : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T),
    ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ .nat →
    Expr (e2eOps ℓ P C K decT encT) Γ (.opt .nat) →
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.sum (.prod (.opt .nat) (e2eDrvStateTy S ℓ))
        (.prod prefixCtxT (.prod (.opt .nat) (e2eDrvStateTy S ℓ))))
  promoteSlotKCost : ℕ → ℕ
  promoteSlotKC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ)),
    (promoteSlotKC I₀ nInsts kE idxOptE σE).cost ≤
      kE.cost + idxOptE.cost + σE.cost + promoteSlotKCost nInsts
  promoteSlotKC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (w : (stepAIface ℓ I₀).Tag → ℕ),
    (promoteSlotKC I₀ nInsts kE idxOptE σE).queries w (fun _ => 0) = 0
  promoteSlotKC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (ρ : Env Γ) (σ' : BHE2EDrvState S ℓ),
    σE.eval ρ = e2eDrvStateEnc σ' →
    σ'.insts.length ≤ nInsts →
    (promoteSlotKC I₀ nInsts kE idxOptE σE).eval ρ =
      pure (promoteSlotKEnc (bhPromoteSlotK (kE.eval ρ) (idxOptE.eval ρ) σ'))

  extSmStepC : ℕ → ℕ → ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ .nat →
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ smQT →
    Comp (e2eOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ) Γ
      (.prod (smRT GhostStT) (e2eDrvStateTy S ℓ))
  extSmStepCost : ℕ → ℕ → ℕ → ℕ
  extSmStepC_cost : ∀ (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sqE : Expr (e2eOps ℓ P C K decT encT) Γ smQT),
    (extSmStepC qStart nCorr nPrins kE σE sqE).cost ≤
      kE.cost + σE.cost + sqE.cost + extSmStepCost qStart nCorr nPrins
  extSmStepC_queries : ∀ (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sqE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (w : E2ESessionTag → ℕ) (wmax : ℕ),
    (∀ g, w g ≤ wmax) →
    (extSmStepC qStart nCorr nPrins kE σE sqE).queries w (fun _ => 0) ≤ wmax
  extSmStepC_eval : ∀ (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sqE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (ρ : Env Γ) (k : ℕ) (σ : BHE2EDrvState S ℓ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
    kE.eval ρ = k →
    σE.eval ρ = e2eDrvStateEnc σ →
    sqE.eval ρ = smQenc sq →
    σ.insts.length ≤ qStart →
    DrvMetaAligned σ →
    σ.corrPrins.length ≤ nCorr →
    σ.revealedSpks.length ≤ nCorr →
    σ.prins.length ≤ nPrins →
    (extSmStepC qStart nCorr nPrins kE σE sqE).eval ρ =
      ((fun out => (packSmRespEnc out.1, e2eDrvStateEnc out.2)) <$> bhExtSmStep k σ sq)

theorem StartAndExtSmIface.extSmStepC_queries_one {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (sim : StartAndExtSmIface ℓ S P C K decT encT)
    (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sqE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) :
    (sim.extSmStepC qStart nCorr nPrins kE σE sqE).queries (fun _ => 1) (fun _ => 0) ≤ 1 :=
  sim.extSmStepC_queries qStart nCorr nPrins kE σE sqE (fun _ => 1) 1 (fun _ => le_refl 1)

theorem StartAndExtSmIface.extSmStepC_eval_qdec {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (sim : StartAndExtSmIface ℓ S P C K decT encT)
    (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sqE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (ρ : Env Γ) (σ : BHE2EDrvState S ℓ)
    (hσE : σE.eval ρ = e2eDrvStateEnc σ)
    (hInsts : σ.insts.length ≤ qStart)
    (hMeta : DrvMetaAligned σ)
    (hCorr : σ.corrPrins.length ≤ nCorr)
    (hRev : σ.revealedSpks.length ≤ nCorr)
    (hPrins : σ.prins.length ≤ nPrins) :
    let sq := smQdec (ℓ := ℓ) (St := GhostState Bytes) (sqE.eval ρ)
    (sim.extSmStepC qStart nCorr nPrins kE σE sqE).eval ρ =
      ((fun out => (packSmRespEnc out.1, e2eDrvStateEnc out.2)) <$>
        bhExtSmStep (kE.eval ρ) σ sq) :=
  sim.extSmStepC_eval qStart nCorr nPrins kE σE sqE ρ (kE.eval ρ) σ
    (smQdec (ℓ := ℓ) (St := GhostState Bytes) (sqE.eval ρ))
    rfl hσE (smQenc_smQdec (sqE.eval ρ)).symm hInsts hMeta hCorr hRev hPrins

/-! ## Combined Sub-Program Interface Bundle -/

/-- Bundle of the five `ReductionDsl` sub-program interfaces consumed by `kindRed` and
`prefixRed`. -/
structure M3SubprogramsIface (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  pqxdh : PqxdhSimIface ℓ S P C K decT encT
  dr : DrSessionSimIface ℓ P C K decT encT
  drv : DrvStateGuardFreshIface ℓ S P C K decT encT
  localSm : LocalSessionStepIface ℓ S P C K decT encT
  startExt : StartAndExtSmIface ℓ S P C K decT encT

/-- Compositional syntax-size (`Expr.size` / `Comp.size`) bounds for an `M3SubprogramsIface`
bundle. -/
structure M3SubprogramsSizeIface {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (subs : M3SubprogramsIface ℓ S P C K decT encT) where
  emptyDrvStateSize : ℕ
  emptyDrvStateE_size : ∀ {Γ : List (Ty (e2eSig ℓ))}
    (bE : Expr (e2eOps ℓ P C K decT encT) Γ .bool),
    (subs.drv.emptyDrvStateE bE).size ≤ bE.size + emptyDrvStateSize
  initKindSize : ℕ
  initKindC_size : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))},
    (subs.drv.initKindC (Γ := Γ) I₀).size ≤ initKindSize
  kiQueryOkSize : ℕ → ℕ → ℕ
  kiQueryOkE_size : ∀ (nPrins qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)),
    (subs.drv.kiQueryOkE nPrins qStart σE kqE).size ≤
      σE.size + kqE.size + kiQueryOkSize nPrins qStart
  mirrorSize : ℕ
  mirrorE_size : ∀ {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (kqE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (krE : Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT),
    (subs.drv.mirrorE σE kqE krE).size ≤ σE.size + kqE.size + krE.size + mirrorSize
  prepStartSpkSize : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  prepStartSpkE_size : ∀ (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S)),
    (subs.drv.prepStartSpkE qStart nPrins nBundles nOpks nSends σE sidE).size ≤
      σE.size + sidE.size + prepStartSpkSize qStart nPrins nBundles nOpks nSends
  finishKindSize : ℕ → ℕ
  finishKindE_size : ∀ (qStart : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E : Expr (e2eOps ℓ P C K decT encT) Γ .bool),
    (subs.drv.finishKindE qStart σE b'E).size ≤ σE.size + b'E.size + finishKindSize qStart
  finishPrefixSize : ℕ → ℕ → ℕ
  finishPrefixC_size : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nAdv : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (b'E flipE : Expr (e2eOps ℓ P C K decT encT) Γ .bool),
    (subs.drv.finishPrefixC I₀ qStart nAdv σE b'E flipE).size ≤
      σE.size + b'E.size + flipE.size + finishPrefixSize qStart nAdv
  pqxdhStepSize : ℕ → ℕ
  pqxdhStepC_size : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)),
    (subs.pqxdh.stepC I₀ nAdv stE qE).size ≤ stE.size + qE.size + pqxdhStepSize nAdv
  stepLocalSmSize : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  stepLocalSmC_size : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nCorr nPrins qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (idxE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT),
    (subs.localSm.stepLocalSmC I₀ qStart nCorr nPrins qBound qep σE idxE qE).size ≤
      σE.size + idxE.size + qE.size + stepLocalSmSize qStart nCorr nPrins qBound qep
  finishStartSpkSize : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  finishStartSpkC_size : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qStart nPrins nBundles nOpks nSends : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (bModeE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt .bool))
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sidE : Expr (e2eOps ℓ P C K decT encT) Γ (sidT S))
    (kr1E kr2E : Expr (e2eOps ℓ P C K decT encT) Γ keyIndRT)
    (acE : Expr (e2eOps ℓ P C K decT encT) Γ BV256),
    (subs.startExt.finishStartSpkC I₀ qStart nPrins nBundles nOpks nSends
      bModeE σE sidE kr1E kr2E acE).size ≤
      bModeE.size + σE.size + sidE.size + kr1E.size + kr2E.size + acE.size +
        finishStartSpkSize qStart nPrins nBundles nOpks nSends
  promoteSlotKSize : ℕ → ℕ
  promoteSlotKC_size : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (nInsts : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (idxOptE : Expr (e2eOps ℓ P C K decT encT) Γ (.opt .nat))
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ)),
    (subs.startExt.promoteSlotKC I₀ nInsts kE idxOptE σE).size ≤
      kE.size + idxOptE.size + σE.size + promoteSlotKSize nInsts
  extSmStepSize : ℕ → ℕ → ℕ → ℕ
  extSmStepC_size : ∀ (qStart nCorr nPrins : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (kE : Expr (e2eOps ℓ P C K decT encT) Γ .nat)
    (σE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eDrvStateTy S ℓ))
    (sqE : Expr (e2eOps ℓ P C K decT encT) Γ smQT),
    (subs.startExt.extSmStepC qStart nCorr nPrins kE σE sqE).size ≤
      kE.size + σE.size + sqE.size + extSmStepSize qStart nCorr nPrins

end Computational.Proofs.E2E.Dsl.M3Interfaces
