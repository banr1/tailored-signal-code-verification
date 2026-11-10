/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.LeafCostBounds
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1
public import Computational.Proofs.LibsignalCli.CliPqAdapterDefs
public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import Computational.Specifications.Session.StatementSession
import Computational.Proofs.E2E.Dsl.ClampsLossless
import Computational.Proofs.E2E.Dsl.SmReachInv
import Computational.Proofs.E2E.Dsl.SmReachInvParty
import Computational.Proofs.E2E.BhAdapterIjHelpersV1Core
import Computational.Proofs.LibsignalCli.Oom.Faithful
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import VCVio.EvalDist.Monad.Basic

/-!
# Costed Binary-Harness to Model-State Adapter

Constructs the `ReductionDsl.CostedReduction` adapters `cliToModelAdapterProg` (list-backed) and
`cliToModelAdapterProgTbl` (`Ty.tbl`-backed) over `e2eAdapterOps`, `e2eBhAdapterCodec`, and
`e2eBhAdapterIface`. Establishes concrete step-cost, syntax-size, and query-count bounds,
per-instance `IsQueryBoundP` transfer, and exact experiment equivalence with `L_bh`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Computational.Proofs.E2E.Dsl.CliAdapterCosted

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Expr Comp Ops Samplers Iface GameCodec
  CostedReduction handlerImpl OpsSizeHonest SampSizeHonest bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (MakesAtMostQueries)
open CryptoGames.LibsignalSession (PublicKey IdentityKey Crypto GhostState)
open CryptoVerification.LibsignalSession (CostedFits GRedBounded)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SignalSession (stdinCapBytes)
open CryptoVerification.E2E (Bytes BinState RecordExtras BHDRCtlQuery bhDrCtlSpec BHAdapterInstMeta
  ModelDriverBase BHE2EDrvState BHE2ESmResp bhGameSpec bhTargetGameSpec bhInitRegId bhBaseMirror
  bhBaseOpkOk bhDecodePreKeyMsgE bhHdrOfPreKeyMsg bhExpectedPreKeyMsg bhWrapSendOut
  bhBinStateOfParty bhSmDefaultWithSpqr CliGameAdversary cliGameSpec cliGameAdversaryReassoc
  CliGameAdversaryQueryBounded CliGameAdversaryPerInstanceBounded bhIsInstQueryWithSpqr
  BhShallowRed bhFwdU L_bh bhShallowWrapWhisper bhShallowSplitWhisper bhShallowParsePreKey
  bhShallowStepMirrorGuard bhShallowUpdateInstMeta bhShallowBobUpdate bhShallowAliceUpdate
  bhShallowQueryTarget bhShallowAdapterGameStep bhShallowAdapterImpl
  bhClassifyComposed bhClassifyGame
  bhClassifyGameOnly bhClassifyTarget bhClassifyTargetOnly isQueryBoundP_bhAdvRun
  cliE2EDrvImplWith cliE2EExpWithKi CliAdapterState cliAdapterInitState cliAdapterStepImplWith
  simulateQ_cliE2EDrvImplWith_adapter_run wirePrekey wireWhisper shortCiphertext
  allTestedSessionsFresh bhDrvKiQueryOk bhE2EDrvInstClean bhE2EDrvWon bhE2EInstIkACorr
  bhE2EMirror bhE2EStepLocalSm bhIsBobAcceptSMResp bhIsBobRecvSMQuery bhNoOpkRespPromoted
  bhPackSmResp bhUnpackSmResp compositionLocalStart configRefuseEarlyBobCorr oracleImplRM
  paramsIdsWithSpqr sessionSchemeFixedSpk smSchemeCoinLogged)
open Computational.Proofs.LibsignalCli.Oom.Faithful (instLawfulMonadWriterTList)
open CryptoVerification.E2E.Costed (e2eSig PB B PU32 U32 FinT PlainT BV512 BinStT GhostStT
  bundleT bundleV bundleOfV hdrT hdrV hdrOfV sidT sidV sidOfV keyIndQT keyIndQenc keyIndQdec
  keyIndRT keyIndRenc keyIndRdec smQT smQenc smRT smRdec recvResultT recvResultEnc recvResultDec
  partyToBool boolToParty E2EPureOp e2ePureOps e2eAdapterOps E2EAdapterTag e2eSamplers
  e2eAdapterIface e2eAdapterCodec gRedBounded_of_bounds costedFits_iff_fits
  e2eRecordExtras e2eEncodeSessionRecord)
open Computational.Proofs.E2E.Dsl.TablesHonest (adapterPureOp eval_adapterPureOp cost_adapterPureOp
  adapterInstMetaT adapterStateTy adapterNoneSmRespExpr adapterCrArm adapterCrArm_cost
  e2eAdapterOps_sizeHonest e2eSamplers_sizeHonest
  bundleOfV_bundleV bundleV_bundleOfV hdrOfV_hdrV hdrV_hdrOfV
  sidOfV_sidV keyIndQdec_keyIndQenc keyIndRdec_keyIndRenc
  recvResultDec_recvResultEnc boolToParty_partyToBool partyToBool_boolToParty)
open Computational.Proofs.E2E.Dsl.LeafCostBounds (e2eAdapterCostBudget bhAdapterCostBudgetHonest
  e2eAdapterCostBudgetPreBlock e2eAdapterCostBudgetUniform12 m0AdapterCostBudget
  adapterPerStepBudget adapterPerStepBudgetPreBlock
  totalCost_le_e2eAdapterCostBudgetPreBlock_of_step totalCost_le_e2eAdapterCostBudget_of_step
  e2eAdapterCostBudgetPreBlock_le_uniform12 e2eAdapterCostBudgetUniform12_le_m0AdapterCostBudget
  fits_bool_two)

/-! ## Codec abbreviations and mirror state -/

def bhCtlUnStart {S : SignalPqxdh.Setup} : BHDRCtlQuery S → SignalPqxdh.SessionId S
  | .startDR sid => sid

@[reducible] def e2eBhAdapterIface (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    Iface (e2eSig ℓ) (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) :=
  e2eAdapterIface S ℓ BHDRCtlQuery.startDR

@[reducible] def e2eBhAdapterCodec (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    GameCodec (e2eSig ℓ) (bhGameSpec S ℓ (BitVec 512)) :=
  e2eAdapterCodec S ℓ bhCtlUnStart

abbrev CliToModelAdapterProgHonest (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) : Type :=
  CostedReduction (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
    (bhGameSpec S ℓ (BitVec 512))
    (e2eBhAdapterCodec S ℓ) .unit .unit .bool .bool

/-- List-backed `ReductionDsl` mirror type `(prins, (bundles, (opks, sends)))` for `ModelDriverBase S`. -/
@[reducible] def drvMirrorTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (.list (.prod (FinT S.N_id) (PB 32)))
    (.prod (.list (.prod (.prod (FinT S.N_id) (FinT S.N_recv)) (.prod (PB 32) (PB 1568))))
      (.prod
        (.list (.prod (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_opk))) (PB 32)))
        (.list (.prod (sidT S) (.prod bundleT hdrT)))))

@[reducible] def cliAdapterStateTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  adapterStateTy (drvMirrorTy S ℓ)

abbrev RefAdapterState (S : SignalPqxdh.Setup) : Type :=
  (ℕ → Option (BHAdapterInstMeta S)) × (ℕ → Bool) × ModelDriverBase S

def refAdapterInitState (S : SignalPqxdh.Setup) : RefAdapterState S :=
  (fun _ => none, (fun _ => false, {}))

def sendEntryToV {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (x : SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr) :
    (Ty.prod (sidT (ℓ := ℓ) S) (.prod bundleT hdrT)).denote :=
  (sidV (ℓ := ℓ) x.1, (bundleV (ℓ := ℓ) x.2.1, hdrV (ℓ := ℓ) x.2.2))

def drvMirrorToV {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : ModelDriverBase S) :
    (drvMirrorTy S ℓ).denote :=
  (d.prins, (d.bundles, (d.opks, d.sends.map (sendEntryToV (ℓ := ℓ)))))

def instMetaToV {S : SignalPqxdh.Setup} {ℓ : ℕ} (inst : BHAdapterInstMeta S) :
    (adapterInstMetaT (ℓ := ℓ)).denote :=
  ((bhInitRegId inst.sid,
    (BitVec.ofNat 32 inst.u_resp.val,
     (inst.bobRemoteRegId, hdrV (ℓ := ℓ) inst.hdr))),
   inst.bobAccepted)

def cliAdapterStateToV {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : RefAdapterState S) :
    (cliAdapterStateTy S ℓ).denote :=
  (fun k => (σ.1 k).map instMetaToV, (σ.2.1, drvMirrorToV σ.2.2))

/-! ## Pure `ReductionDsl` helper expressions -/

section Helpers

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

@[reducible] def cliQuery {Γ : List (Ty (e2eSig ℓ))} (g : E2EAdapterTag)
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ ((e2eBhAdapterIface S ℓ).dom g)) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) Γ
      ((e2eBhAdapterIface S ℓ).cod g) :=
  Comp.query (O := e2eAdapterOps ℓ decT encT) (I := e2eBhAdapterIface S ℓ) g e

def isEmptyBytesExpr {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 32)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .bool :=
  .eqN (adapterPureOp (.bytesLen 32) e) (.nat 0)

theorem eval_isEmptyBytesExpr {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 32)) (ρ : Env Γ) :
    (isEmptyBytesExpr e).eval ρ = (e.eval ρ).isEmpty := by
  unfold isEmptyBytesExpr
  have aux : ∀ xs : Bytes, decide (xs.length = 0) = xs.isEmpty := fun xs => by cases xs <;> rfl
  exact aux (e.eval ρ)

/-- Test whether a byte slice fits within `stdinCapBytes` (`DEV-CLI21`). -/
def capOkBytesExpr {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 32)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .bool :=
  .not (.lt (.nat stdinCapBytes) (adapterPureOp (.bytesLen 32) e))

theorem eval_capOkBytesExpr {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 32)) (ρ : Env Γ) :
    (capOkBytesExpr e).eval ρ = decide ((e.eval ρ).length ≤ stdinCapBytes) := by
  unfold capOkBytesExpr
  have aux : ∀ n : ℕ, (!decide (stdinCapBytes < n)) = decide (n ≤ stdinCapBytes) := fun n => by
    by_cases h : n ≤ stdinCapBytes
    · have hnot : ¬ stdinCapBytes < n := Nat.not_lt.mpr h
      simp [h, hnot]
    · have hlt : stdinCapBytes < n := Nat.lt_of_not_ge h
      simp [h, hlt]
  exact aux (e.eval ρ).length

theorem eval_and_capOkBytesExpr_checkShort_none {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 32)) (ρ : Env Γ) :
    (Expr.and (capOkBytesExpr e)
      (adapterPureOp .checkShortCiphertext (.pair e .none))).eval ρ =
      (decide ((e.eval ρ).length ≤ stdinCapBytes) && shortCiphertext (e.eval ρ)) := by
  change ((capOkBytesExpr e).eval ρ &&
      (adapterPureOp .checkShortCiphertext (.pair e .none)).eval ρ) = _
  rw [eval_capOkBytesExpr, eval_adapterPureOp]
  dsimp only [Expr.eval, E2EPureOp.eval]
  rw [Bool.and_true]

theorem eval_and_capOkBytesExpr_checkShort_some {Γ : List (Ty (e2eSig ℓ))}
    (e inner : Expr (e2eAdapterOps ℓ decT encT) Γ (B 32)) (ρ : Env Γ) :
    (Expr.and (capOkBytesExpr e)
      (adapterPureOp .checkShortCiphertext (.pair e (.some inner)))).eval ρ =
      (decide ((e.eval ρ).length ≤ stdinCapBytes) &&
        shortCiphertext (e.eval ρ) &&
        decide ((inner.eval ρ).length + 2048 < 2 ^ 32)) := by
  change ((capOkBytesExpr e).eval ρ &&
      (adapterPureOp .checkShortCiphertext (.pair e (.some inner))).eval ρ) = _
  rw [eval_capOkBytesExpr, eval_adapterPureOp]
  dsimp only [Expr.eval, E2EPureOp.eval]
  rw [← Bool.and_assoc]

def sidEqExpr {Γ : List (Ty (e2eSig ℓ))}
    (s₁ s₂ : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .bool :=
  .letE (.pair s₁ s₂)
    (.caseSum (.fst .v0)
      (.caseSum (.snd .v1)
        (.and (adapterPureOp (.finEq S.N_id) (.pair (.fst .v1) (.fst .v0)))
              (adapterPureOp (.finEq S.N_send_opk) (.pair (.snd .v1) (.snd .v0))))
        (.bool false))
      (.caseSum .v0
        (.caseSum (.snd .v2)
          (.bool false)
          (.caseSum .v0
            (.and (adapterPureOp (.finEq S.N_id) (.pair (.fst .v2) (.fst .v0)))
                  (adapterPureOp (.finEq S.N_send_no_opk) (.pair (.snd .v2) (.snd .v0))))
            (.bool false)))
        (.caseSum .v0
          (.caseSum (.snd .v3)
            (.bool false)
            (.caseSum .v0
              (.bool false)
              (.caseSum .v0
                (.and (adapterPureOp (.finEq S.N_id) (.pair (.fst .v3) (.fst .v0)))
                  (.and (adapterPureOp (.finEq S.N_recv)
                          (.pair (.fst (.snd .v3)) (.fst (.snd .v0))))
                        (adapterPureOp (.finEq S.N_opk)
                          (.pair (.snd (.snd .v3)) (.snd (.snd .v0))))))
                (.bool false))))
          (.caseSum (.snd .v3)
            (.bool false)
            (.caseSum .v0
              (.bool false)
              (.caseSum .v0
                (.bool false)
                (.and (adapterPureOp (.finEq S.N_id) (.pair (.fst .v3) (.fst .v0)))
                  (.and (adapterPureOp (.finEq S.N_recv)
                          (.pair (.fst (.snd .v3)) (.fst (.snd .v0))))
                        (adapterPureOp (.finEq S.N_no_opk)
                          (.pair (.snd (.snd .v3)) (.snd (.snd .v0))))))))))))

theorem eval_sidEqExpr {Γ : List (Ty (e2eSig ℓ))}
    (s₁ s₂ : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) (ρ : Env Γ) :
    (sidEqExpr s₁ s₂).eval ρ = (sidOfV (ℓ := ℓ) (s₁.eval ρ) == sidOfV (ℓ := ℓ) (s₂.eval ρ)) := by
  rcases h₁ : s₁.eval ρ with ⟨u₁, i₁⟩ | (⟨u₁, i₁⟩ | (⟨k₁, j₁, o₁⟩ | ⟨k₁, j₁, l₁⟩)) <;>
    rcases h₂ : s₂.eval ρ with ⟨u₂, i₂⟩ | (⟨u₂, i₂⟩ | (⟨k₂, j₂, o₂⟩ | ⟨k₂, j₂, l₂⟩)) <;>
    (simp [sidEqExpr, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
      h₁, h₂, eval_adapterPureOp, E2EPureOp.eval, sidOfV, BEq.beq]; try rfl)

def initRegIdExpr {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ U32 :=
  .caseSum s
    (adapterPureOp .u32OfNat (adapterPureOp (.finVal S.N_id) (.fst .v0)))
    (.caseSum .v0
      (adapterPureOp .u32OfNat (adapterPureOp (.finVal S.N_id) (.fst .v0)))
      (adapterPureOp (.u32Lit 0#32) .unit))

theorem eval_initRegIdExpr {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) (ρ : Env Γ) :
    (initRegIdExpr s).eval ρ = bhInitRegId (sidOfV (ℓ := ℓ) (s.eval ρ)) := by
  rcases h : s.eval ρ with ⟨u, i⟩ | (⟨u, i⟩ | (⟨k, j, o⟩ | ⟨k, j, l⟩)) <;>
    simp [initRegIdExpr, Expr.eval, Expr.v0, h, eval_adapterPureOp,
      E2EPureOp.eval, sidOfV, bhInitRegId, CryptoVerification.E2E.bhDrvSessionInitPrin?]

def stepBaseMirrorExpr {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ) :=
  .letE (.pair drv (.pair kq kr))
    (.caseSum (.fst (.snd .v0))
      (.caseSum (.snd (.snd .v1))
        (.fst .v2)
        (.caseSum .v0
          (.pair (.cons (.pair .v2 (.fst .v0)) (.fst (.fst .v3)))
                 (.snd (.fst .v3)))
          (.fst .v3)))
      (.caseSum .v0
        (.fst .v2)
        (.caseSum .v0
          (.caseSum (.snd (.snd .v3))
            (.fst .v4)
            (.caseSum .v0
              (.fst .v5)
              (.caseSum .v0
                (.fst .v6)
                (.caseSum .v0
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTy S ℓ) :=
                       .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                     let spkB := .fst (.snd (.snd .v0))
                     let pqspkB := .fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
                     .pair (.fst dE)
                       (.pair (.cons (.pair .v5 (.pair spkB pqspkB)) (.fst (.snd dE)))
                              (.snd (.snd dE))))
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))
          (.caseSum .v0
            (.caseSum (.snd (.snd .v4))
              (.fst .v5)
              (.caseSum .v0
                (.fst .v6)
                (.caseSum .v0
                  (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTy S ℓ) :=
                     .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
                   .pair (.fst dE)
                     (.pair (.fst (.snd dE))
                       (.pair (.cons (.pair .v3 .v0) (.fst (.snd (.snd dE))))
                              (.snd (.snd (.snd dE))))))
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
            (.caseSum .v0
              (.caseSum (.snd (.snd .v5))
                (.fst .v6)
                (.caseSum .v0
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                    (.caseSum .v0
                      (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
                      (.caseSum .v0
                        (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                        (.caseSum .v0
                          (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTy S ℓ) :=
                             .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                           let uib := .v6
                           let sidE : Expr (e2eAdapterOps ℓ decT encT) _ (sidT S) :=
                             .inl (.pair (.fst uib) (.fst (.snd uib)))
                           let bndE := .snd (.snd uib)
                           .pair (.fst dE)
                             (.pair (.fst (.snd dE))
                               (.pair (.fst (.snd (.snd dE)))
                                 (.cons (.pair sidE (.pair bndE .v0)) (.snd (.snd (.snd dE)))))))
                          (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))))))
              (.caseSum .v0
                (.caseSum (.snd (.snd .v6))
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                    (.caseSum .v0
                      (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
                      (.caseSum .v0
                        (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                        (.caseSum .v0
                          (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
                          (.caseSum .v0
                            (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTy S ℓ) :=
                               .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
                             let uib := .v6
                             let sidE : Expr (e2eAdapterOps ℓ decT encT) _ (sidT S) :=
                               .inr (.inl (.pair (.fst uib) (.fst (.snd uib))))
                             let bndE := .snd (.snd uib)
                             .pair (.fst dE)
                               (.pair (.fst (.snd dE))
                                 (.pair (.fst (.snd (.snd dE)))
                                   (.cons (.pair sidE (.pair bndE .v0)) (.snd (.snd (.snd dE)))))))
                            (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))))))))
                (.fst .v6)))))))

theorem eval_stepBaseMirrorExpr {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT)
    (d : ModelDriverBase S) (ρ : Env Γ)
    (hdrv : drv.eval ρ = drvMirrorToV (ℓ := ℓ) d) :
    (stepBaseMirrorExpr drv kq kr).eval ρ =
      drvMirrorToV (ℓ := ℓ)
        (bhBaseMirror d (keyIndQdec (ℓ := ℓ) (kq.eval ρ)) (keyIndRdec (ℓ := ℓ) (kr.eval ρ))) := by
  unfold stepBaseMirrorExpr
  dsimp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hdrv]
  rcases kq.eval ρ with
      u | (u | (⟨u, j⟩ | (⟨u, j, o⟩ | (⟨u, i, bnd⟩ | (⟨u, i, bnd⟩ | rest)))))
  · rcases kr.eval ρ with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;> rfl
  · rcases kr.eval ρ with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;> rfl
  · rcases kr.eval ρ with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;> rfl
  · rcases kr.eval ρ with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;> rfl
  · rcases kr.eval ρ with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;> rfl
  · rcases kr.eval ρ with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;> rfl
  · rcases rest with _ | (_ | (_ | (_ | (_ | (_ | (_ | _)))))) <;>
      rcases kr.eval ρ with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;>
      rfl

@[local simp] private theorem env_get_zero {S0 : Sig} {Γ0 : List (Ty S0)} {t0 : Ty S0}
    (v : t0.denote) (ρ : Env Γ0) :
    (Env.cons v ρ).get Var.zero = v := rfl

@[local simp] private theorem env_get_succ {S0 : Sig} {Γ0 : List (Ty S0)} {t0 u0 : Ty S0}
    (v : u0.denote) (ρ : Env Γ0) (i : Var Γ0 t0) :
    (Env.cons v ρ).get (Var.succ i) = ρ.get i := rfl

def opkOkPredExpr {Γ : List (Ty (e2eSig ℓ))} :
    Expr (e2eAdapterOps ℓ decT encT)
      (.prod (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_opk))) (PB 32) ::
       .prod PU32 (PB 32) ::
       .prod (.prod (FinT S.N_id) (FinT S.N_recv)) (.prod (PB 32) (PB 1568)) :: Γ) .bool :=
  let u' := .fst (.fst .v0)
  let j' := .fst (.snd (.fst .v0))
  let o := .snd (.snd (.fst .v0))
  let pk := .snd .v0
  let opkId := .fst .v1
  let opkPk := .snd .v1
  let u_resp := .fst (.fst .v2)
  let j_resp := .snd (.fst .v2)
  let oVal := adapterPureOp (.finVal S.N_opk) o
  .and (adapterPureOp (.finEq S.N_id) (.pair u' u_resp))
    (.and (adapterPureOp (.finEq S.N_recv) (.pair j' j_resp))
      (.and (adapterPureOp .pu32Eq (.pair (adapterPureOp .pu32OfNat oVal) opkId))
        (.and (.eqN oVal (adapterPureOp .pu32ToNat opkId))
              (adapterPureOp (.pbytesEq 32 32) (.pair pk opkPk)))))

private theorem eval_opkOkPredExpr {Γ : List (Ty (e2eSig ℓ))}
    (oe : (Ty.prod (.prod (FinT S.N_id) (.prod (FinT S.N_recv) (FinT S.N_opk))) (PB (ℓ := ℓ) 32)).denote)
    (opkPair : (Ty.prod (PU32 (ℓ := ℓ)) (PB 32)).denote)
    (bFound : (Ty.prod (.prod (FinT S.N_id) (FinT S.N_recv)) (.prod (PB (ℓ := ℓ) 32) (PB 1568))).denote)
    (ρ : Env Γ) :
    (opkOkPredExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)).eval
        (Env.cons oe (Env.cons opkPair (Env.cons bFound ρ))) =
      (oe.1.1 == bFound.1.1 && oe.1.2.1 == bFound.1.2 &&
       UInt32.ofNat oe.1.2.2.val == opkPair.1 &&
       oe.1.2.2.val == opkPair.1.toNat && oe.2 == opkPair.2) := by
  rcases oe with ⟨⟨u', j', o⟩, pk⟩
  rcases opkPair with ⟨opkId, opkPk⟩
  rcases bFound with ⟨⟨u_resp, j_resp⟩, _⟩
  simp [opkOkPredExpr, Expr.eval, eval_adapterPureOp, E2EPureOp.eval,
    Expr.v0, Expr.v1, Expr.v2, BEq.beq, Bool.and_assoc]
  rfl

/-- List-backed `startDR` promotion guard expression on `(drv, sid)`. -/
def guardPromoteExpr {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (.opt adapterInstMetaT) :=
  .letE (.pair drv sid)
    (.caseOpt
      (.findB S.N_send_tot (.snd (.snd (.snd (.fst .v0))))
        (sidEqExpr (.fst .v0) (.snd .v1)))
      .none
      (.caseOpt
        (.findB S.N_spk_tot (.fst (.snd (.fst .v1)))
          (let bnd := .fst (.snd .v1)
           let hdr := .snd (.snd .v1)
           let bndSpkB := .fst (.snd (.snd bnd))
           let bndPqspkB := .fst (.snd (.snd (.snd (.snd (.snd (.snd bnd))))))
           let hdrSpkId := .fst (.snd (.snd hdr))
           let hdrPqspkId := .fst (.snd (.snd (.snd (.snd hdr))))
           let jU32 := adapterPureOp .pu32OfNat (adapterPureOp (.finVal S.N_recv) (.snd (.fst .v0)))
           .and (adapterPureOp (.pbytesEq 32 32) (.pair (.fst (.snd .v0)) bndSpkB))
             (.and (adapterPureOp (.pbytesEq 1568 1568) (.pair (.snd (.snd .v0)) bndPqspkB))
               (.and (adapterPureOp .pu32Eq (.pair hdrSpkId jU32))
                     (adapterPureOp .pu32Eq (.pair hdrPqspkId jU32))))))
        .none
        (let prinsOk : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
           .anyB S.N_id (.fst (.fst .v2))
             (.and (adapterPureOp (.finEq S.N_id) (.pair (.fst .v0) (.fst (.fst .v1))))
                   (adapterPureOp (.pbytesEq 32 32)
                     (.pair (.snd .v0) (.fst (.fst (.snd .v2))))))
         let bndOpkOpt := .fst (.snd (.snd (.snd (.snd (.fst (.snd .v1))))))
         let opkOk : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
           .caseOpt bndOpkOpt
             (.bool true)
             (.anyB S.N_opk_tot (.fst (.snd (.snd (.fst .v3)))) opkOkPredExpr)
         .ite (.and prinsOk opkOk)
           (let regIdA := initRegIdExpr (.snd .v2)
            let regIdB := adapterPureOp .u32OfNat
              (adapterPureOp (.finVal S.N_id) (.fst (.fst .v0)))
            let hdr := .snd (.snd .v1)
            .some (.pair (.pair regIdA (.pair regIdB (.pair regIdA hdr))) (.bool false)))
           .none)))

private theorem list_find?_map {α β : Type} (f : α → β) (l : List α) (p : β → Bool) :
    (l.map f).find? p = (l.find? (fun a => p (f a))).map f := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.find?_cons]
    cases p (f a) <;> simp [ih]

theorem eval_guardPromoteExpr {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S))
    (d : ModelDriverBase S) (ρ : Env Γ)
    (hdrv : drv.eval ρ = drvMirrorToV (ℓ := ℓ) d)
    (hPrins : d.prins.length ≤ S.N_id)
    (hBundles : d.bundles.length ≤ S.N_spk_tot)
    (hOpks : d.opks.length ≤ S.N_opk_tot)
    (hSends : d.sends.length ≤ S.N_send_tot) :
    (guardPromoteExpr drv sid).eval ρ =
      ((bhShallowStepMirrorGuard
        (.inr (d, sidOfV (ℓ := ℓ) (sid.eval ρ)))).2).map (instMetaToV (ℓ := ℓ)) := by
  have hSendsMap : (d.sends.map (sendEntryToV (S := S) (ℓ := ℓ))).length ≤ S.N_send_tot := by
    simpa using hSends
  unfold guardPromoteExpr
  change Expr.eval _ (Env.cons (t := .prod (drvMirrorTy S ℓ) (sidT S)) (drv.eval ρ, sid.eval ρ) ρ) = _
  rw [hdrv]
  dsimp only [bhShallowStepMirrorGuard, drvMirrorToV, Expr.eval, env_get_zero, env_get_succ,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3]
  rw [List.take_of_length_le hSendsMap, list_find?_map]
  rw [show List.find? _ d.sends =
        d.sends.find? (fun x => x.1 == sidOfV (ℓ := ℓ) (sid.eval ρ)) by
      apply List.find?_congr
      intro ⟨s, b, h⟩ _
      rw [eval_sidEqExpr]
      dsimp only [sendEntryToV, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1]
      rw [sidOfV_sidV]]
  cases hSend : d.sends.find? (fun x => x.1 == sidOfV (ℓ := ℓ) (sid.eval ρ)) with
  | none => rfl
  | some sbh =>
    rcases sbh with ⟨sFound, bnd, hdr⟩
    simp only [Option.map, sendEntryToV, Expr.eval, eval_adapterPureOp, E2EPureOp.eval,
      bundleV, hdrV, env_get_zero, env_get_succ,
      List.take_of_length_le hBundles]
    have hFindBnd :
        (d.bundles.find? fun be =>
          be.2.1 == bnd.spkB && (be.2.2 == bnd.pqspkB &&
            (hdr.spkId == UInt32.ofNat be.1.2.val &&
              hdr.pqspkId == UInt32.ofNat be.1.2.val))) =
        (d.bundles.find? fun x =>
          x.2.1 == bnd.spkB && x.2.2 == bnd.pqspkB &&
          hdr.spkId == UInt32.ofNat x.1.2.val &&
          hdr.pqspkId == UInt32.ofNat x.1.2.val) := by
      apply List.find?_congr
      intro ⟨⟨u, j⟩, ⟨spkB, pqspkB⟩⟩ _
      simp only [Bool.and_assoc]
    rw [hFindBnd]
    cases hBnd : d.bundles.find? (fun x =>
        x.2.1 == bnd.spkB && x.2.2 == bnd.pqspkB &&
        hdr.spkId == UInt32.ofNat x.1.2.val &&
        hdr.pqspkId == UInt32.ofNat x.1.2.val) with
    | none => rfl
    | some ujSpk =>
      rcases ujSpk with ⟨⟨u_resp, j_resp⟩, spkPair⟩
      unfold bhBaseOpkOk
      cases hopk : bnd.opkB? with
      | none =>
        simp only [List.take_of_length_le hPrins]
        cases hGuard : ((d.prins.any fun x => x.1 == u_resp && x.2 == bnd.ikB) && true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
        · simp only [↓reduceIte, instMetaToV, hdrV]
          rw [eval_initRegIdExpr]
          rfl
      | some opkPair =>
        rcases opkPair with ⟨opkId, opkPk⟩
        simp only [eval_opkOkPredExpr, List.take_of_length_le hPrins, List.take_of_length_le hOpks]
        cases hGuard : ((d.prins.any fun x => x.1 == u_resp && x.2 == bnd.ikB) &&
            (d.opks.any fun x =>
              x.1.1 == u_resp && x.1.2.1 == j_resp &&
                UInt32.ofNat x.1.2.2.val == opkId &&
                x.1.2.2.val == UInt32.toNat opkId && x.2 == opkPk))
        · simp only [Bool.false_eq_true, ↓reduceIte]
        · simp only [↓reduceIte, instMetaToV, hdrV]
          rw [eval_initRegIdExpr]
          rfl

def cliBobUpdateStateExpr {Γ : List (Ty (e2eSig ℓ))}
    (σVar : Var (.opt recvResultT :: Γ) (cliAdapterStateTy S ℓ))
    (instIdxVar : Var (.opt recvResultT :: Γ) .nat)
    (instVar : Var (.opt recvResultT :: Γ) adapterInstMetaT)
    (mRegIdVar : Var (.opt recvResultT :: Γ) U32) :
    Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ) (cliAdapterStateTy S ℓ) :=
  .caseOpt .v0 (.var σVar)
    (.caseSum .v0 (.var (.succ (.succ σVar)))
      (let σE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ σVar))
       let idxE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instIdxVar))
       let instE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instVar))
       let mRegE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ mRegIdVar))
       let regIdA := Expr.fst (.fst instE)
       let regIdB := Expr.fst (.snd (.fst instE))
       let oldBobRem := Expr.fst (.snd (.snd (.fst instE)))
       let instHdr := Expr.snd (.snd (.snd (.fst instE)))
       let bobAcc := Expr.snd instE
       let newBobRem := Expr.ite (.not bobAcc) mRegE oldBobRem
       let newInst := Expr.pair (.pair regIdA (.pair regIdB (.pair newBobRem instHdr))) (.bool true)
       .pair (.tset (.fst σE) idxE (.some newInst)) (.snd σE)))

def cliAliceUpdateStateExpr {Γ : List (Ty (e2eSig ℓ))}
    (σVar : Var (.opt recvResultT :: Γ) (cliAdapterStateTy S ℓ))
    (instIdxVar : Var (.opt recvResultT :: Γ) .nat) :
    Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ) (cliAdapterStateTy S ℓ) :=
  .caseOpt .v0 (.var σVar)
    (.caseSum .v0 (.var (.succ (.succ σVar)))
      (let σE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ σVar))
       let idxE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instIdxVar))
       .pair (.fst σE)
         (.pair (.tset (.fst (.snd σE)) idxE (.bool true))
                (.snd (.snd σE)))))

/-! ## List-backed adapter `cliToModelAdapterProg` -/

def cliAdapterKiOrCtlArm (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.sum (keyIndQT S) (sidT S), cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ)) :=
  .caseSum .v0
    (.bind (cliQuery E2EAdapterTag.ki .v0)
      (.ret (.pair (.inl (.inl .v0))
        (.pair (.fst .v3)
          (.pair (.fst (.snd .v3))
            (stepBaseMirrorExpr (.snd (.snd .v3)) .v1 .v0))))))
    (.bind (cliQuery E2EAdapterTag.ctl .v0)
      (.caseOpt .v0
        (.ret (.pair (.inl (.inr .none)) .v3))
        (.caseOpt (guardPromoteExpr (.snd (.snd .v4)) .v2)
          (.ret (.pair (.inl (.inr (.some .v0))) .v4))
          (.ret (.pair (.inl (.inr (.some .v1)))
            (.pair (.tset (.fst .v5) .v1 (.some .v0)) (.snd .v5)))))))

def cliAdapterTrArm (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (.prod PlainT (.opt BV512)),
       .prod .nat smQT, cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ)) :=
  .caseOpt (.tget (.fst .v2) (.fst .v1))
    (.ret (.pair adapterNoneSmRespExpr .v2))
    (.bind (cliQuery E2EAdapterTag.tr (.pair (.fst .v2) .v1))
      (.caseOpt .v0
        (.ret (.pair adapterNoneSmRespExpr .v4))
        (let regIdA := Expr.fst (.fst .v2)
         let instHdr := Expr.snd (.snd (.snd (.fst .v2)))
         let wire :=
           Expr.ite (.fst .v3)
             (adapterPureOp .wrapWhisperWire .v0)
             (.ite (.tget (.fst (.snd .v5)) (.fst .v4))
               (adapterPureOp .wrapWhisperWire .v0)
               (adapterPureOp .wrapPreKeyWire (.pair regIdA (.pair instHdr .v0))))
         .ret (.pair (.inr (.pair (.some wire) (.pair .none .none))) .v5))))

def cliAdapterChArm (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ)) :=
  .caseOpt (.tget (.fst .v3) (.fst .v2))
    (.ret (.pair adapterNoneSmRespExpr .v3))
    (.bind (cliQuery E2EAdapterTag.ch (.pair (.fst .v3) .v1))
      (.caseOpt .v0
        (.ret (.pair adapterNoneSmRespExpr .v5))
        (let regIdA := Expr.fst (.fst .v2)
         let instHdr := Expr.snd (.snd (.snd (.fst .v2)))
         let wire :=
           Expr.ite (.fst .v3)
             (adapterPureOp .wrapWhisperWire .v0)
             (.ite (.tget (.fst (.snd .v6)) (.fst .v5))
               (adapterPureOp .wrapWhisperWire .v0)
               (adapterPureOp .wrapPreKeyWire (.pair regIdA (.pair instHdr .v0))))
         .ret (.pair (.inr (.pair (.some wire) (.pair .none .none))) .v6))))

def cliAdapterDlArm (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (B 32),
       .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ)) :=
  .ite (.fst .v0)
    (.caseOpt (.tget (.fst .v4) (.fst .v3))
      (.ret (.pair adapterNoneSmRespExpr .v4))
      (.caseOpt (adapterPureOp .parsePreKeyWire (.snd .v1))
        (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v1))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v4) (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
            (.ret (.pair adapterNoneSmRespExpr .v6)))
          (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
            (.ite (isEmptyBytesExpr .v0)
              (.bind (cliQuery E2EAdapterTag.ij
                  (.pair (.fst .v5) (.pair (.bool true) (adapterPureOp .wrapWhisperWire .v0))))
                (.ret (.pair adapterNoneSmRespExpr
                  (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
              (.bind (cliQuery E2EAdapterTag.dl (.pair (.fst .v5) (.pair (.bool true) .v0)))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
            (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) (.pair (.bool true) (.snd .v3))))
              (.ret (.pair adapterNoneSmRespExpr
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))
        (.ite (isEmptyBytesExpr (.snd (.snd .v0)))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v5)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd (.snd .v0))))))
            (.ret (.pair adapterNoneSmRespExpr
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
          (.bind (.ret (.fst .v5))
            (.bind (.ret (.fst .v1))
              (.bind (cliQuery E2EAdapterTag.dl (.pair .v1 .v4))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (cliBobUpdateStateExpr
                    (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                    (.succ (.succ .zero))
                    (.succ (.succ (.succ (.succ .zero))))
                    (.succ .zero))))))))))
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.ite (isEmptyBytesExpr (.snd .v0))
        (.bind (cliQuery E2EAdapterTag.dl (.pair (.fst .v3) .v0))
          (.ret (.pair (.inr (.pair .none (.pair .v0 .none))) .v5)))
        (.ret (.pair adapterNoneSmRespExpr .v4)))
      (.ite (isEmptyBytesExpr .v0)
        (.ret (.pair adapterNoneSmRespExpr .v5))
        (.bind (.ret (.fst .v4))
          (.bind (cliQuery E2EAdapterTag.dl (.pair .v0 (.pair (.bool false) .v1)))
            (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
              (cliAliceUpdateStateExpr
                (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
                (.succ .zero))))))))

def cliAdapterIjArm (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (B 32),
       .sum (.prod .bool (B 32)) .bool,
       .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ)) :=
  .ite (.fst .v0)
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.caseOpt (adapterPureOp .parsePreKeyWire (.snd .v0))
        (.bind (cliQuery E2EAdapterTag.ij
            (.pair (.fst .v4) (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v0)))))
          (.ret (.pair adapterNoneSmRespExpr .v6)))
        (.ite (.and (capOkBytesExpr (.snd .v1))
            (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) (.some (.snd (.snd .v0))))))
          (.caseOpt (.tget (.fst .v6) (.fst .v5))
            (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v5) .v1))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (let bobAcc := Expr.snd .v0
             let regIdA := Expr.fst (.fst .v0)
             let instHdr := Expr.snd (.snd (.snd (.fst .v0)))
             let eqHdrExpr : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
               .caseOpt (adapterPureOp .partneredInnerBytes
                   (.pair bobAcc (.pair regIdA (.pair instHdr (.snd .v2)))))
                 (.bool false) (.bool true)
             .ite (isEmptyBytesExpr (.snd (.snd .v1)))
               (.ite eqHdrExpr
                 (.bind (cliQuery E2EAdapterTag.ij
                     (.pair (.fst .v6)
                       (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v2)))))
                   (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                     (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                 (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) .v2))
                   (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                     (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
               (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) .v2))
                 (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                   (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v5)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
            (.ret (.pair adapterNoneSmRespExpr
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
      (.ite (.and (capOkBytesExpr (.snd .v1))
          (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) .none)))
        (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
          (.ite (isEmptyBytesExpr .v0)
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5)
                  (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5) (.pair (.bool true) .v0)))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v6)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire .v1))))
            (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
        (.bind (cliQuery E2EAdapterTag.ij
            (.pair (.fst .v5)
              (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
          (.ret (.pair adapterNoneSmRespExpr
            (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.ret (.pair adapterNoneSmRespExpr .v5))
      (.ite (.and (capOkBytesExpr (.snd .v1))
          (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) .none)))
        (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
          (.ite (isEmptyBytesExpr .v0)
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5)
                  (.pair (.bool false) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (.bind (.ret (.fst .v5))
              (.bind (cliQuery E2EAdapterTag.ij (.pair .v0 (.pair (.bool false) .v1)))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (cliAliceUpdateStateExpr
                    (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
                    (.succ .zero)))))))
          (.bind (.ret (.fst .v6))
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair .v0 (.pair (.bool false) (adapterPureOp .wrapWhisperWire .v2))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (cliAliceUpdateStateExpr
                  (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.succ .zero)))))))
        (.ret (.pair adapterNoneSmRespExpr .v6))))

def cliAdapterHandle {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ)) :=
  .caseSum (.var (.succ .zero))
    (cliAdapterKiOrCtlArm S ℓ decT encT)
    (.caseSum (.snd .v0)
      (cliAdapterTrArm S ℓ decT encT)
      (.caseSum .v0
        (cliAdapterChArm S ℓ decT encT)
        (.caseSum .v0
          (cliAdapterDlArm S ℓ decT encT)
          (.caseSum .v0
            (cliAdapterIjArm S ℓ decT encT)
            (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
              (drvMirrorTy S ℓ))))))

/-- List-backed `ReductionDsl.CostedReduction` adapter `cliToModelAdapterProg`. -/
def cliToModelAdapterProg {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProgHonest S ℓ decT encT where
  σ := cliAdapterStateTy S ℓ
  init :=
    .ret (.pair
      .unit
      (.pair (.tconst .none)
        (.pair (.tconst (.bool false))
          (.pair .nil (.pair .nil (.pair .nil .nil))))))
  handle := cliAdapterHandle decT encT S ℓ
  finish := .ret (.var (.succ .zero))

end Helpers

/-! ## Cost, size, and query bounds -/

section CostAndQueryBounds
attribute [local simp] env_get_zero env_get_succ

variable {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
  (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)

theorem init_cost_cliToModelAdapterProg :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).init.cost ≤ 24 := by
  dsimp [cliToModelAdapterProg, Comp.cost, Expr.cost]
  omega

theorem finish_cost_cliToModelAdapterProg :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).finish.cost ≤ 4 := by
  dsimp [cliToModelAdapterProg, Comp.cost, Expr.cost]
  omega

private theorem sidEqExpr_cost_le {Γ : List (Ty (e2eSig ℓ))}
    (s₁ s₂ : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (sidEqExpr s₁ s₂).cost ≤ s₁.cost + s₂.cost + 48 := by
  dsimp [sidEqExpr, Expr.cost, cost_adapterPureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3]
  omega

private theorem initRegIdExpr_cost_le {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (initRegIdExpr s).cost ≤ s.cost + 16 := by
  dsimp [initRegIdExpr, Expr.cost, cost_adapterPureOp, E2EPureOp.cost, Expr.v0]
  omega

private theorem stepBaseMirrorExpr_cost_le {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    (stepBaseMirrorExpr drv kq kr).cost ≤ drv.cost + kq.cost + kr.cost + 256 := by
  dsimp [stepBaseMirrorExpr, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, Expr.v6]
  omega

private theorem guardPromoteExpr_cost_le {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (guardPromoteExpr drv sid).cost ≤
      drv.cost + sid.cost + 64 * S.N_send_tot + 3300 * S.N_spk_tot +
        96 * S.N_id + 160 * S.N_opk_tot + 128 := by
  have hSid := sidEqExpr_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := .prod (sidT S) (.prod bundleT hdrT) :: .prod (drvMirrorTy S ℓ) (sidT S) :: Γ)
    (.fst .v0) (.snd .v1)
  have hReg := initRegIdExpr_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := .prod (.prod (FinT S.N_id) (FinT S.N_recv)) (.prod (PB 32) (PB 1568)) ::
      .prod (sidT S) (.prod bundleT hdrT) :: .prod (drvMirrorTy S ℓ) (sidT S) :: Γ)
    (.snd .v2)
  dsimp [guardPromoteExpr, opkOkPredExpr, Expr.cost, cost_adapterPureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hSid hReg ⊢
  have hSendMul := Nat.mul_le_mul_left S.N_send_tot
    (show (sidEqExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
      (Γ := .prod (sidT S) (.prod bundleT hdrT) :: .prod (drvMirrorTy S ℓ) (sidT S) :: Γ)
      (Expr.var Var.zero).fst (Expr.var (Var.succ Var.zero)).snd).cost + 1 ≤ 64 by omega)
  rw [Nat.mul_comm S.N_send_tot 64] at hSendMul
  omega

private theorem cliAdapterKiOrCtlArm_cost_le :
    (cliAdapterKiOrCtlArm S ℓ decT encT).cost ≤
      1000 + 64 * S.N_send_tot + 3300 * S.N_spk_tot + 96 * S.N_id + 160 * S.N_opk_tot := by
  have hMir := stepBaseMirrorExpr_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
           cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v3)) .v1 .v0
  have hGrd := guardPromoteExpr_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
           cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v4)) .v2
  dsimp only [cliAdapterKiOrCtlArm, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hMir hGrd ⊢
  omega

private theorem cliAdapterTrArm_cost_le :
    (cliAdapterTrArm S ℓ decT encT).cost ≤ 512 + 4 * (ℓ / 32) := by
  dsimp only [cliAdapterTrArm, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.cost, Expr.cost, cost_adapterPureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
  omega

private theorem cliAdapterChArm_cost_le :
    (cliAdapterChArm S ℓ decT encT).cost ≤ 512 + 5 * (ℓ / 32) := by
  dsimp only [cliAdapterChArm, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.cost, Expr.cost, cost_adapterPureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  omega

private theorem cliAdapterDlArm_cost_le :
    (cliAdapterDlArm S ℓ decT encT).cost ≤ 1024 + 4 * (ℓ / 32) := by
  have hB32 : bits (32 : ℕ+) = 6 := by decide
  have hB0 : bits 0 = 1 := by decide
  dsimp only [cliAdapterDlArm, cliBobUpdateStateExpr, cliAliceUpdateStateExpr, isEmptyBytesExpr,
    cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr, Comp.cost, Expr.cost,
    cost_adapterPureOp, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, Expr.v6]
  rw [hB32, hB0]
  omega

private theorem cliAdapterIjArm_cost_le :
    (cliAdapterIjArm S ℓ decT encT).cost ≤ 1024 + 4 * (ℓ / 32) := by
  have hB32 : bits (32 : ℕ+) = 6 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hBCap : bits stdinCapBytes = 21 := by decide
  dsimp only [cliAdapterIjArm, cliAliceUpdateStateExpr, isEmptyBytesExpr, capOkBytesExpr,
    cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr, Comp.cost, Expr.cost,
    cost_adapterPureOp, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, Expr.v6]
  rw [hB32, hB0, hBCap]
  omega

theorem handle_only_cost_cliToModelAdapterProg_le :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).handle.cost ≤
      57000 + 8 * (ℓ / 32) + 64 * S.N_send_tot + 3300 * S.N_spk_tot +
        96 * S.N_id + 160 * S.N_opk_tot := by
  have h1 := cliAdapterKiOrCtlArm_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h2 := cliAdapterTrArm_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h3 := cliAdapterChArm_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h4 := cliAdapterDlArm_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h5 := cliAdapterIjArm_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h6 := adapterCrArm_cost S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
    (drvMirrorTy S ℓ)
  dsimp only [cliToModelAdapterProg, cliAdapterHandle, Comp.cost, Expr.cost, Expr.v0]
  omega

theorem handle_cost_cliToModelAdapterProg_of_codecCost_le
    {c : ℕ} (hc : c ≤ 64) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).handle.cost + c ≤
      58000 + 8 * (ℓ / 32) + 64 * S.N_send_tot + 3300 * S.N_spk_tot +
        96 * S.N_id + 160 * S.N_opk_tot := by
  have h := handle_only_cost_cliToModelAdapterProg_le (S := S) (ℓ := ℓ) decT encT
  omega

theorem handle_cost_cliToModelAdapterProg_le :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).handle.cost +
        (e2eBhAdapterCodec S ℓ).codecCost ≤
      58000 + 8 * (ℓ / 32) + 64 * S.N_send_tot + 3300 * S.N_spk_tot +
        96 * S.N_id + 160 * S.N_opk_tot :=
  handle_cost_cliToModelAdapterProg_of_codecCost_le decT encT
    (by dsimp [e2eBhAdapterCodec, e2eAdapterCodec]; omega)

theorem totalCost_cliToModelAdapterProg_le_preBlock
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalCost (b.q_total + qStart + qDR) ≤
      e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ := by
  apply totalCost_le_e2eAdapterCostBudgetPreBlock_of_step
  · have hI := init_cost_cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT
    have hF := finish_cost_cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT
    unfold adapterPerStepBudgetPreBlock
    omega
  · dsimp [e2eBhAdapterIface, e2eAdapterIface, adapterPerStepBudgetPreBlock]
    omega
  · have hH := handle_cost_cliToModelAdapterProg_le (S := S) (ℓ := ℓ) decT encT
    unfold adapterPerStepBudgetPreBlock
    omega

theorem totalCost_cliToModelAdapterProg_le_uniform12
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalCost (b.q_total + qStart + qDR) ≤
      e2eAdapterCostBudgetUniform12 S b qStart qDR ℓ :=
  Nat.le_trans (totalCost_cliToModelAdapterProg_le_preBlock decT encT b qStart qDR)
    (e2eAdapterCostBudgetPreBlock_le_uniform12 S b qStart qDR ℓ)

theorem totalCost_cliToModelAdapterProg_le_m0
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalCost (b.q_total + qStart + qDR) ≤
      m0AdapterCostBudget S b qStart qDR ℓ :=
  Nat.le_trans (totalCost_cliToModelAdapterProg_le_uniform12 decT encT b qStart qDR)
    (e2eAdapterCostBudgetUniform12_le_m0AdapterCostBudget S b qStart qDR ℓ)

theorem totalCost_cliToModelAdapterProg_le
    (hOpk : 32 ≤ S.N_opk) (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalCost (b.q_total + qStart + qDR) ≤
      e2eAdapterCostBudget S b qStart qDR ℓ := by
  apply totalCost_le_e2eAdapterCostBudget_of_step
  · have hI := init_cost_cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT
    have hF := finish_cost_cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT
    unfold adapterPerStepBudget
    omega
  · dsimp [e2eBhAdapterIface, e2eAdapterIface, adapterPerStepBudget]
    omega
  · have hH := handle_cost_cliToModelAdapterProg_le (S := S) (ℓ := ℓ) decT encT
    have hSpkOpk : 32 * S.N_spk_tot ≤ S.N_opk_tot := by
      dsimp [SignalPqxdh.Setup.N_opk_tot, SignalPqxdh.Setup.N_spk_tot]
      calc 32 * (S.N_id * S.N_recv) = (S.N_id * S.N_recv) * 32 := Nat.mul_comm _ _
        _ ≤ (S.N_id * S.N_recv) * S.N_opk := Nat.mul_le_mul_left _ hOpk
    unfold adapterPerStepBudget
    omega

theorem totalQueries_cliToModelAdapterProg_eq (q : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalQueries
      (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, cliToModelAdapterProg, cliAdapterHandle,
    cliAdapterKiOrCtlArm, cliAdapterTrArm, cliAdapterChArm, cliAdapterDlArm, cliAdapterIjArm,
    adapterCrArm, cliQuery, Comp.queries]

theorem totalQueries_cliToModelAdapterProg_le (q : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q :=
  (totalQueries_cliToModelAdapterProg_eq (S := S) (ℓ := ℓ) decT encT q).le

theorem init_size_cliToModelAdapterProg :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).init.size ≤ 32 := by
  dsimp [cliToModelAdapterProg, Comp.size, Expr.size]
  omega

theorem finish_size_cliToModelAdapterProg :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).finish.size ≤ 8 := by
  dsimp [cliToModelAdapterProg, Comp.size, Expr.size]
  omega

private theorem sidEqExpr_size_le {Γ : List (Ty (e2eSig ℓ))}
    (s₁ s₂ : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (sidEqExpr s₁ s₂).size ≤ 4 * s₁.size + 4 * s₂.size + 128 := by
  dsimp [sidEqExpr, Expr.size, Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp,
    E2EPureOp.opSize, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
  omega

private theorem initRegIdExpr_size_le {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (initRegIdExpr s).size ≤ 2 * s.size + 32 := by
  dsimp [initRegIdExpr, Expr.size, Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp,
    E2EPureOp.opSize, Expr.v0]
  omega

private theorem stepBaseMirrorExpr_size_le {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    (stepBaseMirrorExpr drv kq kr).size ≤
      32 * drv.size + 32 * kq.size + 32 * kr.size + 1024 := by
  dsimp [stepBaseMirrorExpr, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, Expr.v6]
  omega

private theorem guardPromoteExpr_size_le {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (guardPromoteExpr drv sid).size ≤
      8 * drv.size + 8 * sid.size + 4 * bits S.N_send_tot + 4 * bits S.N_spk_tot +
        4 * bits S.N_id + 4 * bits S.N_opk_tot + 640 := by
  have hSid := sidEqExpr_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := .prod (sidT S) (.prod bundleT hdrT) :: .prod (drvMirrorTy S ℓ) (sidT S) :: Γ)
    (.fst .v0) (.snd .v1)
  have hReg := initRegIdExpr_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := .prod (.prod (FinT S.N_id) (FinT S.N_recv)) (.prod (PB 32) (PB 1568)) ::
      .prod (sidT S) (.prod bundleT hdrT) :: .prod (drvMirrorTy S ℓ) (sidT S) :: Γ)
    (.snd .v2)
  dsimp [guardPromoteExpr, opkOkPredExpr, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hSid hReg ⊢
  omega

private theorem cliAdapterKiOrCtlArm_size_le :
    (cliAdapterKiOrCtlArm S ℓ decT encT).size ≤
      2560 + 4 * bits S.N_send_tot + 4 * bits S.N_spk_tot +
        4 * bits S.N_id + 4 * bits S.N_opk_tot := by
  have hMir := stepBaseMirrorExpr_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
           cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v3)) .v1 .v0
  have hGrd := guardPromoteExpr_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
           cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v4)) .v2
  dsimp only [cliAdapterKiOrCtlArm, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hMir hGrd ⊢
  omega

private theorem cliAdapterTrArm_size_le :
    (cliAdapterTrArm S ℓ decT encT).size ≤ 256 := by
  dsimp only [cliAdapterTrArm, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
  omega

private theorem cliAdapterChArm_size_le :
    (cliAdapterChArm S ℓ decT encT).size ≤ 256 := by
  dsimp only [cliAdapterChArm, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  omega

private theorem cliAdapterDlArm_size_le :
    (cliAdapterDlArm S ℓ decT encT).size ≤ 1024 := by
  have hB0 : bits 0 = 1 := by decide
  dsimp only [cliAdapterDlArm, cliBobUpdateStateExpr, cliAliceUpdateStateExpr, isEmptyBytesExpr,
    cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hB0]
  omega

private theorem cliAdapterIjArm_size_le :
    (cliAdapterIjArm S ℓ decT encT).size ≤ 1536 := by
  have hB0 : bits 0 = 1 := by decide
  have hBCap : bits stdinCapBytes = 21 := by decide
  dsimp only [cliAdapterIjArm, cliAliceUpdateStateExpr, isEmptyBytesExpr, capOkBytesExpr,
    cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hB0, hBCap]
  omega

theorem size_cliToModelAdapterProg_le_params :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).size ≤
      8192 + 16 * bits (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) := by
  have hI := init_size_cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT
  have hF := finish_size_cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT
  have h1 := cliAdapterKiOrCtlArm_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h2 := cliAdapterTrArm_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h3 := cliAdapterChArm_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h4 := cliAdapterDlArm_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h5 := cliAdapterIjArm_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
  have h6 := Computational.Proofs.E2E.Dsl.TablesHonest.adapterCrArm_size S ℓ
    BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT (drvMirrorTy S ℓ)
  have hb1 : bits S.N_send_tot ≤ bits (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) :=
    Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono (by omega)
  have hb2 : bits S.N_spk_tot ≤ bits (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) :=
    Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono (by omega)
  have hb3 : bits S.N_id ≤ bits (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) :=
    Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono (by omega)
  have hb4 : bits S.N_opk_tot ≤ bits (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) :=
    Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono (by omega)
  dsimp only [CostedReduction.size, cliToModelAdapterProg, cliAdapterHandle, Comp.size, Expr.size,
    Expr.v0] at hI hF ⊢
  omega

theorem size_cliToModelAdapterProg_le_of_setup_le {B : ℕ}
    (hSetup : S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot ≤ B) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget + 2 ^ 12 * bits B :=
  Computational.Proofs.ReductionDsl.SizeBudgetBridge.size_le_budget_of_log_cost_mono
    (by decide) (by decide) hSetup
    (size_cliToModelAdapterProg_le_params (S := S) (ℓ := ℓ) decT encT)

theorem size_cliToModelAdapterProg_le_preBlock
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * bits (e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ) := by
  apply size_cliToModelAdapterProg_le_of_setup_le
  unfold e2eAdapterCostBudgetPreBlock
  calc S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot
      = 1 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) := (Nat.one_mul _).symm
    _ ≤ (2 ^ 8 * (b.q_total + qStart + qDR + 1)) *
          (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) :=
        Nat.mul_le_mul (by omega) (by omega)

theorem size_cliToModelAdapterProg_le_uniform12
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * bits (e2eAdapterCostBudgetUniform12 S b qStart qDR ℓ) := by
  apply size_cliToModelAdapterProg_le_of_setup_le
  refine Nat.le_trans ?_ (e2eAdapterCostBudgetPreBlock_le_uniform12 S b qStart qDR ℓ)
  unfold e2eAdapterCostBudgetPreBlock
  calc S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot
      = 1 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) := (Nat.one_mul _).symm
    _ ≤ (2 ^ 8 * (b.q_total + qStart + qDR + 1)) *
          (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) :=
        Nat.mul_le_mul (by omega) (by omega)

theorem size_cliToModelAdapterProg_le_m0
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * bits (m0AdapterCostBudget S b qStart qDR ℓ) := by
  apply size_cliToModelAdapterProg_le_of_setup_le
  refine Nat.le_trans ?_
    (Nat.le_trans (e2eAdapterCostBudgetPreBlock_le_uniform12 S b qStart qDR ℓ)
      (e2eAdapterCostBudgetUniform12_le_m0AdapterCostBudget S b qStart qDR ℓ))
  unfold e2eAdapterCostBudgetPreBlock
  calc S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot
      = 1 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) := (Nat.one_mul _).symm
    _ ≤ (2 ^ 8 * (b.q_total + qStart + qDR + 1)) *
          (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) :=
        Nat.mul_le_mul (by omega) (by omega)

theorem size_cliToModelAdapterProg_le
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * bits (e2eAdapterCostBudget S b qStart qDR ℓ) := by
  apply size_cliToModelAdapterProg_le_of_setup_le
  unfold e2eAdapterCostBudget
  calc S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot
      = 1 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) := (Nat.one_mul _).symm
    _ ≤ (2 ^ 8 * (b.q_total + qStart + qDR + 1)) *
          (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) :=
        Nat.mul_le_mul (by omega) (by omega)

theorem gRedBounded_cliToModelAdapterProg_of_le
    {q B : ℕ}
    (hCost : (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalCost q ≤ B)
    (hSize : (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget + 2 ^ 12 * bits B) :
    GRedBounded (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) q q B :=
  gRedBounded_of_bounds (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT)
    (fun _ => 1) (fun _ => 0) q q B hCost hSize
    (by rw [totalQueries_cliToModelAdapterProg_eq])
    (e2eAdapterOps_sizeHonest ℓ decT encT)
    (e2eSamplers_sizeHonest ℓ)

theorem gRedBounded_cliToModelAdapterProg_preBlock
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    GRedBounded (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
      (e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ) :=
  gRedBounded_cliToModelAdapterProg_of_le decT encT
    (totalCost_cliToModelAdapterProg_le_preBlock decT encT b qStart qDR)
    (size_cliToModelAdapterProg_le_preBlock decT encT b qStart qDR)

theorem gRedBounded_cliToModelAdapterProg_uniform12
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    GRedBounded (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
      (e2eAdapterCostBudgetUniform12 S b qStart qDR ℓ) :=
  gRedBounded_cliToModelAdapterProg_of_le decT encT
    (totalCost_cliToModelAdapterProg_le_uniform12 decT encT b qStart qDR)
    (size_cliToModelAdapterProg_le_uniform12 decT encT b qStart qDR)

theorem gRedBounded_cliToModelAdapterProg_m0
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    GRedBounded (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
      (m0AdapterCostBudget S b qStart qDR ℓ) :=
  gRedBounded_cliToModelAdapterProg_of_le decT encT
    (totalCost_cliToModelAdapterProg_le_m0 decT encT b qStart qDR)
    (size_cliToModelAdapterProg_le_m0 decT encT b qStart qDR)

/-- `GRedBounded` bound for `cliToModelAdapterProg` in `e2eAdapterCostBudget` when `32 ≤ S.N_opk`. -/
theorem gRedBounded_cliToModelAdapterProg
    (hOpk : 32 ≤ S.N_opk) (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    GRedBounded (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
      (e2eAdapterCostBudget S b qStart qDR ℓ) :=
  gRedBounded_cliToModelAdapterProg_of_le decT encT
    (totalCost_cliToModelAdapterProg_le decT encT hOpk b qStart qDR)
    (size_cliToModelAdapterProg_le decT encT b qStart qDR)

section CompQueryHelpers

variable {Sig0 : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops Sig0} {I : Iface Sig0 T}
variable (P : ι → Prop) [DecidablePred P]

private theorem qb0_ret {Γ : List (Ty Sig0)} {t : Ty Sig0}
    {e : Expr O Γ t} {ρ : Env Γ} :
    ((Comp.ret e : Comp O I Γ t).eval ρ).IsQueryBoundP P 0 :=
  isQueryBoundP_pure P (e.eval ρ) 0

private theorem qb0_ite {Γ : List (Ty Sig0)} {t : Ty Sig0}
    {b : Expr O Γ .bool} {c d : Comp O I Γ t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P 0) (hd : (d.eval ρ).IsQueryBoundP P 0) :
    ((Comp.ite b c d).eval ρ).IsQueryBoundP P 0 := by
  simp only [Comp.eval]; split_ifs; exact hc; exact hd

private theorem qb0_caseOpt {Γ : List (Ty Sig0)} {a t : Ty Sig0}
    {e : Expr O Γ (.opt a)} {n : Comp O I Γ t} {s : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hn : (n.eval ρ).IsQueryBoundP P 0)
    (hs : ∀ x, (s.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.caseOpt e n s).eval ρ).IsQueryBoundP P 0 := by
  simp only [Comp.eval]; cases e.eval ρ with | none => exact hn | some x => exact hs x

private theorem qb0_caseSum {Γ : List (Ty Sig0)} {a b t : Ty Sig0}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t} {ρ : Env Γ}
    (hl : ∀ x, (l.eval (.cons x ρ)).IsQueryBoundP P 0)
    (hr : ∀ y, (r.eval (.cons y ρ)).IsQueryBoundP P 0) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P 0 := by
  simp only [Comp.eval]; cases e.eval ρ with | inl x => exact hl x | inr y => exact hr y

private theorem qb0_caseSum_inl {Γ : List (Ty Sig0)} {a b t : Ty Sig0}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {x : a.denote} (he : e.eval ρ = .inl x)
    (hl : (l.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P 0 := by
  simp only [Comp.eval, he]; exact hl

private theorem qb0_caseSum_inr {Γ : List (Ty Sig0)} {a b t : Ty Sig0}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) t} {r : Comp O I (b :: Γ) t}
    {ρ : Env Γ} {y : b.denote} (he : e.eval ρ = .inr y)
    (hr : (r.eval (.cons y ρ)).IsQueryBoundP P 0) :
    ((Comp.caseSum e l r).eval ρ).IsQueryBoundP P 0 := by
  simp only [Comp.eval, he]; exact hr

private theorem qb0_bind_ret {Γ : List (Ty Sig0)} {a t : Ty Sig0}
    {e : Expr O Γ a} {k : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hk : (k.eval (.cons (e.eval ρ) ρ)).IsQueryBoundP P 0) :
    ((Comp.bind (.ret e) k).eval ρ).IsQueryBoundP P 0 := by
  simpa [Comp.eval] using hk

private theorem qb0_bind {Γ : List (Ty Sig0)} {a t : Ty Sig0}
    {c : Comp O I Γ a} {k : Comp O I (a :: Γ) t} {ρ : Env Γ}
    (hc : (c.eval ρ).IsQueryBoundP P 0)
    (hk : ∀ x, (k.eval (.cons x ρ)).IsQueryBoundP P 0) :
    ((Comp.bind c k).eval ρ).IsQueryBoundP P 0 := by
  simpa [Comp.eval] using isQueryBoundP_bind hc (fun x _ => hk x)

private theorem qb0_query {Γ : List (Ty Sig0)}
    {g : I.Tag} {e : Expr O Γ (I.dom g)} {ρ : Env Γ}
    (hg : ¬ P (I.enc g (e.eval ρ))) :
    ((Comp.query g e : Comp O I Γ (I.cod g)).eval ρ).IsQueryBoundP P 0 := by
  simp only [Comp.eval, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  exact fun h => False.elim (hg h)

end CompQueryHelpers

private theorem isQueryBoundP_e2eBhAdapterIface_fwdU
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (pCtl : BHDRCtlQuery S → Bool)
    (pInst : ℕ → Bool) (n : ℕ) :
    ((e2eBhAdapterIface S ℓ).fwdU n).IsQueryBoundP
      (fun q => bhClassifyTarget pKi pCtl pInst q = true) 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
    (fun q => bhClassifyTarget pKi pCtl pInst q = true) (Sum.inl n) 0).2
    (by simp [bhClassifyTarget])

private theorem cliAdapterHandle_queries :
    (cliAdapterHandle decT encT S ℓ).queries (fun _ => 1) (fun _ => 0) = 1 := by
  have h1 : (cliAdapterKiOrCtlArm S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterKiOrCtlArm, cliQuery, Comp.queries]
  have h2 : (cliAdapterTrArm S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterTrArm, cliQuery, Comp.queries]
  have h3 : (cliAdapterChArm S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterChArm, cliQuery, Comp.queries]
  have h4 : (cliAdapterDlArm S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterDlArm, cliQuery, Comp.queries]
  have h5 : (cliAdapterIjArm S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterIjArm, cliQuery, Comp.queries]
  have h6 : (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
      (drvMirrorTy S ℓ)).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [adapterCrArm, Comp.queries]
  simp [cliAdapterHandle, Comp.queries, h1, h2, h3, h4, h5, h6]

set_option linter.unusedSimpArgs false in
private theorem isQueryBoundP_cliAdapterHandle_eval_ij_cr
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool)
    (s : (cliAdapterStateTy S ℓ).denote) (i : ℕ)
    (sq_ij_cr : (Party × Bytes) ⊕ Party)
    (hpFalse : pInst i = false) :
    ((cliAdapterHandle decT encT S ℓ).eval
      (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc
        (.inr ⟨i, match sq_ij_cr with
          | .inl pc => .inl (.inr pc)
          | .inr p => .inr p⟩)) .nil))).IsQueryBoundP
      (fun q => bhClassifyTarget pKi pCtl pInst q = true) 0 := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi pCtl pInst q = true
  rcases sq_ij_cr with ⟨p, c⟩ | p
  ·
    unfold cliAdapterHandle
    refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
      (qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
        (qb0_caseSum_inl P_tgt rfl ?_))))
    unfold cliAdapterIjArm cliQuery
    cases p <;>
    · repeat' first
        | with_reducible exact qb0_ret P_tgt
        | with_reducible apply qb0_ite P_tgt
        | (with_reducible apply qb0_caseOpt P_tgt) <;> try intro _
        | with_reducible apply qb0_bind_ret P_tgt
        | refine qb0_bind P_tgt
            (qb0_query P_tgt (by
              simp only [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget,
                bhClassifyTargetOnly, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
                Expr.v3, Expr.v4, Expr.v5, Expr.v6, Env.get, hpFalse, Bool.false_eq_true,
                not_false_eq_true]))
            (fun _ => ?_)
  ·
    unfold cliAdapterHandle
    refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
      (qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
        (qb0_caseSum_inr P_tgt rfl ?_))))
    unfold adapterCrArm
    refine qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => ?_)
    refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ =>
      qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => qb0_ret P_tgt))
    simp only [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget,
      bhClassifyTargetOnly, Expr.eval, Expr.v0, Expr.v1, Expr.v5, Env.get, hpFalse,
      Bool.false_eq_true, not_false_eq_true]

set_option linter.unusedSimpArgs false in
private theorem isQueryBoundP_cliAdapterHandle_eval
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool)
    (s : (cliAdapterStateTy S ℓ).denote) (t : (bhGameSpec S ℓ (BitVec 512)).Domain) :
    ((cliAdapterHandle decT encT S ℓ).eval
      (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
      (fun q => bhClassifyTarget pKi pCtl pInst q = true)
      (if bhClassifyGameOnly pKi pCtl pInst t then 1 else 0) := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi pCtl pInst q = true
  by_cases hp : bhClassifyGameOnly pKi pCtl pInst t = true
  · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hp))]
    rw [← cliAdapterHandle_queries (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)]
    exact Comp.queryBound_eval P_tgt (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl)
      (isQueryBoundP_e2eBhAdapterIface_fwdU pKi pCtl pInst)
      (cliAdapterHandle decT encT S ℓ)
      (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc t) .nil))
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hp h))]
    have hpFalse : bhClassifyGameOnly pKi pCtl pInst t = false :=
      Bool.eq_false_iff.mpr hp
    · rcases t with (kq | cq) | ⟨i, sq⟩
      · simp only [bhClassifyGameOnly] at hpFalse
        unfold cliAdapterHandle
        refine qb0_caseSum_inl P_tgt rfl ?_
        unfold cliAdapterKiOrCtlArm cliQuery
        refine qb0_caseSum_inl P_tgt rfl ?_
        refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ => qb0_ret P_tgt)
        simp [P_tgt, e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec,
          bhClassifyTarget, bhClassifyTargetOnly, Expr.eval, Expr.v0, Env.get, hpFalse]
      · rcases cq with ⟨sid⟩
        simp only [bhClassifyGameOnly] at hpFalse
        unfold cliAdapterHandle
        refine qb0_caseSum_inl P_tgt rfl ?_
        unfold cliAdapterKiOrCtlArm cliQuery
        refine qb0_caseSum_inr P_tgt rfl ?_
        refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ => ?_)
        · simp [P_tgt, e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec,
            bhCtlUnStart, bhClassifyTarget, bhClassifyTargetOnly, Expr.eval, Expr.v0, Env.get, hpFalse]
        · exact qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ =>
            qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => qb0_ret P_tgt))
      · simp only [bhClassifyGameOnly] at hpFalse
        rcases sq with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
        ·
          unfold cliAdapterHandle
          refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inl P_tgt rfl ?_)
          unfold cliAdapterTrArm cliQuery
          refine qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => ?_)
          refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ =>
            qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => qb0_ret P_tgt))
          simp [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget, bhClassifyTargetOnly,
            Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, hpFalse]
        ·
          unfold cliAdapterHandle
          refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
            (qb0_caseSum_inl P_tgt rfl ?_))
          unfold cliAdapterChArm cliQuery
          refine qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => ?_)
          refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ =>
            qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => qb0_ret P_tgt))
          simp [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget, bhClassifyTargetOnly,
            Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get, hpFalse]
        ·
          unfold cliAdapterHandle
          refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
            (qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inl P_tgt rfl ?_)))
          unfold cliAdapterDlArm cliQuery
          cases p <;>
          · repeat' first
              | with_reducible exact qb0_ret P_tgt
              | with_reducible apply qb0_ite P_tgt
              | (with_reducible apply qb0_caseOpt P_tgt) <;> try intro _
              | with_reducible apply qb0_bind_ret P_tgt
              | refine qb0_bind P_tgt
                  (qb0_query P_tgt (by
                    simp only [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget,
                      bhClassifyTargetOnly, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
                      Expr.v3, Expr.v4, Expr.v5, Expr.v6, Env.get, hpFalse, Bool.false_eq_true,
                      not_false_eq_true]))
                  (fun _ => ?_)
        ·
          exact isQueryBoundP_cliAdapterHandle_eval_ij_cr decT encT pKi pCtl pInst s i (.inl (p, c))
            hpFalse
        ·
          exact isQueryBoundP_cliAdapterHandle_eval_ij_cr decT encT pKi pCtl pInst s i (.inr p)
            hpFalse

private theorem simulateQ_run_stateT_of_step_le
    {ι κ σ α : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    {P_src : κ → Prop} [DecidablePred P_src] {P_tgt : ι → Prop} [DecidablePred P_tgt]
    {impl : QueryImpl G (StateT σ (OracleComp T))}
    (hstep : ∀ q s, ((impl q).run s).IsQueryBoundP P_tgt (if P_src q then 1 else 0))
    {oa : OracleComp G α} {n : ℕ}
    (hoa : oa.IsQueryBoundP P_src n) (s : σ) :
    ((simulateQ impl oa).run s).IsQueryBoundP P_tgt n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure a => simp [simulateQ_pure]
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rw [simulateQ_query_bind, StateT.run_bind]
    by_cases hp : P_src q
    · have hpos : 0 < n := hoa.1.resolve_left (not_not.mpr hp)
      have hcont : ∀ u, (cont u).IsQueryBoundP P_src (n - 1) := fun u => by
        simpa [hp] using hoa.2 u
      refine (isQueryBoundP_bind (hstep q s) fun z _ => ih z.1 (hcont z.1) z.2).mono ?_
      simp only [hp, ↓reduceIte]
      omega
    · have hcont : ∀ u, (cont u).IsQueryBoundP P_src n := fun u => by
        simpa [hp] using hoa.2 u
      refine (isQueryBoundP_bind (hstep q s) fun z _ => ih z.1 (hcont z.1) z.2).mono ?_
      simp only [hp, ↓reduceIte]
      omega

theorem isQueryBoundP_cliToModelAdapterProg_eval
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (pCtl : BHDRCtlQuery S → Bool)
    (pInst : ℕ → Bool)
    (A : CliGameAdversary S ℓ (BitVec 512)) (n : ℕ)
    (h : A.run.IsQueryBoundP (fun q => bhClassifyComposed pKi pCtl pInst q = true) n) :
    ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()).IsQueryBoundP
      (fun q => bhClassifyTarget pKi pCtl pInst q = true) n := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi pCtl pInst q = true
  have hAdv := isQueryBoundP_bhAdvRun pKi pCtl pInst A n h
  have hstep : ∀ (q : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain)
      (s : (cliAdapterStateTy S ℓ).denote),
      (((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).impl q).run s).IsQueryBoundP
        P_tgt (if bhClassifyGame pKi pCtl pInst q = true then 1 else 0) := by
    intro q s
    cases q with
    | inl m =>
      show ((e2eBhAdapterIface S ℓ).fwdU m >>= fun a => pure (a, s)).IsQueryBoundP P_tgt 0
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (isQueryBoundP_e2eBhAdapterIface_fwdU pKi pCtl pInst m)
        (fun a _ => isQueryBoundP_pure P_tgt (a, s) 0)
    | inr t =>
      show ((cliAdapterHandle decT encT S ℓ).eval
          (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc t) .nil)) >>=
          fun p => pure ((e2eBhAdapterCodec S ℓ).rdec t p.1, p.2)).IsQueryBoundP
        P_tgt (if bhClassifyGameOnly pKi pCtl pInst t = true then 1 else 0)
      simpa only [Nat.add_zero] using isQueryBoundP_bind
        (isQueryBoundP_cliAdapterHandle_eval decT encT pKi pCtl pInst s t)
        (fun p _ => isQueryBoundP_pure P_tgt ((e2eBhAdapterCodec S ℓ).rdec t p.1, p.2) 0)
  have hsim := simulateQ_run_stateT_of_step_le hstep hAdv
  have hinit :
      ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).init.eval
        (Env.cons (t := .unit) () Env.nil)).IsQueryBoundP P_tgt 0 := by
    dsimp only [cliToModelAdapterProg]
    exact qb0_ret P_tgt
  have hfin : ∀ s' b,
      ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).finish.eval
        (Env.cons s' (Env.cons b Env.nil))).IsQueryBoundP P_tgt 0 := by
    intro s' b
    dsimp only [cliToModelAdapterProg]
    exact qb0_ret P_tgt
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit
    (fun ⟨a, s⟩ _ =>
      isQueryBoundP_bind (hsim s)
        (fun ⟨b, s'⟩ _ => hfin s' b))).mono (by omega)

private theorem isQueryBoundP_congr_pred_local {ι α : Type} {spec : OracleSpec ι}
    {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x ↔ q x) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨h.1.imp (mt (hpq t).mpr) id, fun u => ?_⟩
    by_cases ht : p t
    · have hqt : q t := (hpq t).mp ht
      simpa [ht, hqt] using ih u (by simpa [ht] using h.2 u)
    · have hqt : ¬ q t := mt (hpq t).mpr ht
      simpa [ht, hqt] using ih u (by simpa [ht] using h.2 u)

/-- Per-instance `IsQueryBoundP` transfer for `cliToModelAdapterProg`. -/
theorem cliToModelAdapterProg_perInstanceQueryBounds
    (A : CliGameAdversary S ℓ (BitVec 512))
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hA : CliGameAdversaryPerInstanceBounded A b qStart qs) :
    let B_A :=
      (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval
        (fun _ => cliGameAdversaryReassoc A) ()
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
      (∑ k ∈ Finset.range qStart, qs k) ∧
    (∀ k < qStart, B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      (qs k)) := by
  rcases hA with ⟨⟨hRo, hSend, hRecv, hTot, _hOn, hCtl, hDr⟩, hStart, hInst⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isQueryBoundP_cliToModelAdapterProg_eval decT encT
      (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) A b.q_ro
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [simp [bhClassifyComposed];
          (cases kq <;> simp [bhClassifyComposed]); simp [bhClassifyComposed];
          simp [bhClassifyComposed]]) hRo)
  · exact isQueryBoundP_cliToModelAdapterProg_eval decT encT
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (fun _ => false) (fun _ => false) A S.N_send_tot
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [simp [bhClassifyComposed];
          (cases kq <;> simp [bhClassifyComposed]); simp [bhClassifyComposed];
          simp [bhClassifyComposed]]) hSend)
  · exact isQueryBoundP_cliToModelAdapterProg_eval decT encT
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (fun _ => false) (fun _ => false) A S.N_recv_tot
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [simp [bhClassifyComposed];
          (cases kq <;> simp [bhClassifyComposed]); simp [bhClassifyComposed];
          simp [bhClassifyComposed]]) hRecv)
  · exact isQueryBoundP_cliToModelAdapterProg_eval decT encT
      (fun _ => true) (fun _ => false) (fun _ => false) A b.q_total
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> simp [bhClassifyComposed]) hTot)
  · exact isQueryBoundP_cliToModelAdapterProg_eval decT encT
      (fun _ => false) (fun _ => true) (fun _ => false) A S.N_send_tot
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> simp [bhClassifyComposed]) hCtl)
  · exact isQueryBoundP_cliToModelAdapterProg_eval decT encT
      (fun _ => false) (fun _ => true) (fun _ => false) A qStart
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> simp [bhClassifyComposed]) hStart)
  · exact isQueryBoundP_cliToModelAdapterProg_eval decT encT
      (fun _ => false) (fun _ => false) (fun _ => true) A (∑ k ∈ Finset.range qStart, qs k)
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> simp [bhClassifyComposed]) hDr)
  · intro k hk
    exact isQueryBoundP_cliToModelAdapterProg_eval decT encT
      (fun _ => false) (fun _ => false) (fun i => i == k) A (qs k)
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;>
          simp [bhClassifyComposed, bhIsInstQueryWithSpqr]) (hInst k hk))

end CostAndQueryBounds

/-! ## Experiment equivalence with `L_bh` -/

section ExperimentEquivalence
attribute [local simp] env_get_zero env_get_succ

private theorem probComp_bind_congr_support {α β : Type}
    (oa : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ a ∈ support oa, f a = g a) :
    oa >>= f = oa >>= g := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a (by simp)
  | query_bind t mx ih =>
    simp only [bind_assoc]
    congr 1
    funext u
    exact ih u (fun a ha => h a (by simp only [mem_support_bind_iff]; exact ⟨u, by simp, ha⟩))

private theorem probComp_bind_eq_map_bind {α β γ : Type}
    (oa : ProbComp α) {f : α → ProbComp γ} {g : α → ProbComp β} (m : β → γ)
    (h : ∀ a ∈ support oa, f a = m <$> g a) :
    (oa >>= f) = m <$> (oa >>= g) := by
  rw [map_bind]
  exact probComp_bind_congr_support oa h

private theorem tset_map_option {α β : Type} (f : α → β) (tbl : ℕ → Option α) (i : ℕ) (v : α) :
    (fun j => if j = i then some (f v) else (tbl j).map f) =
      (fun j => (if j = i then some v else tbl j).map f) := by
  funext j
  split_ifs <;> rfl

private theorem e2eReadProstVarint_eq :
    ∀ bs : List (BitVec 8),
      CryptoVerification.E2E.Costed.e2eReadProstVarint bs =
        CryptoVerification.E2E.bhReadProstVarint bs
  | [] => rfl
  | b :: rest => by
    simp only [CryptoVerification.E2E.Costed.e2eReadProstVarint,
      CryptoVerification.E2E.bhReadProstVarint]
    split_ifs
    · rfl
    · rw [e2eReadProstVarint_eq rest]

private theorem e2eParseOptPreKeyId_eq (bs : List (BitVec 8)) :
    CryptoVerification.E2E.Costed.e2eParseOptPreKeyId bs =
      CryptoVerification.E2E.bhParseOptPreKeyId bs := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    simp only [CryptoVerification.E2E.Costed.e2eParseOptPreKeyId,
      CryptoVerification.E2E.bhParseOptPreKeyId, e2eReadProstVarint_eq]

private theorem e2eParseUint32Field_eq (k : BitVec 8) (bs : List (BitVec 8)) :
    CryptoVerification.E2E.Costed.e2eParseUint32Field k bs =
      CryptoVerification.E2E.bhParseUint32Field k bs := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    simp only [CryptoVerification.E2E.Costed.e2eParseUint32Field,
      CryptoVerification.E2E.bhParseUint32Field, e2eReadProstVarint_eq]

private theorem e2eParseInnerMsgField_eq (bs : List (BitVec 8)) :
    CryptoVerification.E2E.Costed.e2eParseInnerMsgField bs =
      CryptoVerification.E2E.bhParseInnerMsgFieldWithRest bs := by
  rcases bs with _ | ⟨b, rest⟩
  · rfl
  · by_cases hb : b = 0x22#8
    · subst hb
      simp only [CryptoVerification.E2E.Costed.e2eParseInnerMsgField,
        CryptoVerification.E2E.bhParseInnerMsgFieldWithRest, e2eReadProstVarint_eq]
    · simp [CryptoVerification.E2E.Costed.e2eParseInnerMsgField,
        CryptoVerification.E2E.bhParseInnerMsgFieldWithRest, hb]

private theorem e2eDecodePreKeyRaw_eq (c : Bytes) :
    CryptoVerification.E2E.Costed.e2eDecodePreKeyRaw c =
      CryptoVerification.E2E.bhDecodePreKeyMsgERaw c := by
  rcases c with _ | ⟨t, _ | ⟨v, proto⟩⟩
  · rfl
  · rfl
  · simp only [CryptoVerification.E2E.Costed.e2eDecodePreKeyRaw,
      CryptoVerification.E2E.bhDecodePreKeyMsgERaw,
      e2eParseOptPreKeyId_eq, e2eParseUint32Field_eq, e2eParseInnerMsgField_eq]
    rfl

theorem e2eDecodePreKeyMsg_eq (c : Bytes) :
    CryptoVerification.E2E.Costed.e2eDecodePreKeyMsg c = bhDecodePreKeyMsgE c := by
  unfold CryptoVerification.E2E.Costed.e2eDecodePreKeyMsg bhDecodePreKeyMsgE
  rw [e2eDecodePreKeyRaw_eq]
  cases CryptoVerification.E2E.bhDecodePreKeyMsgERaw c <;> rfl

private theorem parsePreKeyWire_eval_eq (ℓ : ℕ) (c : Bytes) :
    E2EPureOp.eval ℓ .parsePreKeyWire c =
      (bhDecodePreKeyMsgE c).map fun m => (m.regId, (hdrV (ℓ := ℓ) (bhHdrOfPreKeyMsg m), m.inner)) := by
  change (e2ePureOps ℓ).eval .parsePreKeyWire c = _
  rw [Computational.Proofs.E2E.Dsl.ClampsLossless.e2ePureOps_eval_parsePreKeyWire_lossless,
    e2eDecodePreKeyMsg_eq]
  rfl

private theorem partneredInnerBytes_isSome_eq_updateInstMeta_fst
    {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (inst : BHAdapterInstMeta S) (c : Bytes) (m : CryptoVerification.E2E.PreKeyMessageFields)
    (hm : bhDecodePreKeyMsgE c = some m) :
    (match E2EPureOp.eval ℓ .partneredInnerBytes
        (inst.bobAccepted, (bhInitRegId inst.sid, (hdrV (ℓ := ℓ) inst.hdr, c))) with
     | none => false
     | some _ => true) =
      (bhShallowUpdateInstMeta inst false false c).1 := by
  dsimp only [E2EPureOp.eval, bhShallowUpdateInstMeta]
  rw [Computational.Proofs.E2E.Dsl.ClampsLossless.e2ePartneredInnerBytes_lossless,
    e2eDecodePreKeyMsg_eq, hdrOfV_hdrV, hm]
  cases inst.bobAccepted
  · dsimp only [Bool.not_false, ↓reduceIte]
    have hExp : CryptoVerification.E2E.Costed.e2eExpectedPreKeyMsg (bhInitRegId inst.sid)
        inst.hdr m.inner = bhExpectedPreKeyMsg (bhInitRegId inst.sid) inst.hdr m.inner := rfl
    rw [hExp]
    cases (c == wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId inst.sid) inst.hdr m.inner).bytes) <;>
      rfl
  · dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hHdr : CryptoVerification.E2E.Costed.e2eHdrOfPreKeyMsg m = bhHdrOfPreKeyMsg m := rfl
    rw [hHdr]
    cases (bhHdrOfPreKeyMsg m == inst.hdr) <;> rfl

private theorem bh_split_wrapWhisperWire (y : Bytes) :
    bhShallowSplitWhisper (bhShallowWrapWhisper y) =
      if y.isEmpty then none else some y := by
  cases y with
  | nil => rfl
  | cons b bs =>
    simp only [bhShallowWrapWhisper, bhShallowSplitWhisper,
      List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]

private theorem encodeSessionRecord_instMetaToV_eq
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {C : Crypto} {K : MlKem}
    (inst : BHAdapterInstMeta S) (g : GhostState Bytes)
    (hg : Computational.Proofs.E2E.Dsl.SmReachInvParty.PartyReachInv C K g) :
    e2eEncodeSessionRecord (ℓ := ℓ) ((instMetaToV (ℓ := ℓ) inst).1, g) =
      bhBinStateOfParty inst g := by
  dsimp only [instMetaToV]
  rw [hg.encodeSessionRecord_lossless]
  unfold bhBinStateOfParty CryptoVerification.E2E.binStateOfUnderExtras
    CryptoVerification.E2E.encodeRecordUnderExtras e2eRecordExtras
  rw [hdrOfV_hdrV]
  cases g.party <;> rfl

private theorem bhE2EStepLocalSm_cr_partyReachInv
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ}
    (hReach : Computational.Proofs.E2E.Dsl.SmReachInv.DrvSmReachInv C K σ)
    (i : ℕ) (p : Party)
    {r1 : Option Bytes} {r2 : Option (CryptoGames.SM.RecvResult (Plain ℓ))}
    {g : GhostState Bytes} {σ' : BHE2EDrvState S ℓ}
    (hout : ((r1, r2, some g), σ') ∈
      support (CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i (.inr p))) :
    Computational.Proofs.E2E.Dsl.SmReachInvParty.PartyReachInv C K g := by
  unfold CryptoVerification.E2E.bhE2EStepLocalSm at hout
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp [hcl] at hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp [hd] at hout
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp [hd, him] at hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted &&
            CryptoVerification.E2E.bhIsBobRecvSMQuery (ℓ := ℓ) (PQC := BitVec 512) (.inr p) &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d
        · simp [hcorr] at hout
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => simp [hgs] at hout
          | some gs =>
            simp only [hgs, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
            rcases hout with ⟨⟨r, gs'⟩, hcr, hEq⟩
            have hdMem : d ∈ σ.insts := List.mem_of_getElem? hd
            have hgsInv := hReach d hdMem gs hgs
            have hrEq : r = some g := by
              have hfst := (Prod.mk.inj hEq).1
              dsimp only [CryptoVerification.E2E.bhPackSmResp] at hfst
              exact (Prod.mk.inj (Prod.mk.inj hfst).2).2.symm
            subst hrEq
            change (some g, gs') ∈ support
              ((CryptoGames.SM.corrR (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT)
                p).run gs) at hcr
            unfold CryptoGames.SM.corrR at hcr
            simp only [StateT.run_bind, StateT.run_get, pure_bind] at hcr
            by_cases href : gs.win || !gs.corrAllowed p ||
                ((CryptoVerification.E2E.configRefuseEarlyBobCorr
                  (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).r1 &&
                  CryptoGames.SM.inWindow gs p) ||
                !(CryptoVerification.E2E.configRefuseEarlyBobCorr
                  (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).corrOK gs p
            · simp [href, StateT.run_pure] at hcr
            · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
                Option.some.injEq] at hcr
              rcases hcr with ⟨rfl, _⟩
              exact hgsInv.party p

private theorem versionByte_ne_wireWhisper (v : BitVec 8) :
    CryptoGames.LibsignalSession.versionByte v ≠ wireWhisper := by
  have hAll : ∀ w : BitVec 8, CryptoGames.LibsignalSession.versionByte w ≠ wireWhisper := by decide
  exact hAll v

private theorem mut_exec_bind {σ α β : Type} (m : CryptoGames.LibsignalSession.Mut σ α)
    (f : α → CryptoGames.LibsignalSession.Mut σ β) (s : σ) :
    (m >>= f).exec s =
      match m.exec s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => (f a).exec s' := by
  unfold CryptoGames.LibsignalSession.Mut.exec
  rw [ExceptT.run_bind, StateT.run_bind]
  cases m.run.run s with
  | mk res _ => cases res <;> rfl

private theorem mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    (pure a : CryptoGames.LibsignalSession.Mut σ α).exec s = (.ok a, s) := rfl

private theorem mut_exec_get {σ : Type} (s : σ) :
    (get : CryptoGames.LibsignalSession.Mut σ σ).exec s = (.ok s, s) := rfl

private theorem mut_exec_set {σ : Type} (s' s : σ) :
    (set s' : CryptoGames.LibsignalSession.Mut σ Unit).exec s = (.ok (), s') := rfl

private theorem mut_exec_throw {σ α : Type} (e : CryptoGames.LibsignalSession.SignalProtocolError)
    (s : σ) :
    (throw e : CryptoGames.LibsignalSession.Mut σ α).exec s = (.error e, s) := rfl

private theorem mut_exec_liftE {σ α : Type}
    (r : Except CryptoGames.LibsignalSession.SignalProtocolError α) (s : σ) :
    (CryptoGames.LibsignalSession.liftE r : CryptoGames.LibsignalSession.Mut σ α).exec s =
      (r, s) := by
  cases r <;> rfl

private theorem fixedSpk_send_wire_props (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (ℓ : ℕ) (s : BitVec 256)
    (g : GhostState Bytes) (pt : Plain ℓ) (r : BitVec 512) :
    let ct :=
      ((CryptoVerification.E2E.sessionSchemeFixedSpk
        (CryptoVerification.E2E.paramsIdsWithSpqr C
          (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
        ℓ s).send g pt r).2
    ct.length ≤ 32 * (ℓ / 32) + 450 ∧ ∀ rest, ct ≠ wireWhisper :: rest := by
  dsimp only [CryptoVerification.E2E.sessionSchemeFixedSpk, CryptoGames.LibsignalSession.Params.send,
    CryptoGames.LibsignalSession.SessionState.messageEncrypt]
  cases hfrom :
      CryptoGames.LibsignalSession.OutgoingTripleRatchet.fromSessionState.exec g.session with
  | mk resFrom taken =>
    cases resFrom with
    | error _ =>
      dsimp only
      exact ⟨by simp, fun _ h => nomatch h⟩
    | ok o0 =>
      dsimp only
      let P0 := CryptoVerification.E2E.paramsIdsWithSpqr C
        (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB
      cases henc :
          (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt P0.C P0.codec P0.spqr
            pt.toList (g.session.encryptAddresses (P0.sendAddrs g.party)) r).exec o0 with
      | mk resEnc o1 =>
        cases resEnc with
        | error _ =>
          dsimp only
          exact ⟨by simp, fun _ h => nomatch h⟩
        | ok msg =>
          dsimp only
          unfold CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt at henc
          rw [mut_exec_bind, mut_exec_get] at henc
          dsimp only at henc
          cases hpan : P0.spqr.sendPanics o0.pqrState r
          · simp only [hpan, Bool.false_eq_true, ↓reduceIte] at henc
            try rw [mut_exec_bind, mut_exec_pure] at henc
            cases hsp : P0.spqr.send o0.pqrState r with
            | none =>
              rw [hsp, mut_exec_throw] at henc
              cases henc
            | some triple =>
              rcases triple with ⟨newPq, pqKey, pqMsg⟩
              rw [hsp] at henc
              dsimp only at henc
              rw [mut_exec_bind, mut_exec_liftE] at henc
              cases hnext : o0.senderChainKey.nextChainKey P0.C.F with
              | error _ =>
                rw [hnext] at henc
                cases henc
              | ok ckNext =>
                rw [hnext] at henc
                dsimp only at henc
                rw [mut_exec_bind, mut_exec_set] at henc
                dsimp only at henc
                rw [mut_exec_pure] at henc
                injection henc with hok _
                injection hok with hmsg
                rw [← hmsg]
                have hct :
                    (CryptoGames.LibsignalSession.aesCbcEncrypt C.E
                      ((o0.senderChainKey.messageKeys C.F).generateKeys C.F pqKey).cipherKey
                      ((o0.senderChainKey.messageKeys C.F).generateKeys C.F pqKey).iv
                      pt.toList).length ≤ 32 * (ℓ / 32 + 2) := by
                  rw [Computational.Proofs.E2E.Dsl.ClampsLossless.aesCbcEncrypt_length_eq]
                  omega
                have hpq : pqMsg.length ≤ 96 :=
                  Computational.Proofs.E2E.Dsl.SmReachInvParty.spqrV1Send_pqMsg_length_le_96
                    C.F K o0.pqrState r hsp
                have haddr :
                    ∀ a ∈ g.session.encryptAddresses (P0.sendAddrs g.party), a.length ≤ 128 := by
                  intro a ha
                  unfold CryptoGames.LibsignalSession.SessionState.encryptAddresses at ha
                  cases hp : g.session.pendingPreKey with
                  | false => simp [hp] at ha
                  | true =>
                    simp only [hp, ↓reduceIte] at ha
                    cases hgP : g.party <;> {
                      rw [hgP] at ha
                      exact Computational.Proofs.E2E.Dsl.SmReachInvParty.serializedPartyAddresses_length_le_128
                        _ _ _ a ha
                    }
                refine ⟨Computational.Proofs.E2E.Dsl.ClampsLossless.signalMsgNew_serialized_length_le
                  C.F o0.sessionVersion _ _ o0.senderRatchetKey.publicKey o0.senderChainKey.index
                  o0.previousCounter _ o0.localIdentityKey o0.remoteIdentityKey pqMsg hct hpq haddr,
                  ?_⟩
                intro rest hcons
                dsimp only [CryptoGames.LibsignalSession.SignalMessage.new,
                  CryptoGames.LibsignalSession.serializeContent,
                  List.cons_append] at hcons
                exact versionByte_ne_wireWhisper o0.sessionVersion (List.cons.inj hcons).1
          · simp only [hpan, ↓reduceIte] at henc
            try rw [mut_exec_bind] at henc
            rw [mut_exec_throw] at henc
            cases henc

private def DrvNoWhisperTrans {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : BHE2EDrvState S ℓ) : Prop :=
  ∀ d ∈ σ.insts, ∀ gs ∈ d.gs, ∀ rec_ ∈ gs.trans, ∀ rest, rec_.ct ≠ wireWhisper :: rest

private theorem drvNoWhisperTrans_init {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (b : Bool) (st : SignalPqxdh.KeyIndState S) :
    DrvNoWhisperTrans ({ b := b, st := st } : BHE2EDrvState S ℓ) :=
  fun _ hd => nomatch hd

private theorem drvNoWhisperTrans_mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {σ : BHE2EDrvState S ℓ} (h : DrvNoWhisperTrans σ)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse) :
    DrvNoWhisperTrans (CryptoVerification.E2E.bhE2EMirror σ kq kr) :=
  h

private theorem drvNoWhisperTrans_compositionLocalStart {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {σ : BHE2EDrvState S ℓ} (h : DrvNoWhisperTrans σ) (sid : SignalPqxdh.SessionId S)
    {out : Option ℕ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (CryptoVerification.E2E.compositionLocalStart ki C K bMode? σ sid)) :
    DrvNoWhisperTrans out.2 := by
  unfold CryptoVerification.E2E.compositionLocalStart at hout
  split at hout
  · simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact h
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr1, st1⟩, -, ⟨kr2, st2⟩, -, ac, -, rfl⟩
    unfold CryptoVerification.E2E.bhE2EFinishStartSpk
    split
    · split_ifs
      · intro d hd gs hgs
        rcases List.mem_append.mp hd with hd0 | hd1
        · exact h d hd0 gs hgs
        · simp only [List.mem_singleton] at hd1
          subst hd1
          rcases Option.mem_map.mp hgs with ⟨b, -, rfl⟩
          intro rec_ hrec
          simp [CryptoGames.SM.initState] at hrec
      · exact h
    · exact h

private theorem epMgmt_trans_eq {ℓ : ℕ}
    {gs s1 : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hep : gs.epMgmt Δ qep P bad = some s1) :
    s1.trans = gs.trans := by
  unfold CryptoGames.SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (gs.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    by_cases hq1 : qep < gs.epoch P + 1
    · simp only [hq1, ↓reduceIte] at hep
      cases hep
    · simp only [hq1, ↓reduceIte] at hep
      by_cases hbad : (bad && !gs.safeCh Δ P) = true
      · simp only [hbad, ↓reduceIte, Option.some.injEq] at hep
        subst hep; rfl
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hep
        subst hep; rfl
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    by_cases hq2 : qep < gs.epoch P
    · simp only [hq2, ↓reduceIte] at hep
      cases hep
    · simp only [hq2, ↓reduceIte, Option.some.injEq] at hep
      subst hep; rfl

private theorem noWhisper_oracleImplR (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (ℓ Δ qep : ℕ) (s : BitVec 256)
    (cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (qry : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {gs : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (h : ∀ rec_ ∈ gs.trans, ∀ rest, rec_.ct ≠ wireWhisper :: rest)
    {out : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range qry ×
      CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hout : out ∈ support
      ((CryptoGames.SM.oracleImplR
          (CryptoVerification.E2E.sessionSchemeFixedSpk
            (CryptoVerification.E2E.paramsIdsWithSpqr C
              (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB)
            ℓ s) Δ qep cfg qry).run gs)) :
    ∀ rec_ ∈ out.2.trans, ∀ rest, rec_.ct ≠ wireWhisper :: rest := by
  let sm := CryptoVerification.E2E.sessionSchemeFixedSpk
    (CryptoVerification.E2E.paramsIdsWithSpqr C
      (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K) idA idB) ℓ s
  rcases qry with (((⟨P, m, optR⟩ | ⟨P, m0, m1, optR⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change out ∈ support ((CryptoGames.SM.transmitR sm Δ qep cfg (P, m, optR)).run gs) at hout
    unfold CryptoGames.SM.transmitR CryptoGames.SM.transmitImpl at hout
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hok : !cfg.sendOK gs P
    · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact h
    · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
        pure_bind] at hout
      by_cases hwin : gs.win
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact h
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
        rcases hout with ⟨⟨⟨coins, bad⟩, s0⟩, ⟨_, -, hpair⟩, hout⟩
        have hs0 : s0 = gs := (Prod.mk.inj hpair).2; subst s0
        dsimp only at hout
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact h
        | some s1 =>
          simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hout
          subst hout
          intro rec_ hrec
          simp only [CryptoGames.SM.GameState.record, epMgmt_trans_eq hep, List.mem_cons] at hrec
          rcases hrec with rfl | hmem
          · exact (fixedSpk_send_wire_props C K idA idB ℓ s (s1.st P) m coins).2
          · exact h rec_ hmem
  · change out ∈ support ((CryptoGames.SM.challR sm Δ qep cfg (P, m0, m1, optR)).run gs) at hout
    unfold CryptoGames.SM.challR CryptoGames.SM.challImpl at hout
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hok : !cfg.sendOK gs P
    · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact h
    · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
        pure_bind] at hout
      by_cases hwin : gs.win
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact h
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
        rcases hout with ⟨⟨⟨coins, bad⟩, s0⟩, ⟨_, -, hpair⟩, hout⟩
        have hs0 : s0 = gs := (Prod.mk.inj hpair).2; subst s0
        dsimp only at hout
        cases hep : gs.epMgmt Δ qep P bad with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact h
        | some s1 =>
          rw [hep] at hout; dsimp only at hout
          by_cases hsafe : !s1.safeCh Δ P || !cfg.base.challAllowedIn (s1.epoch P)
          · simp only [hsafe, ↓reduceIte, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hout
            subst hout; exact h
          · simp only [hsafe, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
            subst hout
            intro rec_ hrec
            simp only [CryptoGames.SM.GameState.record, epMgmt_trans_eq hep, List.mem_cons] at hrec
            rcases hrec with rfl | hmem
            · exact (fixedSpk_send_wire_props C K idA idB ℓ s (s1.st P) _ coins).2
            · exact h rec_ hmem
  · change out ∈ support ((CryptoGames.SM.deliverR sm cfg (P, c)).run gs) at hout
    unfold CryptoGames.SM.deliverR at hout
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases hwin : gs.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact h
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hout
      cases htr : gs.inTransit P.other c with
      | none =>
        simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact h
      | some rec0 =>
        simp only [htr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
        rcases hout with ⟨⟨rc, s0⟩, ⟨_, -, hpair⟩, hout⟩
        have hs0 : s0 = gs := (Prod.mk.inj hpair).2; subst s0
        dsimp only at hout
        cases hrecv : sm.receive (gs.st P) c rc with
        | none =>
          rw [hrecv] at hout; dsimp only at hout
          by_cases hmust : cfg.base.deliverWin && cfg.must gs P rec0
          · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact h
          · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact h
        | some quad =>
          rcases quad with ⟨st', t', i', m'⟩
          rw [hrecv] at hout; dsimp only at hout
          have hacc : ∀ rec_ ∈ (gs.accept P st' rec0.pos).trans,
              ∀ rest, rec_.ct ≠ wireWhisper :: rest := by
            intro rec_ hrec
            simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete,
              List.mem_filter] at hrec
            exact h rec_ hrec.1
          by_cases hbad : cfg.base.deliverWin && cfg.must gs P rec0 &&
              !decide ((t', i', m') = (rec0.pos.epoch, rec0.pos.idx, rec0.msg))
          · simp only [hbad, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact hacc
          · simp only [hbad, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact hacc
  · change out ∈ support ((CryptoGames.SM.injectR sm Δ qep cfg (P, c)).run gs) at hout
    rw [CryptoVerification.E2E.BhAdapterIjHelpersV1.injectR_run] at hout
    by_cases href : gs.win || (gs.inTransit P.other c).isSome || !gs.safeInj Δ || !cfg.injOK c
    · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact h
    · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hout
      rcases hout with ⟨rc, -, rfl⟩
      dsimp only [CryptoVerification.E2E.BhAdapterIjHelpersV1.injectPost]
      cases sm.receive (gs.st P) c rc with
      | none => exact h
      | some quad =>
        rcases quad with ⟨st', t', i', m'⟩
        dsimp only
        by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte]; exact h
        · simp only [hqep, ↓reduceIte]
          have hacc : ∀ rec_ ∈ (gs.accept P st' ⟨P.other, t', i'⟩).trans,
              ∀ rest, rec_.ct ≠ wireWhisper :: rest := by
            intro rec_ hrec
            simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete,
              List.mem_filter] at hrec
            exact h rec_ hrec.1
          by_cases htriv : gs.trivial Δ ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte]; exact hacc
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
            by_cases hfull : cfg.base.injectFull t'
            · simp only [hfull, ↓reduceIte]; exact h
            · simp only [hfull, Bool.false_eq_true, ↓reduceIte]; exact h
  · change out ∈ support ((CryptoGames.SM.corrR cfg P).run gs) at hout
    unfold CryptoGames.SM.corrR at hout
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hout
    by_cases href : gs.win || !gs.corrAllowed P ||
        (cfg.r1 && CryptoGames.SM.inWindow gs P) || !cfg.corrOK gs P
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact h
    · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact h

private theorem mem_list_set_or {α : Type} :
    ∀ (l : List α) (i : ℕ) (x y : α), y ∈ l.set i x → y = x ∨ y ∈ l
  | [], _, _, _, hy => nomatch hy
  | _ :: as, 0, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ hmem)
  | a :: as, i + 1, x, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Or.inr List.mem_cons_self
    · rcases mem_list_set_or as i x y hmem with rfl | hmem'
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem a hmem')

private theorem drvNoWhisperTrans_bhE2EStepLocalSm {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} (h : DrvNoWhisperTrans σ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : CryptoVerification.E2E.BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    DrvNoWhisperTrans out.2 := by
  unfold CryptoVerification.E2E.bhE2EStepLocalSm at hout
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout; subst hout; exact h
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp only [hd, support_pure, Set.mem_singleton_iff] at hout; subst hout; exact h
    | some d =>
      cases him : σ.instMeta[i]? with
      | none =>
        simp only [hd, him, support_pure, Set.mem_singleton_iff] at hout; subst hout; exact h
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && CryptoVerification.E2E.bhIsBobRecvSMQuery sq &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact h
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none =>
            simp only [hgs, support_pure, Set.mem_singleton_iff] at hout; subst hout; exact h
          | some gs =>
            simp only [hgs] at hout
            have hdMem : d ∈ σ.insts := List.mem_of_getElem? hd
            have hgsInv := h d hdMem gs hgs
            have hrunStd :
                ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ)
                    (BitVec 512) Bytes).Domain),
                out ∈ support (do
                  let (r, gs') ← (CryptoGames.SM.oracleImplR
                    (CryptoVerification.E2E.sessionSchemeFixedSpk
                      (CryptoVerification.E2E.paramsIdsWithSpqr C
                        (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                        d.idA d.idB)
                      ℓ d.spkCoins) (2 + 1) qep
                    (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT) q').run gs
                  let accepted := CryptoVerification.E2E.bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true,
                                ikACorrAtAccept := CryptoVerification.E2E.bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (CryptoVerification.E2E.bhPackSmResp q' r, σ1)) →
                DrvNoWhisperTrans out.2 := by
              intro q' hrun
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrun
              rcases hrun with ⟨⟨r, gs'⟩, hstep, rfl⟩
              have hgs' := noWhisper_oracleImplR C K d.idA d.idB ℓ (2 + 1) qep d.spkCoins _ q'
                hgsInv hstep
              intro d' hd' gs0 hgs0
              rcases mem_list_set_or σ.insts i { d with gs := some gs' } d' hd' with rfl | hmem
              · simp only [Option.mem_def, Option.some.injEq] at hgs0
                subst hgs0
                exact hgs'
              · exact h d' hmem gs0 hgs0
            have hpure : out ∈ support (pure ((none, none, none), σ) :
                ProbComp (CryptoVerification.E2E.BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) →
                DrvNoWhisperTrans out.2 := by
              simp only [support_pure, Set.mem_singleton_iff]
              intro heq; subst heq; exact h
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · exact hrunStd _ hout
            · exact hrunStd _ hout
            · cases pDl
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunStd _ hout
              · dsimp only at hout
                split_ifs at hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; exact hrunStd _ hout
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
                  · rw [hdec] at hout; exact hrunStd _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
            · exact hrunStd _ hout

private theorem bhE2EStepLocalSm_tr_len_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (p : Party) (m : Plain ℓ) (optR : Option (BitVec 512))
    {ct : Bytes} {r2 : Option (CryptoGames.SM.RecvResult (Plain ℓ))}
    {r3 : Option (GhostState Bytes)} {σ' : BHE2EDrvState S ℓ}
    (hout : ((some ct, r2, r3), σ') ∈ support
      (CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i
        (.inl (.inl (.inl (.inl (p, m, optR))))))) :
    ct.length ≤ 32 * (ℓ / 32) + 450 := by
  unfold CryptoVerification.E2E.bhE2EStepLocalSm at hout
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp [hcl] at hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp [hd] at hout
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp [hd, him] at hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hbob : (!im.bobAccepted &&
            CryptoVerification.E2E.bhIsBobRecvSMQuery (ℓ := ℓ) (PQC := BitVec 512)
              (.inl (.inl (.inl (.inl (p, m, optR))))) &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d) = true
        · simp [hbob] at hout
        · simp only [hbob, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => simp [hgs] at hout
          | some gs =>
            simp only [hgs, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
            rcases hout with ⟨⟨r, gs'⟩, htr, hEq⟩
            have hr : r = some ct := (Prod.mk.inj (Prod.mk.inj hEq).1).1.symm
            subst r
            change (some ct, gs') ∈ support
              ((CryptoGames.SM.transmitR
                (CryptoVerification.E2E.sessionSchemeFixedSpk
                  (CryptoVerification.E2E.paramsIdsWithSpqr C
                    (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                    d.idA d.idB) ℓ d.spkCoins)
                (2 + 1) qep
                (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT)
                (p, m, optR)).run gs) at htr
            unfold CryptoGames.SM.transmitR CryptoGames.SM.transmitImpl at htr
            simp only [StateT.run_bind, StateT.run_get, pure_bind] at htr
            by_cases hok : !(CryptoVerification.E2E.configRefuseEarlyBobCorr
                (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs p
            · simp [hok, StateT.run_pure] at htr
            · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
                pure_bind] at htr
              by_cases hwin : gs.win
              · simp [hwin, StateT.run_pure] at htr
              · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                  StateT.run_monadLift, monadLift_self, mem_support_bind_iff, support_pure,
                  Set.mem_singleton_iff] at htr
                rcases htr with ⟨⟨⟨coins, bad⟩, s0⟩, ⟨_, -, hpair⟩, htr⟩
                have hs0 : s0 = gs := (Prod.mk.inj hpair).2; subst s0
                dsimp only at htr
                cases hep : gs.epMgmt (2 + 1) qep p bad with
                | none => simp [hep, StateT.run_pure] at htr
                | some s1 =>
                  simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                    support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at htr
                  rcases htr with ⟨rfl, _⟩
                  exact (fixedSpk_send_wire_props C K d.idA d.idB ℓ d.spkCoins (s1.st p) m coins).1

private theorem bhE2EStepLocalSm_ch_len_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (p : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512))
    {ct : Bytes} {r2 : Option (CryptoGames.SM.RecvResult (Plain ℓ))}
    {r3 : Option (GhostState Bytes)} {σ' : BHE2EDrvState S ℓ}
    (hout : ((some ct, r2, r3), σ') ∈ support
      (CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i
        (.inl (.inl (.inl (.inr (p, m0, m1, optR))))))) :
    ct.length ≤ 32 * (ℓ / 32) + 450 := by
  unfold CryptoVerification.E2E.bhE2EStepLocalSm at hout
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp [hcl] at hout
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none => simp [hd] at hout
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => simp [hd, him] at hout
      | some im =>
        simp only [hd, him] at hout
        by_cases hbob : (!im.bobAccepted &&
            CryptoVerification.E2E.bhIsBobRecvSMQuery (ℓ := ℓ) (PQC := BitVec 512)
              (.inl (.inl (.inl (.inr (p, m0, m1, optR))))) &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d) = true
        · simp [hbob] at hout
        · simp only [hbob, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none => simp [hgs] at hout
          | some gs =>
            simp only [hgs, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
            rcases hout with ⟨⟨r, gs'⟩, hch, hEq⟩
            have hr : r = some ct := (Prod.mk.inj (Prod.mk.inj hEq).1).1.symm
            subst r
            change (some ct, gs') ∈ support
              ((CryptoGames.SM.challR
                (CryptoVerification.E2E.sessionSchemeFixedSpk
                  (CryptoVerification.E2E.paramsIdsWithSpqr C
                    (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                    d.idA d.idB) ℓ d.spkCoins)
                (2 + 1) qep
                (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT)
                (p, m0, m1, optR)).run gs) at hch
            unfold CryptoGames.SM.challR CryptoGames.SM.challImpl at hch
            simp only [StateT.run_bind, StateT.run_get, pure_bind] at hch
            by_cases hok : !(CryptoVerification.E2E.configRefuseEarlyBobCorr
                (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).sendOK gs p
            · simp [hok, StateT.run_pure] at hch
            · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
                pure_bind] at hch
              by_cases hwin : gs.win
              · simp [hwin, StateT.run_pure] at hch
              · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                  StateT.run_monadLift, monadLift_self, mem_support_bind_iff, support_pure,
                  Set.mem_singleton_iff] at hch
                rcases hch with ⟨⟨⟨coins, bad⟩, s0⟩, ⟨_, -, hpair⟩, hch⟩
                have hs0 : s0 = gs := (Prod.mk.inj hpair).2; subst s0
                dsimp only at hch
                cases hep : gs.epMgmt (2 + 1) qep p bad with
                | none => simp [hep, StateT.run_pure] at hch
                | some s1 =>
                  rw [hep] at hch; dsimp only at hch
                  by_cases hsafe : !s1.safeCh (2 + 1) p ||
                      !(CryptoVerification.E2E.configRefuseEarlyBobCorr
                        (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).base.challAllowedIn
                        (s1.epoch p)
                  · simp [hsafe, StateT.run_pure] at hch
                  · simp only [hsafe, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
                      StateT.run_set, StateT.run_pure, pure_bind, support_pure,
                      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hch
                    rcases hch with ⟨rfl, _⟩
                    exact (fixedSpk_send_wire_props C K d.idA d.idB ℓ d.spkCoins (s1.st p) _ coins).1

private theorem bhDecodePreKeyMsgE_wireWhisper_cons (r : Bytes) :
    CryptoVerification.E2E.bhDecodePreKeyMsgE (wireWhisper :: r) = none := by
  unfold CryptoVerification.E2E.bhDecodePreKeyMsgE CryptoVerification.E2E.bhDecodePreKeyMsgERaw
  rcases r with _ | ⟨v, proto⟩
  · rfl
  · have hne : (wireWhisper == wirePrekey) = false := by decide
    simp [hne]

private theorem inTransit_wireWhisper_isSome_eq_false {ℓ : ℕ}
    {gs : CryptoGames.SM.GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hNoWhisp : ∀ rec_ ∈ gs.trans, ∀ rest, rec_.ct ≠ wireWhisper :: rest)
    (P : Party) (r : Bytes) :
    (gs.inTransit P (wireWhisper :: r)).isSome = false := by
  unfold CryptoGames.SM.GameState.inTransit
  cases hf : gs.trans.find? (fun x => x.pos.sender == P && decide (x.ct = wireWhisper :: r)) with
  | none => rfl
  | some rec_ =>
    have hmem := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    rcases Bool.and_eq_true_iff.mp hp with ⟨_, hct⟩
    exact False.elim (hNoWhisp rec_ hmem r (of_decide_eq_true hct))

private theorem bhE2EStepLocalSm_ij_wireWhisper_irrel {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} (hNoWhisp : DrvNoWhisperTrans σ)
    (i : ℕ) (P : Party) (r₁ r₂ : Bytes) :
    CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i
        (.inl (.inr (P, wireWhisper :: r₁))) =
      CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i
        (.inl (.inr (P, wireWhisper :: r₂))) := by
  unfold CryptoVerification.E2E.bhE2EStepLocalSm
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp [hcl]
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
    cases hd : σ.insts[i]? with
    | none => rfl
    | some d =>
      cases him : σ.instMeta[i]? with
      | none => rfl
      | some im =>
        have hBobEq :
            CryptoVerification.E2E.bhIsBobRecvSMQuery (ℓ := ℓ) (PQC := BitVec 512)
              (.inl (.inr (P, wireWhisper :: r₁))) =
            CryptoVerification.E2E.bhIsBobRecvSMQuery (ℓ := ℓ) (PQC := BitVec 512)
              (.inl (.inr (P, wireWhisper :: r₂))) := by cases P <;> rfl
        simp only [hBobEq]
        by_cases hbob : (!im.bobAccepted &&
            CryptoVerification.E2E.bhIsBobRecvSMQuery (ℓ := ℓ) (PQC := BitVec 512)
              (.inl (.inr (P, wireWhisper :: r₂))) &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d) = true
        · simp [hbob]
        · simp only [hbob, Bool.false_eq_true, ↓reduceIte]
          cases hgs : d.gs with
          | none => rfl
          | some gs =>
            have hdMem : d ∈ σ.insts := List.mem_of_getElem? hd
            have hgsNW := hNoWhisp d hdMem gs hgs
            have hRunEq :
                (CryptoGames.SM.oracleImplR
                  (CryptoVerification.E2E.sessionSchemeFixedSpk
                    (CryptoVerification.E2E.paramsIdsWithSpqr C
                      (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                      d.idA d.idB) ℓ d.spkCoins)
                  (2 + 1) qep
                  (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT)
                  (.inl (.inr (P, wireWhisper :: r₁)))).run gs =
                (CryptoGames.SM.oracleImplR
                  (CryptoVerification.E2E.sessionSchemeFixedSpk
                    (CryptoVerification.E2E.paramsIdsWithSpqr C
                      (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                      d.idA d.idB) ℓ d.spkCoins)
                  (2 + 1) qep
                  (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT)
                  (.inl (.inr (P, wireWhisper :: r₂)))).run gs := by
              change
                (CryptoGames.SM.injectR
                  (CryptoVerification.E2E.sessionSchemeFixedSpk
                    (CryptoVerification.E2E.paramsIdsWithSpqr C
                      (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                      d.idA d.idB) ℓ d.spkCoins)
                  (2 + 1) qep
                  (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT)
                  (P, wireWhisper :: r₁)).run gs =
                (CryptoGames.SM.injectR
                  (CryptoVerification.E2E.sessionSchemeFixedSpk
                    (CryptoVerification.E2E.paramsIdsWithSpqr C
                      (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                      d.idA d.idB) ℓ d.spkCoins)
                  (2 + 1) qep
                  (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT)
                  (P, wireWhisper :: r₂)).run gs
              rw [CryptoVerification.E2E.BhAdapterIjHelpersV1.injectR_run,
                CryptoVerification.E2E.BhAdapterIjHelpersV1.injectR_run]
              have htr1 := inTransit_wireWhisper_isSome_eq_false hgsNW P.other r₁
              have htr2 := inTransit_wireWhisper_isSome_eq_false hgsNW P.other r₂
              have hok1 : (CryptoVerification.E2E.configRefuseEarlyBobCorr
                  (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK
                  (wireWhisper :: r₁) = true :=
                CryptoVerification.E2E.BhAdapterIjHelpersV1.ratchetKeyOnCurve_wireWhisper_cons
                  _ decT encT r₁
              have hok2 : (CryptoVerification.E2E.configRefuseEarlyBobCorr
                  (St := GhostState Bytes) (Msg := Plain ℓ) decT encT).injOK
                  (wireWhisper :: r₂) = true :=
                CryptoVerification.E2E.BhAdapterIjHelpersV1.ratchetKeyOnCurve_wireWhisper_cons
                  _ decT encT r₂
              rw [htr1, htr2, hok1, hok2]
              cases (gs.win || false || !gs.safeInj (2 + 1) || !true)
              · simp only [Bool.false_eq_true, ↓reduceIte]
                congr 1; funext rc
                dsimp only [CryptoVerification.E2E.BhAdapterIjHelpersV1.injectPost,
                  CryptoVerification.E2E.sessionSchemeFixedSpk]
                rw [CryptoVerification.E2E.BhAdapterIjHelpersV1.params_receive_wireWhisper_cons,
                  CryptoVerification.E2E.BhAdapterIjHelpersV1.params_receive_wireWhisper_cons]
              · rfl
            cases P
            · dsimp only
              rw [bhDecodePreKeyMsgE_wireWhisper_cons, bhDecodePreKeyMsgE_wireWhisper_cons]
              simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
              rw [hRunEq]
              congr 1
            · dsimp only
              by_cases hba : (!im.bobAccepted) = true
              · simp [hba]
              · simp only [hba, Bool.false_eq_true, ↓reduceIte]
                rw [bhDecodePreKeyMsgE_wireWhisper_cons, bhDecodePreKeyMsgE_wireWhisper_cons]
                dsimp only
                rw [hRunEq]
                congr 1

private theorem bhE2EStepLocalSm_ij_wrapWhisperWire_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} (hNoWhisp : DrvNoWhisperTrans σ)
    (i : ℕ) (P : Party) (y : Bytes) :
    CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i
        (.inl (.inr (P, E2EPureOp.eval ℓ .wrapWhisperWire y))) =
      CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i
        (.inl (.inr (P, bhShallowWrapWhisper y))) := by
  cases y with
  | nil => rfl
  | cons b bs =>
    simp only [E2EPureOp.eval, bhShallowWrapWhisper, List.isEmpty_cons,
      Bool.false_eq_true, ↓reduceIte]
    obtain ⟨m, hm⟩ : ∃ m, 32 * (2 * (ℓ / 32) + 26) = m + 1 :=
      ⟨32 * (2 * (ℓ / 32) + 26) - 1, by omega⟩
    rw [hm, List.take_succ_cons]
    exact bhE2EStepLocalSm_ij_wireWhisper_irrel C K qep decT encT hNoWhisp i P _ (b :: bs)

/-! ### Fresh-key and mirror invariants -/

private def initSidToSum? {S : SignalPqxdh.Setup} :
    SignalPqxdh.SessionId S →
      Option ((Fin S.N_id × Fin S.N_send_opk) ⊕ (Fin S.N_id × Fin S.N_send_no_opk))
  | .sendOPK u i => some (.inl (u, i))
  | .sendNoOPK u i => some (.inr (u, i))
  | .recvOPK .. => none
  | .recvNoOPK .. => none

private theorem initSidToSum?_inj {S : SignalPqxdh.Setup}
    {s₁ s₂ : SignalPqxdh.SessionId S}
    {y : (Fin S.N_id × Fin S.N_send_opk) ⊕ (Fin S.N_id × Fin S.N_send_no_opk)}
    (h₁ : initSidToSum? s₁ = some y) (h₂ : initSidToSum? s₂ = some y) :
    s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> simp [initSidToSum?] at h₁ h₂
  · rcases Sum.inl.inj (h₁.trans h₂.symm) with ⟨rfl, rfl⟩
    rfl
  · cases h₁.trans h₂.symm
  · cases h₁.trans h₂.symm
  · rcases Sum.inr.inj (h₁.trans h₂.symm) with ⟨rfl, rfl⟩
    rfl

/-- Monotonicity and freshness invariant on a `KeyInd` handler `ki` under which each principal,
SPK bundle, OPK entry, and initiator session ID is recorded at most once in `ModelDriverBase`. -/
structure KiFreshKeys (S : SignalPqxdh.Setup)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)) :
    Prop where
  mono : ∀ kq st kr st', (kr, st') ∈ support ((ki kq).run st) →
    st.principals.map Prod.fst ⊆ st'.principals.map Prod.fst ∧
    st.spkBundles.map Prod.fst ⊆ st'.spkBundles.map Prod.fst ∧
    st.opkEntries.map Prod.fst ⊆ st'.opkEntries.map Prod.fst ∧
    st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid ⊆
      st'.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid
  initPrin_fresh : ∀ u st ikPk sPk st',
    (.initPrinResp ikPk sPk, st') ∈ support ((ki (.initPrin u)).run st) →
    u.val ∉ st.principals.map Prod.fst ∧ u.val ∈ st'.principals.map Prod.fst
  genSPK_fresh : ∀ u j st bnd st',
    (.bundleResp bnd, st') ∈ support ((ki (.genSPK u j)).run st) →
    (u.val, j.val) ∉ st.spkBundles.map Prod.fst ∧ (u.val, j.val) ∈ st'.spkBundles.map Prod.fst
  genOPK_fresh : ∀ u j o st pk st',
    (.pkResp pk, st') ∈ support ((ki (.genOPK u j o)).run st) →
    (u.val, j.val, o.val) ∉ st.opkEntries.map Prod.fst ∧
      (u.val, j.val, o.val) ∈ st'.opkEntries.map Prod.fst
  initiateOPK_fresh : ∀ u i bnd st hdr st',
    (.hdrResp hdr, st') ∈ support ((ki (.initiateOPK u i bnd)).run st) →
    SignalPqxdh.SessionId.sendOPK u i ∉ st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid ∧
      SignalPqxdh.SessionId.sendOPK u i ∈ st'.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid
  initiateNoOPK_fresh : ∀ u i bnd st hdr st',
    (.hdrResp hdr, st') ∈ support ((ki (.initiateNoOPK u i bnd)).run st) →
    SignalPqxdh.SessionId.sendNoOPK u i ∉ st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid ∧
      SignalPqxdh.SessionId.sendNoOPK u i ∈ st'.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid

private theorem map_fst_preserve {α β γ : Type} (l : List (α × β)) (g : α × β → α × γ)
    (hg : ∀ x, (g x).1 = x.1) :
    (l.map g).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [hg x, ih]

private theorem map_sid_preserve {S : SignalPqxdh.Setup}
    (l : List (SignalPqxdh.KeyIndInitiatorEntry S))
    (g : SignalPqxdh.KeyIndInitiatorEntry S → SignalPqxdh.KeyIndInitiatorEntry S)
    (hg : ∀ s, (g s).sid = s.sid) :
    (l.map g).map SignalPqxdh.KeyIndInitiatorEntry.sid =
      l.map SignalPqxdh.KeyIndInitiatorEntry.sid := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [hg x, ih]

private theorem runKeyIndInitiate_props (useRo : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) (sid : SignalPqxdh.SessionId S)
    (u : Fin S.N_id) (bundle : SignalPqxdh.PreKeyBundleInput)
    (st st' : SignalPqxdh.KeyIndState S) (kr : SignalPqxdh.KeyIndResponse)
    (h : (kr, st') ∈ support ((SignalPqxdh.runKeyIndInitiate useRo S P sid u bundle).run st)) :
    (st.principals.map Prod.fst ⊆ st'.principals.map Prod.fst ∧
     st.spkBundles.map Prod.fst ⊆ st'.spkBundles.map Prod.fst ∧
     st.opkEntries.map Prod.fst ⊆ st'.opkEntries.map Prod.fst ∧
     st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid ⊆
       st'.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid) ∧
    (∀ hdr, kr = .hdrResp hdr →
      sid ∉ st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid ∧
        sid ∈ st'.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid) := by
  unfold SignalPqxdh.runKeyIndInitiate at h
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
  by_cases hdup : (st.sessions.any fun e => e.sid == sid) = true
  · simp only [hdup, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
    rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    exact ⟨⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩,
      fun _ hkr => nomatch hkr⟩
  · simp only [hdup, Bool.false_eq_true, ↓reduceIte] at h
    have hnotMem : sid ∉ st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid := by
      intro hmem
      rcases List.mem_map.mp hmem with ⟨e, he, rfl⟩
      exact hdup (List.any_eq_true.mpr ⟨e, he, beq_self_eq_true _⟩)
    cases hprin : st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [hprin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact ⟨⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩,
        fun _ hkr => nomatch hkr⟩
    | some uPair =>
      rcases uPair with ⟨_, uEntry⟩
      rw [hprin] at h; dsimp only at h
      by_cases hkosk : (!SignalPqxdh.koskBundleOk P st.principals st.spkBundles st.opkEntries
          st.advKeys bundle) = true
      · simp only [hkosk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨rfl, rfl⟩
        exact ⟨⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩,
          fun _ hkr => nomatch hkr⟩
      · simp only [hkosk, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, mem_support_bind_iff] at h
        rcases h with ⟨⟨ekASk, s1⟩, ⟨_, -, hp1⟩, ⟨kemCoins, s2⟩, ⟨_, -, hp2⟩, h⟩
        have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
        have hs2 : s2 = st := (Prod.mk.inj hp2).2; subst s2
        dsimp only at h
        by_cases hsig : (!(P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
            (SignalPqxdh.encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (SignalPqxdh.resolveSigPk P st.principals bundle.ikB)
              (SignalPqxdh.encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp only [hsig, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
          rcases Prod.mk.inj h with ⟨rfl, rfl⟩
          exact ⟨⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩,
            fun _ hkr => nomatch hkr⟩
        · simp only [hsig, Bool.false_eq_true, ↓reduceIte] at h
          cases hkem : P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            simp only [hkem, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
            rcases Prod.mk.inj h with ⟨rfl, rfl⟩
            exact ⟨⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩,
              fun _ hkr => nomatch hkr⟩
          | some ssCt =>
            rcases ssCt with ⟨ss, kemCt⟩
            rw [hkem] at h; dsimp only at h
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
              mem_support_bind_iff] at h
            rcases h with ⟨⟨⟨drKeyReal, roCache'⟩, s3⟩, ⟨_, -, hp3⟩, h⟩
            have hs3 : s3 = st := (Prod.mk.inj hp3).2; subst s3
            dsimp only at h
            have hst' :
                st'.principals = st.principals ∧
                st'.spkBundles = st.spkBundles ∧
                st'.opkEntries = st.opkEntries ∧
                st'.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid =
                  sid :: st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid := by
              cases hpart : SignalPqxdh.keyIndPartnerRandKey? P st.respSessions _ with
              | some drKeyRand =>
                rw [hpart] at h; dsimp only at h
                simp only [StateT.run_bind, StateT.run_set, pure_bind] at h
                cases hfp : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB <;>
                  rw [hfp] at h <;> dsimp only at h <;>
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h <;>
                  rcases Prod.mk.inj h with ⟨_, rfl⟩ <;>
                  exact ⟨rfl, rfl, rfl, rfl⟩
              | none =>
                rw [hpart] at h; dsimp only at h
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  pure_bind, mem_support_bind_iff] at h
                rcases h with ⟨⟨drKeyRand, s4⟩, ⟨_, -, hp4⟩, h⟩
                have hs4 : s4 = st := (Prod.mk.inj hp4).2; subst s4
                dsimp only at h
                cases hfp : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB <;>
                  rw [hfp] at h <;> dsimp only at h <;>
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h <;>
                  rcases Prod.mk.inj h with ⟨_, rfl⟩ <;>
                  exact ⟨rfl, rfl, rfl, rfl⟩
            rcases hst' with ⟨hP, hB, hO, hS⟩
            refine ⟨⟨by rw [hP], by rw [hB], by rw [hO], ?_⟩, fun _ _ => ⟨hnotMem, ?_⟩⟩
            · rw [hS]; exact List.subset_cons_self _ _
            · rw [hS]; exact List.mem_cons_self

theorem kiFreshKeys_pqxdhKeyIndImpl (useRo : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) :
    KiFreshKeys S (SignalPqxdh.pqxdhKeyIndImpl useRo S P) where
  mono := by
    intro kq st kr st' h
    have hrefl :
        st.principals.map Prod.fst ⊆ st.principals.map Prod.fst ∧
        st.spkBundles.map Prod.fst ⊆ st.spkBundles.map Prod.fst ∧
        st.opkEntries.map Prod.fst ⊆ st.opkEntries.map Prod.fst ∧
        st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid ⊆
          st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid :=
      ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩
    rcases kq with u | u | ⟨u, j⟩ | ⟨u, j, o⟩ | ⟨u, i, bnd⟩ | ⟨u, i, bnd⟩ |
        ⟨k, j, o, hdr⟩ | ⟨k, j, l, hdr⟩ | sid | secrets | _ | sid | sk | ⟨u, j⟩
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases hdup : (st.principals.any fun (idx, _) => idx == u.val) = true
      · simp only [hdup, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [hdup, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨⟨_, s1⟩, ⟨_, -, hp1⟩, ⟨_, s2⟩, ⟨_, -, hp2⟩, h⟩
        have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
        have hs2 : s2 = st := (Prod.mk.inj hp2).2; subst s2
        rcases Prod.mk.inj h with ⟨_, rfl⟩
        exact ⟨List.subset_cons_self _ _, List.Subset.refl _, List.Subset.refl _,
          List.Subset.refl _⟩
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      cases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hfind] at h; dsimp only at h
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      | some pe =>
        rcases pe with ⟨_, entry⟩
        rw [hfind] at h; dsimp only at h
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩
        refine ⟨?_, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩
        dsimp only
        rw [map_fst_preserve st.principals _ (fun ⟨_, _⟩ => by dsimp only; split_ifs <;> rfl)]
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases hdup : (st.spkBundles.any fun (k, _) => k == (u.val, j.val)) = true
      · simp only [hdup, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [hdup, Bool.false_eq_true, ↓reduceIte] at h
        cases hp : st.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
          rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
        | some ue =>
          rcases ue with ⟨_, _⟩
          rw [hp] at h; dsimp only at h
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, pure_bind, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at h
          rcases h with ⟨⟨_, s1⟩, ⟨_, -, hp1⟩, ⟨_, s2⟩, ⟨_, -, hp2⟩,
            ⟨⟨_, _⟩, s3⟩, ⟨_, -, hp3⟩, ⟨_, s4⟩, ⟨_, -, hp4⟩, h⟩
          have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
          have hs2 : s2 = st := (Prod.mk.inj hp2).2; subst s2
          have hs3 : s3 = st := (Prod.mk.inj hp3).2; subst s3
          have hs4 : s4 = st := (Prod.mk.inj hp4).2; subst s4
          rcases Prod.mk.inj h with ⟨_, rfl⟩
          exact ⟨List.Subset.refl _, List.subset_cons_self _ _, List.Subset.refl _,
            List.Subset.refl _⟩
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases hdup : (st.opkEntries.any fun (k, _) => k == (u.val, j.val, o.val)) = true
      · simp only [hdup, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [hdup, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨⟨_, s1⟩, ⟨_, -, hp1⟩, h⟩
        have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
        rcases Prod.mk.inj h with ⟨_, rfl⟩
        exact ⟨List.Subset.refl _, List.Subset.refl _, List.subset_cons_self _ _,
          List.Subset.refl _⟩
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases hopk : bnd.opkB?.isNone = true
      · simp only [hopk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [hopk, Bool.false_eq_true, ↓reduceIte] at h
        exact (runKeyIndInitiate_props useRo S P (.sendOPK u i) u bnd st st' kr h).1
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases hopk : bnd.opkB?.isSome = true
      · simp only [hopk, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [hopk, Bool.false_eq_true, ↓reduceIte] at h
        exact (runKeyIndInitiate_props useRo S P (.sendNoOPK u i) u bnd st st' kr h).1
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases cg1 : (!(hdr.spkId == UInt32.ofNat j.val &&
          hdr.pqspkId == UInt32.ofNat j.val &&
          hdr.opkId? == some (UInt32.ofNat o.val) &&
          hdr.ikAPk.length == 32 &&
          hdr.ekAPk.length == 32)) = true
      · simp only [cg1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [cg1, Bool.false_eq_true, ↓reduceIte] at h
        by_cases cg2 : st.usedRecvOPK.contains (k.val, j.val, o.val) = true
        · simp only [cg2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
          rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
        · simp only [cg2, Bool.false_eq_true, ↓reduceIte] at h
          by_cases cg3 : (!SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
          · simp only [cg3, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
            rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
          · simp only [cg3, Bool.false_eq_true, ↓reduceIte] at h
            cases hp1 : st.principals.find? (fun (idx, _) => idx == k.val) with
            | none =>
              simp only [hp1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
              rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
            | some ke =>
              rcases ke with ⟨_, kEntry⟩
              rw [hp1] at h; dsimp only at h
              cases hp2 : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
              | none =>
                simp only [hp2, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
                rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
              | some be =>
                rcases be with ⟨_, bEntry⟩
                rw [hp2] at h; dsimp only at h
                cases hp3 : st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
                | none =>
                  simp only [hp3, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
                  rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
                | some oe =>
                  rcases oe with ⟨_, oEntry⟩
                  rw [hp3] at h; dsimp only at h
                  by_cases hcons : oEntry.consumed = true
                  · simp only [hcons, ↓reduceIte, StateT.run_pure, support_pure,
                      Set.mem_singleton_iff] at h
                    rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
                  · simp only [hcons, Bool.false_eq_true, ↓reduceIte] at h
                    cases hm1 : SignalPqxdh.Model.acceptKeys P _ with
                    | none =>
                      rw [hm1] at h; dsimp only at h
                      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
                      rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
                    | some u0 =>
                      rw [hm1] at h; dsimp only at h
                      cases hm2 : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                      | none =>
                        rw [hm2] at h; dsimp only at h
                        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
                        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
                      | some ss =>
                        rw [hm2] at h; dsimp only at h
                        unfold SignalPqxdh.recordKeyIndResp at h
                        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                          StateT.run_get, StateT.run_set, pure_bind, mem_support_bind_iff] at h
                        rcases h with ⟨⟨⟨drKey, roCache'⟩, s1⟩, ⟨_, -, hp4⟩, ⟨_, s2⟩, hdr0, h⟩
                        have hs1 : s1 = st := (Prod.mk.inj hp4).2; subst s1
                        dsimp only at hdr0 h
                        have hs2 :
                            s2.principals = st.principals ∧
                            s2.spkBundles = st.spkBundles ∧
                            s2.opkEntries.map Prod.fst = st.opkEntries.map Prod.fst ∧
                            s2.sessions = st.sessions := by
                          have hopk :
                              (st.opkEntries.map fun (idx, e) =>
                                if idx == (k.val, j.val, o.val) then
                                  (idx, { e with consumed := true })
                                else (idx, e)).map Prod.fst = st.opkEntries.map Prod.fst :=
                            map_fst_preserve st.opkEntries _
                              (fun ⟨_, _⟩ => by dsimp only; split_ifs <;> rfl)
                          cases hpart : (st.sessions.find? fun s => SignalPqxdh.keyIndPartner P s _) with
                          | some s0 =>
                            rw [hpart] at hdr0; dsimp only at hdr0
                            simp only [StateT.run_set, support_pure, Set.mem_singleton_iff] at hdr0
                            rcases Prod.mk.inj hdr0 with ⟨_, rfl⟩
                            exact ⟨rfl, rfl, hopk, rfl⟩
                          | none =>
                            rw [hpart] at hdr0; dsimp only at hdr0
                            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                              StateT.run_set, mem_support_bind_iff,
                              support_pure, Set.mem_singleton_iff] at hdr0
                            rcases hdr0 with ⟨⟨_, _⟩, ⟨_, -, _⟩, hp5⟩
                            rcases Prod.mk.inj hp5 with ⟨_, rfl⟩
                            exact ⟨rfl, rfl, hopk, rfl⟩
                        have hst' :
                            st'.principals = s2.principals ∧ st'.spkBundles = s2.spkBundles ∧
                            st'.opkEntries = s2.opkEntries ∧ st'.sessions = s2.sessions := by
                          cases hfp : SignalPqxdh.findHonestPrincipal P st.principals hdr.ikAPk <;>
                            rw [hfp] at h <;> dsimp only at h <;>
                            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h <;>
                            rcases Prod.mk.inj h with ⟨_, rfl⟩ <;>
                            exact ⟨rfl, rfl, rfl, rfl⟩
                        rw [hst'.1, hs2.1, hst'.2.1, hs2.2.1, hst'.2.2.1, hs2.2.2.1, hst'.2.2.2,
                          hs2.2.2.2]
                        exact hrefl
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases cg1 : (!(hdr.spkId == UInt32.ofNat j.val &&
          hdr.pqspkId == UInt32.ofNat j.val &&
          hdr.opkId? == none &&
          hdr.ikAPk.length == 32 &&
          hdr.ekAPk.length == 32)) = true
      · simp only [cg1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [cg1, Bool.false_eq_true, ↓reduceIte] at h
        by_cases cg2 : st.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
        · simp only [cg2, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
          rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
        · simp only [cg2, Bool.false_eq_true, ↓reduceIte] at h
          by_cases cg3 : (!SignalPqxdh.koskSenderOk P st.principals st.advKeys hdr.ikAPk) = true
          · simp only [cg3, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
            rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
          · simp only [cg3, Bool.false_eq_true, ↓reduceIte] at h
            cases hp1 : st.principals.find? (fun (idx, _) => idx == k.val) with
            | none =>
              simp only [hp1, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
              rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
            | some ke =>
              rcases ke with ⟨_, kEntry⟩
              rw [hp1] at h; dsimp only at h
              cases hp2 : st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
              | none =>
                simp only [hp2, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
                rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
              | some be =>
                rcases be with ⟨_, bEntry⟩
                rw [hp2] at h; dsimp only at h
                cases hm1 : SignalPqxdh.Model.acceptKeys P _ with
                | none =>
                  rw [hm1] at h; dsimp only at h
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
                  rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
                | some u0 =>
                  rw [hm1] at h; dsimp only at h
                  cases hm2 : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                  | none =>
                    rw [hm2] at h; dsimp only at h
                    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
                    rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
                  | some ss =>
                    rw [hm2] at h; dsimp only at h
                    unfold SignalPqxdh.recordKeyIndResp at h
                    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                      StateT.run_get, StateT.run_set, pure_bind, mem_support_bind_iff] at h
                    rcases h with ⟨⟨⟨drKey, roCache'⟩, s1⟩, ⟨_, -, hp4⟩, ⟨_, s2⟩, hdr0, h⟩
                    have hs1 : s1 = st := (Prod.mk.inj hp4).2; subst s1
                    dsimp only at hdr0 h
                    have hs2 :
                        s2.principals = st.principals ∧
                        s2.spkBundles = st.spkBundles ∧
                        s2.opkEntries = st.opkEntries ∧
                        s2.sessions = st.sessions := by
                      cases hpart : (st.sessions.find? fun s => SignalPqxdh.keyIndPartner P s _) with
                      | some s0 =>
                        rw [hpart] at hdr0; dsimp only at hdr0
                        simp only [StateT.run_set, support_pure, Set.mem_singleton_iff] at hdr0
                        rcases Prod.mk.inj hdr0 with ⟨_, rfl⟩
                        exact ⟨rfl, rfl, rfl, rfl⟩
                      | none =>
                        rw [hpart] at hdr0; dsimp only at hdr0
                        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                          StateT.run_set, mem_support_bind_iff,
                          support_pure, Set.mem_singleton_iff] at hdr0
                        rcases hdr0 with ⟨⟨_, _⟩, ⟨_, -, _⟩, hp5⟩
                        rcases Prod.mk.inj hp5 with ⟨_, rfl⟩
                        exact ⟨rfl, rfl, rfl, rfl⟩
                    have hst' :
                        st'.principals = s2.principals ∧ st'.spkBundles = s2.spkBundles ∧
                        st'.opkEntries = s2.opkEntries ∧ st'.sessions = s2.sessions := by
                      cases hfp : SignalPqxdh.findHonestPrincipal P st.principals hdr.ikAPk <;>
                        rw [hfp] at h <;> dsimp only at h <;>
                        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h <;>
                        rcases Prod.mk.inj h with ⟨_, rfl⟩ <;>
                        exact ⟨rfl, rfl, rfl, rfl⟩
                    rw [hst'.1, hs2.1, hst'.2.1, hs2.2.1, hst'.2.2.1, hs2.2.2.1, hst'.2.2.2,
                      hs2.2.2.2]
                    exact hrefl
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases htest : (!SignalPqxdh.isKeyIndSessionTestable st sid) = true
      · simp only [htest, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [htest, Bool.false_eq_true, ↓reduceIte] at h
        cases hsess : st.sessions.find? (fun e => e.sid == sid) with
        | some e =>
          rw [hsess] at h; dsimp only at h
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at h
          rcases Prod.mk.inj h with ⟨_, rfl⟩
          refine ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, ?_⟩
          dsimp only
          rw [map_sid_preserve st.sessions _ (fun _ => by split_ifs <;> rfl)]
        | none =>
          rw [hsess] at h; dsimp only at h
          cases hresp : st.respSessions.find? (fun r => r.sid == sid) with
          | none =>
            rw [hresp] at h; dsimp only at h
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
            rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
          | some r =>
            rw [hresp] at h; dsimp only at h
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at h
            rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases hro : (!useRo) = true
      · simp only [hro, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [hro, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨⟨⟨_, _⟩, s1⟩, ⟨_, -, hp1⟩, h⟩
        have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases hro : useRo = true
      · simp only [hro, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      · simp only [hro, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      cases hsess : st.sessions.find? (fun e => e.sid == sid) with
      | some e =>
        rw [hsess] at h; dsimp only at h
        by_cases htest : e.tested = true
        · simp only [htest, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
          rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
        · simp only [htest, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at h
          rcases Prod.mk.inj h with ⟨_, rfl⟩
          refine ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, ?_⟩
          dsimp only
          rw [map_sid_preserve st.sessions _ (fun _ => by split_ifs <;> rfl)]
      | none =>
        rw [hsess] at h; dsimp only at h
        cases hresp : st.respSessions.find? (fun r => r.sid == sid) with
        | none =>
          rw [hresp] at h; dsimp only at h
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
          rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
        | some r =>
          rw [hresp] at h; dsimp only at h
          by_cases htest : r.tested = true
          · simp only [htest, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
            rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
          · simp only [htest, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at h
            rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      cases hreg : SignalPqxdh.registerAdvKey P st.advKeys sk with
      | none =>
        rw [hreg] at h; dsimp only at h
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      | some pa =>
        rcases pa with ⟨_, _⟩
        rw [hreg] at h; dsimp only at h
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      cases hspk : st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
      | none =>
        rw [hspk] at h; dsimp only at h
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩; exact hrefl
      | some be =>
        rcases be with ⟨_, bEntry⟩
        rw [hspk] at h; dsimp only at h
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩
        refine ⟨List.Subset.refl _, ?_, List.Subset.refl _, List.Subset.refl _⟩
        dsimp only
        rw [map_fst_preserve st.spkBundles _ (fun ⟨_, _⟩ => by dsimp only; split_ifs <;> rfl)]
  initPrin_fresh := by
    intro u st ikPk sPk st' h
    unfold SignalPqxdh.pqxdhKeyIndImpl at h
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
    by_cases hdup : (st.principals.any fun (idx, _) => idx == u.val) = true
    · simp [hdup, StateT.run_pure] at h
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at h
      rcases h with ⟨⟨_, s1⟩, ⟨_, -, hp1⟩, ⟨_, s2⟩, ⟨_, -, hp2⟩, h⟩
      have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
      have hs2 : s2 = st := (Prod.mk.inj hp2).2; subst s2
      rcases Prod.mk.inj h with ⟨_, rfl⟩
      refine ⟨?_, List.mem_cons_self⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨⟨idx, e⟩, he, hidx⟩
      dsimp only at hidx; subst idx
      exact hdup (List.any_eq_true.mpr ⟨(u.val, e), he, beq_self_eq_true _⟩)
  genSPK_fresh := by
    intro u j st bnd st' h
    unfold SignalPqxdh.pqxdhKeyIndImpl at h
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
    by_cases hdup : (st.spkBundles.any fun (k, _) => k == (u.val, j.val)) = true
    · simp [hdup, StateT.run_pure] at h
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte] at h
      cases hp : st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [hp, StateT.run_pure] at h
      | some ue =>
        rcases ue with ⟨_, _⟩
        rw [hp] at h; dsimp only at h
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at h
        rcases h with ⟨⟨_, s1⟩, ⟨_, -, hp1⟩, ⟨_, s2⟩, ⟨_, -, hp2⟩,
          ⟨⟨_, _⟩, s3⟩, ⟨_, -, hp3⟩, ⟨_, s4⟩, ⟨_, -, hp4⟩, h⟩
        have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
        have hs2 : s2 = st := (Prod.mk.inj hp2).2; subst s2
        have hs3 : s3 = st := (Prod.mk.inj hp3).2; subst s3
        have hs4 : s4 = st := (Prod.mk.inj hp4).2; subst s4
        rcases Prod.mk.inj h with ⟨_, rfl⟩
        refine ⟨?_, List.mem_cons_self⟩
        intro hmem
        rcases List.mem_map.mp hmem with ⟨⟨k, b⟩, hb, hk⟩
        dsimp only at hk; subst k
        exact hdup (List.any_eq_true.mpr ⟨((u.val, j.val), b), hb, beq_self_eq_true _⟩)
  genOPK_fresh := by
    intro u j o st pk st' h
    unfold SignalPqxdh.pqxdhKeyIndImpl at h
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
    by_cases hdup : (st.opkEntries.any fun (k, _) => k == (u.val, j.val, o.val)) = true
    · simp [hdup, StateT.run_pure] at h
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at h
      rcases h with ⟨⟨_, s1⟩, ⟨_, -, hp1⟩, h⟩
      have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
      rcases Prod.mk.inj h with ⟨_, rfl⟩
      refine ⟨?_, List.mem_cons_self⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨⟨k, e⟩, he, hk⟩
      dsimp only at hk; subst k
      exact hdup (List.any_eq_true.mpr ⟨((u.val, j.val, o.val), e), he, beq_self_eq_true _⟩)
  initiateOPK_fresh := by
    intro u i bnd st hdr st' h
    unfold SignalPqxdh.pqxdhKeyIndImpl at h
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
    by_cases hopk : bnd.opkB?.isNone = true
    · simp [hopk, StateT.run_pure] at h
    · simp only [hopk, Bool.false_eq_true, ↓reduceIte] at h
      exact (runKeyIndInitiate_props useRo S P (.sendOPK u i) u bnd st st' _ h).2 hdr rfl
  initiateNoOPK_fresh := by
    intro u i bnd st hdr st' h
    unfold SignalPqxdh.pqxdhKeyIndImpl at h
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
    by_cases hopk : bnd.opkB?.isSome = true
    · simp [hopk, StateT.run_pure] at h
    · simp only [hopk, Bool.false_eq_true, ↓reduceIte] at h
      exact (runKeyIndInitiate_props useRo S P (.sendNoOPK u i) u bnd st st' _ h).2 hdr rfl

theorem kiFreshKeys_pqxdhKeyIndImpl1KeyReal (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) :
    KiFreshKeys S (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) := by
  have hBase := kiFreshKeys_pqxdhKeyIndImpl false S P
  refine ⟨?_, ?_, hBase.genSPK_fresh, hBase.genOPK_fresh,
    hBase.initiateOPK_fresh, hBase.initiateNoOPK_fresh⟩
  · intro kq st kr st' h
    rcases kq with u | u | ⟨u, j⟩ | ⟨u, j, o⟩ | ⟨u, i, bnd⟩ | ⟨u, i, bnd⟩ |
        ⟨k, j, o, hdr⟩ | ⟨k, j, l, hdr⟩ | sid | secrets | _ | sid | sk | ⟨u, j⟩
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal at h
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
      by_cases hdup : (st.principals.any fun (idx, _) => idx == u.val) = true
      · simp only [hdup, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
        rcases Prod.mk.inj h with ⟨_, rfl⟩
        exact ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩
      · simp only [hdup, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨⟨_, s1⟩, ⟨_, -, hp1⟩, h⟩
        have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
        rcases Prod.mk.inj h with ⟨_, rfl⟩
        exact ⟨List.subset_cons_self _ _, List.Subset.refl _, List.Subset.refl _,
          List.Subset.refl _⟩
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal at h
      simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at h
      rcases h with ⟨⟨⟨_, _⟩, s1⟩, ⟨_, -, hp1⟩, h⟩
      have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
      rcases Prod.mk.inj h with ⟨_, rfl⟩
      exact ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩
    ·
      unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal at h
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
      rcases Prod.mk.inj h with ⟨_, rfl⟩
      exact ⟨List.Subset.refl _, List.Subset.refl _, List.Subset.refl _, List.Subset.refl _⟩
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
    · exact hBase.mono _ st kr st' h
  · intro u st ikPk sPk st' h
    unfold SignalPqxdh.pqxdhKeyIndImpl1KeyReal at h
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
    by_cases hdup : (st.principals.any fun (idx, _) => idx == u.val) = true
    · simp [hdup, StateT.run_pure] at h
    · simp only [hdup, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, pure_bind, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at h
      rcases h with ⟨⟨_, s1⟩, ⟨_, -, hp1⟩, h⟩
      have hs1 : s1 = st := (Prod.mk.inj hp1).2; subst s1
      rcases Prod.mk.inj h with ⟨_, rfl⟩
      refine ⟨?_, List.mem_cons_self⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨⟨idx, e⟩, he, hidx⟩
      dsimp only at hidx; subst idx
      exact hdup (List.any_eq_true.mpr ⟨(u.val, e), he, beq_self_eq_true _⟩)

theorem kiFreshKeys_pqxdhKeyIndImpl1KeyRo (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives) :
    KiFreshKeys S (SignalPqxdh.pqxdhKeyIndImpl1KeyRo S P) := by
  have hReal := kiFreshKeys_pqxdhKeyIndImpl1KeyReal S P
  have hBase := kiFreshKeys_pqxdhKeyIndImpl true S P
  refine ⟨?_, hReal.initPrin_fresh, hBase.genSPK_fresh, hBase.genOPK_fresh,
    hBase.initiateOPK_fresh, hBase.initiateNoOPK_fresh⟩
  intro kq st kr st' h
  cases kq
  · exact hReal.mono _ st kr st' h
  all_goals exact hBase.mono _ st kr st' h

private structure MirrorKiInv {S : SignalPqxdh.Setup} (d : ModelDriverBase S)
    (st : SignalPqxdh.KeyIndState S) : Prop where
  prins_nodup : (d.prins.map Prod.fst).Nodup
  prins_sub : ∀ u ∈ d.prins.map Prod.fst, u.val ∈ st.principals.map Prod.fst
  bundles_nodup : (d.bundles.map Prod.fst).Nodup
  bundles_sub : ∀ x ∈ d.bundles.map Prod.fst,
    (x.1.val, x.2.val) ∈ st.spkBundles.map Prod.fst
  opks_nodup : (d.opks.map Prod.fst).Nodup
  opks_sub : ∀ x ∈ d.opks.map Prod.fst,
    (x.1.val, x.2.1.val, x.2.2.val) ∈ st.opkEntries.map Prod.fst
  sends_nodup : (d.sends.filterMap (fun x => initSidToSum? x.1)).Nodup
  sends_sub : ∀ x ∈ d.sends,
    (initSidToSum? x.1).isSome = true ∧
      x.1 ∈ st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid

private theorem mirrorKiInv_empty {S : SignalPqxdh.Setup} (st : SignalPqxdh.KeyIndState S) :
    MirrorKiInv ({} : ModelDriverBase S) st where
  prins_nodup := List.nodup_nil
  prins_sub := fun _ h => nomatch h
  bundles_nodup := List.nodup_nil
  bundles_sub := fun _ h => nomatch h
  opks_nodup := List.nodup_nil
  opks_sub := fun _ h => nomatch h
  sends_nodup := List.nodup_nil
  sends_sub := fun _ h => nomatch h

private theorem mirrorKiInv_mono {S : SignalPqxdh.Setup} {d : ModelDriverBase S}
    {st st' : SignalPqxdh.KeyIndState S} (h : MirrorKiInv d st)
    (hm : st.principals.map Prod.fst ⊆ st'.principals.map Prod.fst ∧
      st.spkBundles.map Prod.fst ⊆ st'.spkBundles.map Prod.fst ∧
      st.opkEntries.map Prod.fst ⊆ st'.opkEntries.map Prod.fst ∧
      st.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid ⊆
        st'.sessions.map SignalPqxdh.KeyIndInitiatorEntry.sid) :
    MirrorKiInv d st' where
  prins_nodup := h.prins_nodup
  prins_sub := fun u hu => hm.1 (h.prins_sub u hu)
  bundles_nodup := h.bundles_nodup
  bundles_sub := fun x hx => hm.2.1 (h.bundles_sub x hx)
  opks_nodup := h.opks_nodup
  opks_sub := fun x hx => hm.2.2.1 (h.opks_sub x hx)
  sends_nodup := h.sends_nodup
  sends_sub := fun x hx => ⟨(h.sends_sub x hx).1, hm.2.2.2 (h.sends_sub x hx).2⟩

private theorem mirrorKiInv_bhBaseMirror {S : SignalPqxdh.Setup}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki) {d : ModelDriverBase S} {st st' : SignalPqxdh.KeyIndState S}
    (hInv : MirrorKiInv d st)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (hStep : (kr, st') ∈ support ((ki kq).run st)) :
    MirrorKiInv (bhBaseMirror d kq kr) st' := by
  have hMono := mirrorKiInv_mono hInv (hKi.mono kq st kr st' hStep)
  rcases kq with u | u | ⟨u, j⟩ | ⟨u, j, o⟩ | ⟨u, i, bnd⟩ | ⟨u, i, bnd⟩ |
      ⟨k, j, o, hdr⟩ | ⟨k, j, l, hdr⟩ | sid | secrets | _ | sid | sk | ⟨u, j⟩
  · cases kr with
    | initPrinResp ikPk sPk =>
      obtain ⟨hNot, hIn⟩ := hKi.initPrin_fresh u st ikPk sPk st' hStep
      refine ⟨List.nodup_cons.mpr ⟨fun hu => hNot (hInv.prins_sub u hu), hInv.prins_nodup⟩,
        ?_, hMono.bundles_nodup, hMono.bundles_sub, hMono.opks_nodup, hMono.opks_sub,
        hMono.sends_nodup, hMono.sends_sub⟩
      intro u' hu'
      rcases List.mem_cons.mp hu' with rfl | hmem
      · exact hIn
      · exact hMono.prins_sub u' hmem
    | _ => exact hMono
  · exact hMono
  · cases kr with
    | bundleResp bnd =>
      obtain ⟨hNot, hIn⟩ := hKi.genSPK_fresh u j st bnd st' hStep
      refine ⟨hMono.prins_nodup, hMono.prins_sub,
        List.nodup_cons.mpr ⟨fun hx => hNot (hInv.bundles_sub (u, j) hx), hInv.bundles_nodup⟩,
        ?_, hMono.opks_nodup, hMono.opks_sub, hMono.sends_nodup, hMono.sends_sub⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hIn
      · exact hMono.bundles_sub x hmem
    | _ => exact hMono
  · cases kr with
    | pkResp pk =>
      obtain ⟨hNot, hIn⟩ := hKi.genOPK_fresh u j o st pk st' hStep
      refine ⟨hMono.prins_nodup, hMono.prins_sub, hMono.bundles_nodup, hMono.bundles_sub,
        List.nodup_cons.mpr ⟨fun hx => hNot (hInv.opks_sub (u, j, o) hx), hInv.opks_nodup⟩,
        ?_, hMono.sends_nodup, hMono.sends_sub⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hIn
      · exact hMono.opks_sub x hmem
    | _ => exact hMono
  · cases kr with
    | hdrResp hdr =>
      obtain ⟨hNot, hIn⟩ := hKi.initiateOPK_fresh u i bnd st hdr st' hStep
      refine ⟨hMono.prins_nodup, hMono.prins_sub, hMono.bundles_nodup, hMono.bundles_sub,
        hMono.opks_nodup, hMono.opks_sub, ?_, ?_⟩
      · dsimp only [bhBaseMirror, List.filterMap_cons, initSidToSum?]
        refine List.nodup_cons.mpr ⟨?_, hInv.sends_nodup⟩
        intro hmem
        rcases List.mem_filterMap.mp hmem with ⟨x, hx, hsum⟩
        have hsid := initSidToSum?_inj hsum (rfl : initSidToSum? (.sendOPK u i) = some (.inl (u, i)))
        exact hNot (hsid ▸ (hInv.sends_sub x hx).2)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨rfl, hIn⟩
        · exact hMono.sends_sub x hmem
    | _ => exact hMono
  · cases kr with
    | hdrResp hdr =>
      obtain ⟨hNot, hIn⟩ := hKi.initiateNoOPK_fresh u i bnd st hdr st' hStep
      refine ⟨hMono.prins_nodup, hMono.prins_sub, hMono.bundles_nodup, hMono.bundles_sub,
        hMono.opks_nodup, hMono.opks_sub, ?_, ?_⟩
      · dsimp only [bhBaseMirror, List.filterMap_cons, initSidToSum?]
        refine List.nodup_cons.mpr ⟨?_, hInv.sends_nodup⟩
        intro hmem
        rcases List.mem_filterMap.mp hmem with ⟨x, hx, hsum⟩
        have hsid := initSidToSum?_inj hsum (rfl : initSidToSum? (.sendNoOPK u i) = some (.inr (u, i)))
        exact hNot (hsid ▸ (hInv.sends_sub x hx).2)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨rfl, hIn⟩
        · exact hMono.sends_sub x hmem
    | _ => exact hMono
  all_goals exact hMono

private theorem nodup_length_le_card {α : Type} [DecidableEq α] [Fintype α]
    {l : List α} (h : l.Nodup) : l.length ≤ Fintype.card α := by
  have h1 : l.toFinset.card = l.length := List.toFinset_card_of_nodup h
  rw [← h1]
  exact Finset.card_le_univ l.toFinset

private theorem length_filterMap_of_all_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | a :: as, hall => by
    have ha := hall a List.mem_cons_self
    cases hf : f a with
    | none => rw [hf] at ha; cases ha
    | some b =>
      simp only [List.filterMap_cons, hf, List.length_cons]
      exact congrArg Nat.succ
        (length_filterMap_of_all_isSome f as (fun x hx => hall x (List.mem_cons_of_mem a hx)))

private theorem MirrorKiInv.prins_length_le {S : SignalPqxdh.Setup} {d : ModelDriverBase S}
    {st : SignalPqxdh.KeyIndState S} (h : MirrorKiInv d st) :
    d.prins.length ≤ S.N_id := by
  have hlen := nodup_length_le_card h.prins_nodup
  simpa using hlen

private theorem MirrorKiInv.bundles_length_le {S : SignalPqxdh.Setup} {d : ModelDriverBase S}
    {st : SignalPqxdh.KeyIndState S} (h : MirrorKiInv d st) :
    d.bundles.length ≤ S.N_spk_tot := by
  have hlen := nodup_length_le_card h.bundles_nodup
  simpa [SignalPqxdh.Setup.N_spk_tot] using hlen

private theorem MirrorKiInv.opks_length_le {S : SignalPqxdh.Setup} {d : ModelDriverBase S}
    {st : SignalPqxdh.KeyIndState S} (h : MirrorKiInv d st) :
    d.opks.length ≤ S.N_opk_tot := by
  have hlen := nodup_length_le_card h.opks_nodup
  simpa [SignalPqxdh.Setup.N_opk_tot, SignalPqxdh.Setup.N_spk_tot, Nat.mul_assoc] using hlen

private theorem MirrorKiInv.sends_length_le {S : SignalPqxdh.Setup} {d : ModelDriverBase S}
    {st : SignalPqxdh.KeyIndState S} (h : MirrorKiInv d st) :
    d.sends.length ≤ S.N_send_tot := by
  have hlen := nodup_length_le_card h.sends_nodup
  rw [length_filterMap_of_all_isSome _ d.sends (fun x hx => (h.sends_sub x hx).1)] at hlen
  simpa [SignalPqxdh.Setup.N_send_tot, SignalPqxdh.Setup.N_send_opk_tot,
    SignalPqxdh.Setup.N_send_no_opk_tot] using hlen

/-! ### Coupled step simulation -/

private theorem bhE2EStepLocalSm_base_st_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {out : CryptoVerification.E2E.BHE2ESmResp ℓ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT σ i sq)) :
    out.2.toModelDriverBase = σ.toModelDriverBase ∧ out.2.st = σ.st := by
  unfold CryptoVerification.E2E.bhE2EStepLocalSm at hout
  by_cases hcl : !CryptoVerification.E2E.bhE2EDrvInstClean σ i
  · simp only [hcl, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
    subst hout; exact ⟨rfl, rfl⟩
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hout
    cases hd : σ.insts[i]? with
    | none =>
      simp only [hd, support_pure, Set.mem_singleton_iff] at hout
      subst hout; exact ⟨rfl, rfl⟩
    | some d =>
      cases him : σ.instMeta[i]? with
      | none =>
        simp only [hd, him, support_pure, Set.mem_singleton_iff] at hout
        subst hout; exact ⟨rfl, rfl⟩
      | some im =>
        simp only [hd, him] at hout
        by_cases hcorr : !im.bobAccepted && CryptoVerification.E2E.bhIsBobRecvSMQuery sq &&
            CryptoVerification.E2E.bhE2EInstIkACorr σ d
        · simp only [hcorr, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hout
          subst hout; exact ⟨rfl, rfl⟩
        · simp only [hcorr, Bool.false_eq_true, ↓reduceIte] at hout
          cases hgs : d.gs with
          | none =>
            simp only [hgs, support_pure, Set.mem_singleton_iff] at hout
            subst hout; exact ⟨rfl, rfl⟩
          | some gs =>
            simp only [hgs] at hout
            have hrunStd :
                ∀ (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ)
                    (BitVec 512) Bytes).Domain),
                out ∈ support (do
                  let (r, gs') ← (CryptoGames.SM.oracleImplR
                    (CryptoVerification.E2E.sessionSchemeFixedSpk
                      (CryptoVerification.E2E.paramsIdsWithSpqr C
                        (CryptoVerification.LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K)
                        d.idA d.idB)
                      ℓ d.spkCoins) (2 + 1) qep
                    (CryptoVerification.E2E.configRefuseEarlyBobCorr decT encT) q').run gs
                  let accepted := CryptoVerification.E2E.bhIsBobAcceptSMResp q' r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true,
                                ikACorrAtAccept := CryptoVerification.E2E.bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  pure (CryptoVerification.E2E.bhPackSmResp q' r, σ1)) →
                out.2.toModelDriverBase = σ.toModelDriverBase ∧ out.2.st = σ.st := by
              intro q' hrun
              simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrun
              rcases hrun with ⟨⟨_, _⟩, -, rfl⟩
              exact ⟨rfl, rfl⟩
            have hpure : out ∈ support (pure ((none, none, none), σ) :
                ProbComp (CryptoVerification.E2E.BHE2ESmResp ℓ × BHE2EDrvState S ℓ)) →
                out.2.toModelDriverBase = σ.toModelDriverBase ∧ out.2.st = σ.st := by
              simp only [support_pure, Set.mem_singleton_iff]
              intro heq; subst heq; exact ⟨rfl, rfl⟩
            rcases sq with (((qTr | qCh) | ⟨pDl, cDl⟩) | ⟨pIj, cIj⟩) | qCr
            · exact hrunStd _ hout
            · exact hrunStd _ hout
            · cases pDl
              · dsimp only at hout
                split_ifs at hout
                · exact hpure hout
                · exact hrunStd _ hout
              · dsimp only at hout
                split_ifs at hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; exact hpure hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
                · cases hdec : bhDecodePreKeyMsgE cDl
                  · rw [hdec] at hout; exact hrunStd _ hout
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
                  · rw [hdec] at hout; exact hrunStd _ hout
                  · rw [hdec] at hout; dsimp only at hout
                    split_ifs at hout
                    · exact hrunStd _ hout
                    · exact hpure hout
            · exact hrunStd _ hout

private theorem compositionLocalStart_base_mirror {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki) (C : Crypto) (K : MlKem) (bMode? : Option Bool)
    {d : ModelDriverBase S} {σ : BHE2EDrvState S ℓ}
    (hd : d = σ.toModelDriverBase) (hMir : MirrorKiInv d σ.st) (sid : SignalPqxdh.SessionId S)
    {out : Option ℕ × BHE2EDrvState S ℓ}
    (hout : out ∈ support (CryptoVerification.E2E.compositionLocalStart ki C K bMode? σ sid)) :
    d = out.2.toModelDriverBase ∧ MirrorKiInv d out.2.st := by
  unfold CryptoVerification.E2E.compositionLocalStart at hout
  split at hout
  · simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨hd, hMir⟩
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨kr1, st1⟩, h1, ⟨kr2, st2⟩, h2, ac, -, rfl⟩
    have hMir2 : MirrorKiInv d st2 :=
      mirrorKiInv_mono (mirrorKiInv_mono hMir (hKi.mono _ σ.st kr1 st1 h1))
        (hKi.mono _ st1 kr2 st2 h2)
    unfold CryptoVerification.E2E.bhE2EFinishStartSpk
    split
    · split_ifs <;> exact ⟨hd, hMir2⟩
    · exact ⟨hd, hMir2⟩

private structure AdapterCouplingInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem)
    (s_ad : CliAdapterState S) (σ_e2e : BHE2EDrvState S ℓ) : Prop where
  no_ack : ∀ k inst, s_ad.1 k = some inst → inst.aliceAcked = false
  drv_eq : s_ad.2.2 = σ_e2e.toModelDriverBase
  mirror_ki : MirrorKiInv s_ad.2.2 σ_e2e.st
  reach : Computational.Proofs.E2E.Dsl.SmReachInv.DrvSmReachInv C K σ_e2e
  no_whisp : DrvNoWhisperTrans σ_e2e

private theorem adapterCouplingInv_init {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : MlKem) (b : Bool) (secb : Bool) :
    AdapterCouplingInv C K (cliAdapterInitState S)
      ({ b := b, st := SignalPqxdh.KeyIndState.empty S secb } : BHE2EDrvState S ℓ) where
  no_ack := fun _ _ h => nomatch h
  drv_eq := rfl
  mirror_ki := mirrorKiInv_empty _
  reach := fun _ hd => nomatch hd
  no_whisp := drvNoWhisperTrans_init b _

private theorem adapterCouplingInv_of_sm_step {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad s_ad' : CliAdapterState S} {σ_e2e σ' : BHE2EDrvState S ℓ}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (hNoAck' : ∀ k inst, s_ad'.1 k = some inst → inst.aliceAcked = false)
    (hDrv' : s_ad'.2.2 = s_ad.2.2)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    {sr : CryptoVerification.E2E.BHE2ESmResp ℓ}
    (hout : (sr, σ') ∈ support (CryptoVerification.E2E.bhE2EStepLocalSm C K qep decT encT
      σ_e2e i sq)) :
    AdapterCouplingInv C K s_ad' σ' := by
  obtain ⟨hBaseEq, hStEq⟩ := bhE2EStepLocalSm_base_st_eq C K qep decT encT i sq hout
  refine ⟨hNoAck', ?_, ?_,
    Computational.Proofs.E2E.Dsl.SmReachInv.drvSmReachInv_bhE2EStepLocalSm C K qep decT encT
      hInv.reach i sq hout,
    drvNoWhisperTrans_bhE2EStepLocalSm C K qep decT encT hInv.no_whisp i sq hout⟩
  · rw [hDrv', hInv.drv_eq, hBaseEq]
  · rw [hDrv', hStEq]
    exact hInv.mirror_ki

abbrev CoinLogM : Type → Type := WriterT (List (BitVec 512)) ProbComp

def bhE2EStepLocalSmCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    CoinLogM (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) := do
  if !bhE2EDrvInstClean σ i then return ((none, none, none), σ)
  else
    match σ.insts[i]?, σ.instMeta[i]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d then
        let imCorr := { im with bobAccepted := true, ikACorrAtAccept := true }
        let σ' := { σ with instMeta := σ.instMeta.set i imCorr }
        return ((none, none, none), σ')
      else
        match d.gs with
        | none => return ((none, none, none), σ)
        | some gs =>
          let spqr := spqrV1SessionUniformCoins C.F K
          let sch := sessionSchemeFixedSpk (paramsIdsWithSpqr C spqr d.idA d.idB) ℓ d.spkCoins
          let cfg := configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT
          let runStd (q' : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
              (σ0 : BHE2EDrvState S ℓ) : CoinLogM (BHE2ESmResp ℓ × BHE2EDrvState S ℓ) := do
            let (r, gs') ← (oracleImplRM (smSchemeCoinLogged sch) (2 + 1) qep cfg q').run gs
            let accepted := bhIsBobAcceptSMResp q' r
            let im' := if !im.bobAccepted && accepted then
                { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ0 d }
              else im
            let σ1 := { σ0 with insts := σ0.insts.set i { d with gs := some gs' },
                                instMeta := σ0.instMeta.set i im' }
            return (bhPackSmResp q' r, σ1)
          match q with
          | .inl (.inl (.inr (.A, c))) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σ)
            else runStd q σ
          | .inl (.inr (.A, c)) =>
            if (bhDecodePreKeyMsgE c).isSome then return ((none, none, none), σ)
            else runStd q σ
          | .inl (.inl (.inr (.B, c))) =>
            if !im.bobAccepted then
              match bhDecodePreKeyMsgE c with
              | some m =>
                if c == wirePrekey ::
                    (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
                  runStd (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σ)
              | none => return ((none, none, none), σ)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr then
                  runStd (.inl (.inl (.inr (.B, m.inner)))) σ
                else return ((none, none, none), σ)
              | none => runStd (.inl (.inl (.inr (.B, c)))) σ
          | .inl (.inr (.B, c)) =>
            if !im.bobAccepted then return ((none, none, none), σ)
            else
              match bhDecodePreKeyMsgE c with
              | some m =>
                if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                   decide (m.inner.length + 2048 < 2 ^ 32) then
                  runStd (.inl (.inr (.B, m.inner))) σ
                else return ((none, none, none), σ)
              | none => runStd (.inl (.inr (.B, c))) σ
          | _ => runStd q σ
    | _, _ => return ((none, none, none), σ)

def cliE2EDrvImplWithCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (BHE2EDrvState S ℓ) CoinLogM) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let σ ← get
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return .noneResp
    else
      let (kr, st') ← StateT.lift (liftM ((ki kq).run σ.st))
      set (bhE2EMirror { σ with st := st' } kq kr)
      return kr
  | .inr (.inl (.inr (.startDR sid))) => do
    let σ ← get
    let (idx?, σ') ← StateT.lift (liftM (compositionLocalStart ki C K (some σ.b) σ sid))
    set σ'
    return idx?
  | .inr (.inr ⟨i, sq⟩) => do
    let σ ← get
    let (sr, σ') ← StateT.lift (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i sq)
    set σ'
    return bhUnpackSmResp sq sr

/-- Send-coin-logged E2E model experiment returning `(out, coinsLog)` where `coinsLog` collects
every 512-bit coin word passed to an SPQR V1 session `send` across all promoted instances. -/
def cliE2EExpWithKiCoinLogged (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    ProbComp (Bool × List (BitVec 512)) :=
  WriterT.run do
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let (b', σ) ← (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) B).run
      { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
    if !allTestedSessionsFresh P σ.st then liftM ($ᵗ Bool : ProbComp Bool)
    else return (b' == b || bhE2EDrvWon σ b)

private def forgetCoinW {α : Type} (m : CoinLogM α) : ProbComp α :=
  Prod.fst <$> m.run

@[simp] private theorem forgetCoinW_pure {α : Type} (a : α) :
    forgetCoinW (pure a) = pure a := by
  simp [forgetCoinW]

@[simp] private theorem forgetCoinW_map {α β : Type} (f : α → β) (m : CoinLogM α) :
    forgetCoinW (f <$> m) = f <$> forgetCoinW m := by
  simp [forgetCoinW, Functor.map_map]

@[simp] private theorem forgetCoinW_bind {α β : Type} (m : CoinLogM α) (k : α → CoinLogM β) :
    forgetCoinW (m >>= k) = forgetCoinW m >>= fun a => forgetCoinW (k a) := by
  simp [forgetCoinW, map_eq_bind_pure_comp, bind_assoc]

@[simp] private theorem forgetCoinW_liftM {α : Type} (c : ProbComp α) :
    forgetCoinW (liftM c) = c := by
  dsimp [forgetCoinW, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [Functor.map_map]

@[simp] private theorem forgetCoinW_ite {α : Type} (c : Prop) [Decidable c] (t e : CoinLogM α) :
    forgetCoinW (if c then t else e) = if c then forgetCoinW t else forgetCoinW e := by
  split_ifs <;> rfl

private def forgetCoinS1 {σ α : Type} (m : StateT σ CoinLogM α) : StateT σ ProbComp α :=
  fun s => forgetCoinW (m.run s)

@[simp] private theorem forgetCoinS1_run {σ α : Type} (m : StateT σ CoinLogM α) (s : σ) :
    (forgetCoinS1 m).run s = forgetCoinW (m.run s) := rfl

@[simp] private theorem forgetCoinS1_pure {σ α : Type} (a : α) :
    forgetCoinS1 (pure a : StateT σ CoinLogM α) = pure a := by
  ext s; simp

@[simp] private theorem forgetCoinS1_map {σ α β : Type} (f : α → β) (m : StateT σ CoinLogM α) :
    forgetCoinS1 (f <$> m) = f <$> forgetCoinS1 m := by
  ext s; simp [StateT.run_map]

@[simp] private theorem forgetCoinS1_bind {σ α β : Type}
    (m : StateT σ CoinLogM α) (k : α → StateT σ CoinLogM β) :
    forgetCoinS1 (m >>= k) = forgetCoinS1 m >>= fun a => forgetCoinS1 (k a) := by
  ext s; simp

@[simp] private theorem forgetCoinS1_get {σ : Type} :
    forgetCoinS1 (get : StateT σ CoinLogM σ) = get := by
  ext s; simp

@[simp] private theorem forgetCoinS1_set {σ : Type} (s' : σ) :
    forgetCoinS1 (set s' : StateT σ CoinLogM PUnit) = set s' := by
  ext s; simp

@[simp] private theorem forgetCoinS1_lift {σ α : Type} (m : CoinLogM α) :
    forgetCoinS1 (StateT.lift m : StateT σ CoinLogM α) = StateT.lift (forgetCoinW m) := by
  ext s; simp [StateT.run_lift]

@[simp] private theorem forgetCoinS1_liftM_prob {σ α : Type} (c : ProbComp α) :
    forgetCoinS1 (liftM c : StateT σ CoinLogM α) = liftM c := by
  ext s
  change forgetCoinW ((StateT.lift (liftM c : CoinLogM α)).run s) = (StateT.lift c).run s
  simp [StateT.run_lift]

@[simp] private theorem forgetCoinS1_liftStateT {σ α : Type} (x : StateT σ ProbComp α) :
    forgetCoinS1 (CryptoVerification.E2E.liftStateT (n := CoinLogM) x) = x := by
  ext s; exact forgetCoinW_liftM (x s)

private theorem forgetCoinS1_oracleImplRM_smSchemeCoinLogged
    {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (q : (CryptoGames.SM.spec St Msg (BitVec 512) C).Domain) :
    forgetCoinS1 (oracleImplRM (smSchemeCoinLogged sch) Δ qep cfg q) =
      CryptoGames.SM.oracleImplR sch Δ qep cfg q := by
  have hsend : ∀ s m r, forgetCoinW ((smSchemeCoinLogged sch).send s m r) = pure (sch.send s m r) := by
    intro s m r; simp [smSchemeCoinLogged, forgetCoinW]
  have hrecv : ∀ s c rc, forgetCoinW ((smSchemeCoinLogged sch).receive s c rc) = pure (sch.receive s c rc) := by
    intro s c rc; simp [smSchemeCoinLogged]
  rcases q with (((⟨p, m, r⟩ | ⟨p, m₀, m₁, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · change forgetCoinS1 (CryptoVerification.E2E.transmitRM (smSchemeCoinLogged sch) Δ qep cfg (p, m, r)) =
      CryptoGames.SM.transmitR sch Δ qep cfg (p, m, r)
    ext gs
    unfold CryptoVerification.E2E.transmitRM CryptoGames.SM.transmitR
      CryptoGames.SM.transmitImpl CryptoGames.SMSchemeR.sendPart
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs p
    · simp [StateT.run_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_monadLift,
          monadLift_self, forgetCoinW_bind, forgetCoinW_liftM, bind_assoc]
        congr 1; funext x; rcases x with ⟨cns, bad⟩
        rcases h : gs.epMgmt Δ qep p bad with _ | s₁
        · simp [h, StateT.run_pure]
        · simp [h, hsend, StateT.run_map, StateT.run_set, StateT.run_bind]
      · simp [StateT.run_pure]
  · change forgetCoinS1 (CryptoVerification.E2E.challRM (smSchemeCoinLogged sch) Δ qep cfg (p, m₀, m₁, r)) =
      CryptoGames.SM.challR sch Δ qep cfg (p, m₀, m₁, r)
    ext gs
    unfold CryptoVerification.E2E.challRM CryptoGames.SM.challR
      CryptoGames.SM.challImpl CryptoGames.SMSchemeR.sendPart
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK gs p
    · simp [StateT.run_pure]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_monadLift,
          monadLift_self, forgetCoinW_bind, forgetCoinW_liftM, bind_assoc]
        congr 1; funext x; rcases x with ⟨cns, bad⟩
        rcases h : gs.epMgmt Δ qep p bad with _ | s₁
        · simp [h, StateT.run_pure]
        · by_cases hc : s₁.safeCh Δ p = false ∨ cfg.base.challAllowedIn (s₁.epoch p) = false
          · simp [h, hc, StateT.run_pure]
          · simp [h, hc, hsend, StateT.run_map, StateT.run_set, StateT.run_bind]
      · simp [StateT.run_pure]
  · change forgetCoinS1 (CryptoVerification.E2E.deliverRM (smSchemeCoinLogged sch) cfg (p, c)) =
      CryptoGames.SM.deliverR sch cfg (p, c)
    ext gs
    unfold CryptoVerification.E2E.deliverRM CryptoGames.SM.deliverR
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases gs.inTransit p.other c with
      | none => simp [StateT.run_pure]
      | some r =>
        dsimp only
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          forgetCoinW_bind, forgetCoinW_liftM, hrecv, pure_bind, bind_assoc]
        congr 1; funext rc
        rcases sch.receive (gs.st p) c rc with _ | ⟨st', t', i', m'⟩ <;>
          (try dsimp only) <;> (try split_ifs) <;>
          simp [StateT.run_pure, StateT.run_map, StateT.run_set]
    · simp [StateT.run_pure]
  · change forgetCoinS1 (CryptoVerification.E2E.injectRM (smSchemeCoinLogged sch) Δ qep cfg (p, c)) =
      CryptoGames.SM.injectR sch Δ qep cfg (p, c)
    ext gs
    unfold CryptoVerification.E2E.injectRM CryptoGames.SM.injectR
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases hcond : (gs.win || (gs.inTransit p.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
        StateT.run_monadLift, monadLift_self, forgetCoinW_bind, forgetCoinW_liftM, hrecv,
        pure_bind, bind_assoc]
      congr 1; funext rc
      rcases sch.receive (gs.st p) c rc with _ | ⟨st', t', i', m'⟩ <;>
        (try dsimp only) <;> (try split_ifs) <;>
        simp [StateT.run_pure, StateT.run_map, StateT.run_set]
    · simp [StateT.run_pure]
  · exact forgetCoinS1_liftStateT (CryptoGames.SM.corrR cfg p)

private theorem forgetCoinW_bhE2EStepLocalSmCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    forgetCoinW (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i q) =
      bhE2EStepLocalSm C K qep decT encT σ i q := by
  unfold bhE2EStepLocalSmCoinLogged bhE2EStepLocalSm
  cases hclean : (!bhE2EDrvInstClean σ i)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases σ.insts[i]? with _ | d
    · simp
    · rcases σ.instMeta[i]? with _ | im
      · simp
      · dsimp only
        cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery q && bhE2EInstIkACorr σ d)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rcases d.gs with _ | gs
          · simp
          · dsimp only
            rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | q₅
            · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
            · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
            · cases p
              · dsimp only
                cases (bhDecodePreKeyMsgE c).isSome
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                · simp
              · dsimp only
                cases (!im.bobAccepted)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                  · cases (bhHdrOfPreKeyMsg m == d.hdr)
                    · simp
                    · simp only [↓reduceIte]
                      rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                · simp only [↓reduceIte]
                  rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · simp
                  · cases (c == wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes)
                    · simp
                    · simp only [↓reduceIte]
                      rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
            · cases p
              · dsimp only
                cases (bhDecodePreKeyMsgE c).isSome
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                · simp
              · dsimp only
                cases (!im.bobAccepted)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                  · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                  · cases (bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                      decide (m.inner.length + 2048 < 2 ^ 32))
                    · simp
                    · simp only [↓reduceIte]
                      rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
                · simp
            · rw [forgetCoinW_bind, ← forgetCoinS1_run, forgetCoinS1_oracleImplRM_smSchemeCoinLogged]; simp
        · simp
  · simp

private theorem forgetCoinS1_cliE2EDrvImplWithCoinLogged {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    forgetCoinS1 (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT q) =
      cliE2EDrvImplWith P ki C K qep decT encT q := by
  rcases q with n | ((kq | ⟨sid⟩) | ⟨i, sq⟩)
  · simp [cliE2EDrvImplWithCoinLogged, cliE2EDrvImplWith]
  · ext σ
    unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
    simp only [forgetCoinS1_run, StateT.run_bind, StateT.run_get, pure_bind]
    cases (!bhDrvKiQueryOk P σ.toModelDriverBase kq)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases kq <;> dsimp only <;>
        (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> (try split_ifs) <;>
        simp [StateT.run_pure, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_map]
    · simp [StateT.run_pure]
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
    simp only [forgetCoinS1_bind, forgetCoinS1_get]
    congr 1; funext σ
    simp only [forgetCoinS1_lift, forgetCoinW_liftM]
    rfl
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWith
    simp only [forgetCoinS1_bind, forgetCoinS1_get]
    congr 1; funext σ
    simp only [forgetCoinS1_lift, forgetCoinW_bhE2EStepLocalSmCoinLogged]
    rfl

private theorem forgetCoinS1_simulateQ {ι σ α : Type} {spec : OracleSpec ι}
    {implM : QueryImpl spec (StateT σ CoinLogM)}
    {impl : QueryImpl spec (StateT σ ProbComp)}
    (h : ∀ q, forgetCoinS1 (implM q) = impl q) (oa : OracleComp spec α) :
    forgetCoinS1 (simulateQ implM oa) = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, forgetCoinS1_bind, h]
    congr 1; funext u; exact ih u

theorem cliE2EExpWithKiCoinLogged_fst (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) :
    Prod.fst <$> cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT B =
      cliE2EExpWithKi secb S P ki C K ℓ qep decT encT B := by
  change forgetCoinW (do
      let b ← liftM ($ᵗ Bool : ProbComp Bool)
      let (b', σ) ← (simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) B).run
        { b := b, st := SignalPqxdh.KeyIndState.empty S secb }
      if !allTestedSessionsFresh P σ.st then liftM ($ᵗ Bool : ProbComp Bool)
      else return (b' == b || bhE2EDrvWon σ b)) =
    cliE2EExpWithKi secb S P ki C K ℓ qep decT encT B
  unfold cliE2EExpWithKi
  simp only [forgetCoinW_bind, forgetCoinW_liftM]
  congr 1; funext b
  rw [← forgetCoinS1_run, forgetCoinS1_simulateQ
    (forgetCoinS1_cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) B]
  congr 1; funext ⟨b', σ⟩
  split_ifs <;> simp

private theorem mem_support_bhE2EStepLocalSm_of_coinLogged
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} {i : ℕ}
    {q : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain}
    {out : BHE2ESmResp ℓ × BHE2EDrvState S ℓ} {w : List (BitVec 512)}
    (h : (out, w) ∈ support (WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i q))) :
    out ∈ support (bhE2EStepLocalSm C K qep decT encT σ i q) := by
  rw [← forgetCoinW_bhE2EStepLocalSmCoinLogged, forgetCoinW, map_eq_bind_pure_comp,
    Function.comp_def, mem_support_bind_iff]
  exact ⟨(out, w), h, by simp only [support_pure, Set.mem_singleton_iff]⟩

private theorem run_liftM_prob {α : Type} (c : ProbComp α) :
    WriterT.run (liftM c : CoinLogM α) = (fun a => (a, ([] : List (BitVec 512)))) <$> c :=
  rfl

private theorem run_injectRM_smSchemeCoinLogged
    {Key St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (sch : CryptoGames.SMSchemeR Key St Msg (BitVec 512) (BitVec 256) C)
    (Δ qep : ℕ) (cfg : CryptoGames.SM.ConfigR St Msg C)
    (p : Party) (c : C) (gs : CryptoGames.SM.GameState St Msg C) :
    WriterT.run ((CryptoVerification.E2E.injectRM (smSchemeCoinLogged sch) Δ qep cfg (p, c)).run gs) =
      (fun x => (x, ([] : List (BitVec 512)))) <$>
        (CryptoGames.SM.injectR sch Δ qep cfg (p, c)).run gs := by
  have hrecv : ∀ s ct rc,
      WriterT.run ((smSchemeCoinLogged sch).receive s ct rc) =
        pure (sch.receive s ct rc, ([] : List (BitVec 512))) := by
    intro s ct rc; simp [smSchemeCoinLogged]
  unfold CryptoVerification.E2E.injectRM CryptoGames.SM.injectR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hcond : (gs.win || (gs.inTransit p.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift,
      StateT.run_monadLift, monadLift_self, WriterT.run_bind, hrecv, run_liftM_prob,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, List.nil_append]
    congr 1; funext rc
    rcases sch.receive (gs.st p) c rc with _ | ⟨st', t', i', m'⟩ <;>
      (try dsimp only) <;> (try split_ifs) <;>
      simp [StateT.run_pure, StateT.run_map, StateT.run_set, List.empty_eq]
  · simp [StateT.run_pure]

private theorem run_bhE2EStepLocalSmCoinLogged_ij
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (i : ℕ) (p : Party) (c : Bytes) :
    WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i (.inl (.inr (p, c)))) =
      (fun x => (x, ([] : List (BitVec 512)))) <$>
        bhE2EStepLocalSm C K qep decT encT σ i (.inl (.inr (p, c))) := by
  unfold bhE2EStepLocalSmCoinLogged bhE2EStepLocalSm
  cases hclean : (!bhE2EDrvInstClean σ i)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases σ.insts[i]? with _ | d
    · simp
    · rcases σ.instMeta[i]? with _ | im
      · simp
      · dsimp only
        cases hcorr : (!im.bobAccepted && bhIsBobRecvSMQuery (.inl (.inr (p, c))) && bhE2EInstIkACorr σ d)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rcases d.gs with _ | gs
          · simp
          · have hStd : ∀ (p' : Party) (c' : Bytes),
                WriterT.run (do
                  let (r, gs') ← (oracleImplRM (smSchemeCoinLogged
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins)) (2 + 1) qep
                    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT)
                    (.inl (.inr (p', c')))).run gs
                  let accepted := bhIsBobAcceptSMResp (.inl (.inr (p', c'))) r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  return (bhPackSmResp (.inl (.inr (p', c'))) r, σ1)) =
                (fun x => (x, ([] : List (BitVec 512)))) <$> (do
                  let (r, gs') ← (CryptoGames.SM.oracleImplR
                    (sessionSchemeFixedSpk
                      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                      ℓ d.spkCoins) (2 + 1) qep
                    (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT)
                    (.inl (.inr (p', c')))).run gs
                  let accepted := bhIsBobAcceptSMResp (.inl (.inr (p', c'))) r
                  let im' := if !im.bobAccepted && accepted then
                      { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
                    else im
                  let σ1 := { σ with insts := σ.insts.set i { d with gs := some gs' },
                                     instMeta := σ.instMeta.set i im' }
                  return (bhPackSmResp (.inl (.inr (p', c'))) r, σ1)) := by
              intro p' c'
              have hinj := run_injectRM_smSchemeCoinLogged
                (sessionSchemeFixedSpk
                  (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) d.idA d.idB)
                  ℓ d.spkCoins) (2 + 1) qep
                (configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := Plain ℓ) decT encT)
                p' c' gs
              simp only [WriterT.run_bind]
              change (WriterT.run ((CryptoVerification.E2E.injectRM _ _ _ _ (p', c')).run gs) >>= _) =
                (fun x => (x, [])) <$> ((CryptoGames.SM.injectR _ _ _ _ (p', c')).run gs >>= _)
              rw [hinj]
              simp only [WriterT.run_pure, map_eq_bind_pure_comp, Function.comp_def,
                bind_assoc, pure_bind, List.empty_eq, List.append_nil]
            cases p
            · dsimp only
              cases (bhDecodePreKeyMsgE c).isSome
              · simp only [Bool.false_eq_true, ↓reduceIte]; simpa using hStd .A c
              · simp
            · dsimp only
              cases hbob : im.bobAccepted
              · simp
              · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                rcases bhDecodePreKeyMsgE c with _ | m <;> dsimp only
                · simpa [hbob] using hStd .B c
                · cases (bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                    decide (m.inner.length + 2048 < 2 ^ 32))
                  · simp
                  · simp only [↓reduceIte]; simpa [hbob] using hStd .B m.inner
        · simp
  · simp

private theorem bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {σ : BHE2EDrvState S ℓ} (hNoWhisp : DrvNoWhisperTrans σ)
    (i : ℕ) (P : Party) (y : Bytes) :
    WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i
        (.inl (.inr (P, E2EPureOp.eval ℓ .wrapWhisperWire y)))) =
      WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ i
        (.inl (.inr (P, bhShallowWrapWhisper y)))) := by
  rw [run_bhE2EStepLocalSmCoinLogged_ij, run_bhE2EStepLocalSmCoinLogged_ij,
    bhE2EStepLocalSm_ij_wrapWhisperWire_eq C K qep decT encT hNoWhisp i P y]

private abbrev DrvLogState (S : SignalPqxdh.Setup) (ℓ : ℕ) : Type :=
  BHE2EDrvState S ℓ × List (BitVec 512)

private def cliE2EDrvImplWithLogState {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      (StateT (DrvLogState S ℓ) ProbComp) := fun q =>
  match q with
  | .inl n => liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl kq)) => do
    let s ← get
    if !bhDrvKiQueryOk P s.1.toModelDriverBase kq then
      return .noneResp
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted s.1.instMeta u | _ => false) then
      return .noneResp
    else
      let p ← liftM ((ki kq).run s.1.st)
      set (bhE2EMirror { s.1 with st := p.2 } kq p.1, s.2)
      return p.1
  | .inr (.inl (.inr (.startDR sid))) => do
    let s ← get
    let p ← liftM (compositionLocalStart ki C K (some s.1.b) s.1 sid)
    set (p.2, s.2)
    return p.1
  | .inr (.inr ⟨i, sq⟩) => do
    let s ← get
    let p ← liftM (WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT s.1 i sq))
    set (p.1.2, s.2 ++ p.2)
    return bhUnpackSmResp sq p.1.1

private theorem step_cliE2EDrvImplWithCoinLogged_eq_logState
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
    (σ : BHE2EDrvState S ℓ) (log : List (BitVec 512)) :
    (fun x => (x.1.1, (x.1.2, log ++ x.2))) <$>
        WriterT.run ((cliE2EDrvImplWithCoinLogged P ki C K qep decT encT q).run σ) =
      (cliE2EDrvImplWithLogState P ki C K qep decT encT q).run (σ, log) := by
  rcases q with n | ((kq | ⟨sid⟩) | ⟨i, sq⟩)
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWithLogState
    change (fun x => (x.1.1, (x.1.2, log ++ x.2))) <$>
        WriterT.run ((StateT.lift (liftM (query (spec := unifSpec) n : ProbComp (Fin (n + 1))))).run σ) =
      (StateT.lift (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))).run (σ, log)
    simp only [StateT.run_lift, WriterT.run_bind, WriterT.run_pure, run_liftM_prob,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, List.empty_eq,
      List.append_nil]
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWithLogState
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases (!bhDrvKiQueryOk P σ.toModelDriverBase kq)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases kq <;> dsimp only <;>
        (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> (try split_ifs) <;>
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, WriterT.run_bind, WriterT.run_pure, run_liftM_prob,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, List.empty_eq,
          List.append_nil]
    · simp only [↓reduceIte, StateT.run_pure, WriterT.run_pure, map_eq_bind_pure_comp,
        Function.comp_def, pure_bind, List.empty_eq, List.append_nil]
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWithLogState
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, WriterT.run_bind, WriterT.run_pure,
      run_liftM_prob, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
      List.empty_eq, List.append_nil]
  · unfold cliE2EDrvImplWithCoinLogged cliE2EDrvImplWithLogState
    simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, WriterT.run_bind, WriterT.run_pure,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, List.empty_eq,
      List.append_nil]

private theorem run_simulateQ_cliE2EDrvImplWithCoinLogged_eq_logState
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) (log : List (BitVec 512)) :
    (fun x => (x.1.1, (x.1.2, log ++ x.2))) <$>
        WriterT.run ((simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) oa).run σ) =
      (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT) oa).run (σ, log) := by
  induction oa using OracleComp.inductionOn generalizing σ log with
  | pure a =>
    simp [StateT.run_pure, List.empty_eq]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, WriterT.run_bind]
    rw [← step_cliE2EDrvImplWithCoinLogged_eq_logState P ki C K qep decT encT q σ log]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    congr 1; funext ⟨⟨u, σ₁⟩, w₁⟩
    have ih₁ := ih u σ₁ (log ++ w₁)
    simp only [map_eq_bind_pure_comp, Function.comp_def, List.append_assoc] at ih₁
    simpa using ih₁

private theorem run_simulateQ_cliE2EDrvImplWithCoinLogged_nil
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (σ : BHE2EDrvState S ℓ) :
    WriterT.run ((simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT) oa).run σ) =
      (fun x => ((x.1, x.2.1), x.2.2)) <$>
        (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT) oa).run (σ, []) := by
  rw [← run_simulateQ_cliE2EDrvImplWithCoinLogged_eq_logState P ki C K qep decT encT oa σ []]
  simp [Functor.map_map]

private def cliAdapterStepImplWithLogState {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhGameSpec S ℓ (BitVec 512))
      (StateT (CliAdapterState S) (StateT (DrvLogState S ℓ) ProbComp)) := fun q =>
  StateT.mk fun σ_ad =>
    simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      ((bhShallowAdapterImpl S ℓ (BitVec 512) q).run σ_ad)

private theorem simulateQ_cliE2EDrvImplWithLogState_adapter_run
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) α)
    (σ_ad : CliAdapterState S) (σ_log : DrvLogState S ℓ) :
    (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      ((simulateQ (bhShallowAdapterImpl S ℓ (BitVec 512)) oa).run σ_ad)).run σ_log =
    (((simulateQ (cliAdapterStepImplWithLogState P ki C K qep decT encT) oa).run σ_ad).run
      σ_log) := by
  induction oa using OracleComp.inductionOn generalizing σ_ad σ_log with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind, run_simulateQ_query_bind,
      StateT.run_bind]
    exact bind_congr fun ⟨⟨r, σ_ad'⟩, σ_log'⟩ => ih r σ_ad' σ_log'

private def cliHonestStepImplWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhGameSpec S ℓ (BitVec 512))
      (StateT (cliAdapterStateTy S ℓ).denote (StateT (DrvLogState S ℓ) ProbComp)) := fun q =>
  StateT.mk fun s =>
    simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      ((handlerImpl (C := e2eBhAdapterCodec S ℓ)
        (I := e2eBhAdapterIface S ℓ)
        (cliAdapterHandle decT encT S ℓ) q).run s)

private theorem simulateQ_cliE2EDrvImplWith_honest_run
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) α)
    (s : (cliAdapterStateTy S ℓ).denote) (σ_log : DrvLogState S ℓ) :
    (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      ((simulateQ (handlerImpl (C := e2eBhAdapterCodec S ℓ)
        (I := e2eBhAdapterIface S ℓ)
        (cliAdapterHandle decT encT S ℓ)) oa).run s)).run σ_log =
    (((simulateQ (cliHonestStepImplWith P ki C K qep decT encT) oa).run s).run σ_log) := by
  induction oa using OracleComp.inductionOn generalizing s σ_log with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind, run_simulateQ_query_bind,
      StateT.run_bind]
    exact bind_congr fun ⟨⟨r, s'⟩, σ_log'⟩ => ih r s' σ_log'

private theorem partyEnc_eq_partyToBool (p : Party) :
    CryptoGames.SM.partyEnc p = partyToBool p := by
  cases p <;> rfl

private theorem partyDec_eq_boolToParty (b : Bool) :
    CryptoGames.SM.partyDec b = boolToParty b := by
  cases b <;> rfl

private theorem smRrEnc_eq_recvResultEnc {ℓ : ℕ} (r : CryptoGames.SM.RecvResult (Plain ℓ)) :
    CryptoGames.SM.smRrEnc r = recvResultEnc (ℓ := ℓ) r := by
  cases r <;> rfl

private theorem map_smRrEnc_eq_recvResultEnc {ℓ : ℕ}
    (optR : Option (CryptoGames.SM.RecvResult (Plain ℓ))) :
    optR.map CryptoGames.SM.smRrEnc = optR.map (recvResultEnc (ℓ := ℓ)) := by
  cases optR with
  | none => rfl
  | some r => exact congrArg some (smRrEnc_eq_recvResultEnc r)

private theorem map_recvResultDec_enc {ℓ : ℕ}
    (optR : Option (CryptoGames.SM.RecvResult (Plain ℓ))) :
    (optR.map (recvResultEnc (ℓ := ℓ))).map recvResultDec = optR := by
  cases optR with
  | none => rfl
  | some r => exact congrArg some (recvResultDec_recvResultEnc r)

private theorem map_smRrDec_enc {ℓ : ℕ}
    (optR : Option (CryptoGames.SM.RecvResult (Plain ℓ))) :
    (optR.map CryptoGames.SM.smRrEnc).map CryptoGames.SM.smRrDec = optR := by
  cases optR with
  | none => rfl
  | some r => cases r <;> rfl

private theorem wrapSendWire_eq_of_len_le {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (inst : BHAdapterInstMeta S) (hAck : inst.aliceAcked = false)
    (bParty ackFlag : Bool) {ct : Bytes} (hct : ct.length ≤ 32 * (ℓ / 32) + 450) :
    (if bParty then E2EPureOp.eval ℓ .wrapWhisperWire ct
     else if ackFlag then E2EPureOp.eval ℓ .wrapWhisperWire ct
     else E2EPureOp.eval ℓ .wrapPreKeyWire
       (bhInitRegId inst.sid, (hdrV (ℓ := ℓ) inst.hdr, ct))) =
    (if bParty then bhShallowWrapWhisper ct
     else if ackFlag then bhShallowWrapWhisper ct
     else bhWrapSendOut inst .A ct) := by
  have hw : E2EPureOp.eval ℓ .wrapWhisperWire ct =
      (if ct.isEmpty then [] else wireWhisper :: ct) :=
    Computational.Proofs.E2E.Dsl.ClampsLossless.e2ePureOps_eval_wrapWhisperWire_lossless
      ℓ ct (by omega)
  cases bParty
  · cases ackFlag
    · simp only [Bool.false_eq_true, ↓reduceIte]
      change (e2ePureOps ℓ).eval .wrapPreKeyWire (bhInitRegId inst.sid, (hdrV (ℓ := ℓ) inst.hdr, ct)) =
        bhWrapSendOut inst .A ct
      rw [Computational.Proofs.E2E.Dsl.ClampsLossless.e2ePureOps_eval_wrapPreKeyWire_lossless
        ℓ (bhInitRegId inst.sid) (hdrV (ℓ := ℓ) inst.hdr) ct (by omega)]
      dsimp only [bhWrapSendOut, CryptoVerification.E2E.bhAlicePreKeyMsgE]
      rw [hdrOfV_hdrV, hAck]
      rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, bhShallowWrapWhisper]
      exact hw
  · simp only [↓reduceIte, bhShallowWrapWhisper]
    exact hw

private def aliceUpdV {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (Ty.opt (recvResultT (ℓ := ℓ))).denote)
    (sV : (cliAdapterStateTy S ℓ).denote) (i : ℕ) : (cliAdapterStateTy S ℓ).denote :=
  match v with
  | none => sV
  | some x =>
    match x with
    | .inl _ => sV
    | .inr _ => (sV.1, ((fun j => if j = i then true else sV.2.1 j), sV.2.2))

private theorem aliceUpd_stateToV {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (optR : Option (CryptoGames.SM.RecvResult (Plain ℓ)))
    (s_ad : CliAdapterState S) (i : ℕ) :
    aliceUpdV (optR.map (recvResultEnc (ℓ := ℓ))) (cliAdapterStateToV (ℓ := ℓ) s_ad) i =
      cliAdapterStateToV (ℓ := ℓ) (bhShallowAliceUpdate s_ad i optR) := by
  rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩ <;> rfl

private theorem bhShallowAliceUpdate_preserves {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (optR : Option (CryptoGames.SM.RecvResult (Plain ℓ)))
    {s_ad : CliAdapterState S}
    (hNoAck : ∀ k inst, s_ad.1 k = some inst → inst.aliceAcked = false) (i : ℕ) :
    (∀ k inst, (bhShallowAliceUpdate s_ad i optR).1 k = some inst → inst.aliceAcked = false) ∧
    (bhShallowAliceUpdate s_ad i optR).2.2 = s_ad.2.2 := by
  rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩ <;> exact ⟨hNoAck, rfl⟩

private def bobUpdV {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (v : (Ty.opt (recvResultT (ℓ := ℓ))).denote)
    (sV : (cliAdapterStateTy S ℓ).denote) (i : ℕ)
    (instV : (adapterInstMetaT (ℓ := ℓ)).denote) (mRegId : BitVec 32) :
    (cliAdapterStateTy S ℓ).denote :=
  match v with
  | none => sV
  | some x =>
    match x with
    | .inl _ => sV
    | .inr _ =>
      let newBobRem := if !instV.2 then mRegId else instV.1.2.2.1
      let newInst := ((instV.1.1, (instV.1.2.1, (newBobRem, instV.1.2.2.2))), true)
      ((fun j => if j = i then some newInst else sV.1 j), sV.2)

private theorem bobUpd_stateToV {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (optR : Option (CryptoGames.SM.RecvResult (Plain ℓ)))
    (s_ad : CliAdapterState S) (i : ℕ) (inst : BHAdapterInstMeta S)
    (c : Bytes) (m : CryptoVerification.E2E.PreKeyMessageFields)
    (hm : bhDecodePreKeyMsgE c = some m) :
    bobUpdV (optR.map (recvResultEnc (ℓ := ℓ))) (cliAdapterStateToV (ℓ := ℓ) s_ad) i
        (instMetaToV (ℓ := ℓ) inst) m.regId =
      cliAdapterStateToV (ℓ := ℓ) (bhShallowBobUpdate s_ad i inst c optR) := by
  rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩
  · rfl
  · rfl
  · dsimp only [Option.map, recvResultEnc, bobUpdV, bhShallowBobUpdate,
      bhShallowUpdateInstMeta, cliAdapterStateToV, instMetaToV]
    rw [hm]
    congr 1
    funext j
    by_cases hji : j = i <;> simp [hji]

private theorem eval_cliAliceUpdateStateExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (σVar : Var (.opt (recvResultT (ℓ := ℓ)) :: Γ) (cliAdapterStateTy S ℓ))
    (idxVar : Var (.opt (recvResultT (ℓ := ℓ)) :: Γ) .nat)
    (v : (Ty.opt (recvResultT (ℓ := ℓ))).denote) (ρ : Env Γ) :
    (cliAliceUpdateStateExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT) σVar idxVar).eval
        (.cons v ρ) =
      aliceUpdV v ((Expr.var (O := e2eAdapterOps ℓ decT encT) σVar).eval (.cons v ρ))
        ((Expr.var (O := e2eAdapterOps ℓ decT encT) idxVar).eval (.cons v ρ)) := by
  rcases v with _ | ⟨_ | _⟩ <;> rfl

private theorem eval_cliBobUpdateStateExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (σVar : Var (.opt (recvResultT (ℓ := ℓ)) :: Γ) (cliAdapterStateTy S ℓ))
    (idxVar : Var (.opt (recvResultT (ℓ := ℓ)) :: Γ) .nat)
    (instVar : Var (.opt (recvResultT (ℓ := ℓ)) :: Γ) (adapterInstMetaT (ℓ := ℓ)))
    (mRegIdVar : Var (.opt (recvResultT (ℓ := ℓ)) :: Γ) U32)
    (v : (Ty.opt (recvResultT (ℓ := ℓ))).denote) (ρ : Env Γ) :
    (cliBobUpdateStateExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
        σVar idxVar instVar mRegIdVar).eval (.cons v ρ) =
      bobUpdV v ((Expr.var (O := e2eAdapterOps ℓ decT encT) σVar).eval (.cons v ρ))
        ((Expr.var (O := e2eAdapterOps ℓ decT encT) idxVar).eval (.cons v ρ))
        ((Expr.var (O := e2eAdapterOps ℓ decT encT) instVar).eval (.cons v ρ))
        ((Expr.var (O := e2eAdapterOps ℓ decT encT) mRegIdVar).eval (.cons v ρ)) := by
  rcases v with _ | ⟨_ | _⟩ <;> rfl

private theorem comp_eval_ite_of_eq {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
    {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    {b : Expr O Γ .bool} {c d : Comp O I Γ t} {ρ : Env Γ} {v : Bool}
    (hb : b.eval ρ = v) :
    (Comp.ite b c d).eval ρ = (if v then c.eval ρ else d.eval ρ) := by
  rw [Comp.eval, hb]

private theorem comp_eval_caseOpt_of_eq {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {ι : Type}
    {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    {t u : Ty (e2eSig ℓ)} {e : Expr O Γ (.opt t)} {n : Comp O I Γ u}
    {s : Comp O I (t :: Γ) u} {ρ : Env Γ} {v : Option t.denote}
    (he : e.eval ρ = v) :
    (Comp.caseOpt e n s).eval ρ =
      Option.casesOn v (n.eval ρ) (fun x => s.eval (.cons x ρ)) := by
  rw [Comp.eval, he]; cases v <;> rfl

private theorem bhShallowBobUpdate_preserves {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (optR : Option (CryptoGames.SM.RecvResult (Plain ℓ)))
    {s_ad : CliAdapterState S}
    (hNoAck : ∀ k inst0, s_ad.1 k = some inst0 → inst0.aliceAcked = false)
    (i : ℕ) {inst : BHAdapterInstMeta S} (hInstAck : inst.aliceAcked = false) (c : Bytes) :
    (∀ k inst0, (bhShallowBobUpdate s_ad i inst c optR).1 k = some inst0 →
      inst0.aliceAcked = false) ∧
    (bhShallowBobUpdate s_ad i inst c optR).2.2 = s_ad.2.2 := by
  rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩
  · exact ⟨hNoAck, rfl⟩
  · exact ⟨hNoAck, rfl⟩
  · refine ⟨?_, rfl⟩
    intro k inst0 hk
    dsimp only [bhShallowBobUpdate] at hk
    by_cases hki : k = i
    · simp only [hki, ↓reduceIte] at hk
      injection hk with hk'
      rw [← hk']
      simp [bhShallowUpdateInstMeta, hInstAck]
    · simp only [hki, ↓reduceIte] at hk
      exact hNoAck k inst0 hk

private def StepCoupledEq {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    (C : Crypto) (K : MlKem)
    (c_hon : ProbComp ((α × (cliAdapterStateTy S ℓ).denote) × DrvLogState S ℓ))
    (c_ref : ProbComp ((α × CliAdapterState S) × DrvLogState S ℓ)) : Prop :=
  c_hon = (fun p => ((p.1.1, cliAdapterStateToV (ℓ := ℓ) p.1.2), p.2)) <$> c_ref ∧
  ∀ out ∈ support c_ref, AdapterCouplingInv C K out.1.2 out.2.1

private def EvalArmHon {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (t : (bhGameSpec S ℓ (BitVec 512)).Domain)
    (c_hon : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      ((e2eBhAdapterCodec S ℓ).R.denote × (cliAdapterStateTy S ℓ).denote))
    (σ_log : DrvLogState S ℓ) :
    ProbComp (((bhGameSpec S ℓ (BitVec 512)).Range t × (cliAdapterStateTy S ℓ).denote) ×
      DrvLogState S ℓ) :=
  (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
    (c_hon >>= fun p => pure ((e2eBhAdapterCodec S ℓ).rdec t p.1, p.2))).run σ_log

private def EvalArmRef {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (t : (bhGameSpec S ℓ (BitVec 512)).Domain)
    (c_ref : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      ((bhGameSpec S ℓ (BitVec 512)).Range t × CliAdapterState S))
    (σ_log : DrvLogState S ℓ) :
    ProbComp (((bhGameSpec S ℓ (BitVec 512)).Range t × CliAdapterState S) ×
      DrvLogState S ℓ) :=
  (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT) c_ref).run σ_log

private theorem run_simulateQ_drv_lift_query {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query q)) =
      cliE2EDrvImplWithLogState P ki C K qep decT encT q := by
  simp only [simulateQ_query, OracleSpec.query_def]
  dsimp only [OracleQuery.cont, OracleQuery.input]
  exact id_map _

private theorem run_simulateQ_drv_sm {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (σ_e2e : BHE2EDrvState S ℓ) (log : List (BitVec 512)) :
    (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (.inr (.inr ⟨i, sq⟩))))).run
      (σ_e2e, log) =
    (WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i sq) >>= fun p =>
      pure (CryptoVerification.E2E.bhUnpackSmResp sq p.1.1, (p.1.2, log ++ p.2))) := by
  rw [run_simulateQ_drv_lift_query]
  unfold cliE2EDrvImplWithLogState
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]

private theorem run_simulateQ_drv_ctl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (sid : SignalPqxdh.SessionId S) (σ_e2e : BHE2EDrvState S ℓ) (log : List (BitVec 512)) :
    (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
          (.inr (.inl (.inr (.startDR sid))))))).run (σ_e2e, log) =
      (CryptoVerification.E2E.compositionLocalStart ki C K (some σ_e2e.b) σ_e2e sid >>= fun p =>
        pure (p.1, (p.2, log))) := by
  rw [run_simulateQ_drv_lift_query]
  unfold cliE2EDrvImplWithLogState
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]

private theorem run_simulateQ_drv_ki {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (kq : SignalPqxdh.KeyIndQuery S) (σ_e2e : BHE2EDrvState S ℓ) (log : List (BitVec 512)) :
    (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
          (.inr (.inl (.inl kq)))))).run (σ_e2e, log) =
    (if !CryptoVerification.E2E.bhDrvKiQueryOk P σ_e2e.toModelDriverBase kq then
      pure (.noneResp, (σ_e2e, log))
     else if (match kq with
       | .corruptIK u => CryptoVerification.E2E.bhNoOpkRespPromoted σ_e2e.instMeta u
       | _ => false) then
      pure (.noneResp, (σ_e2e, log))
     else
      (ki kq).run σ_e2e.st >>= fun p =>
        pure (p.1, (CryptoVerification.E2E.bhE2EMirror { σ_e2e with st := p.2 } kq p.1, log))) := by
  rw [run_simulateQ_drv_lift_query]
  unfold cliE2EDrvImplWithLogState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases !CryptoVerification.E2E.bhDrvKiQueryOk P σ_e2e.toModelDriverBase kq
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases (match kq with
      | .corruptIK u => CryptoVerification.E2E.bhNoOpkRespPromoted σ_e2e.instMeta u
      | _ => false)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    · simp only [↓reduceIte, StateT.run_pure]
  · simp only [↓reduceIte, StateT.run_pure]

private theorem leaf_ret_none {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    {t : (bhGameSpec S ℓ (BitVec 512)).Domain}
    {rNone : (bhGameSpec S ℓ (BitVec 512)).Range t}
    (hr : (e2eBhAdapterCodec S ℓ).rdec t (.inr (none, (none, none))) = rNone) :
    StepCoupledEq C K
      (EvalArmHon P ki C K qep decT encT t
        (pure (.inr (none, (none, none)), cliAdapterStateToV (ℓ := ℓ) s_ad)) (σ_e2e, log))
      (EvalArmRef P ki C K qep decT encT t
        (pure (rNone, s_ad)) (σ_e2e, log)) := by
  refine ⟨?_, ?_⟩
  · unfold EvalArmHon EvalArmRef
    rw [pure_bind]
    change (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (pure ((e2eBhAdapterCodec S ℓ).rdec t (.inr (none, (none, none))),
        cliAdapterStateToV (ℓ := ℓ) s_ad))).run (σ_e2e, log) = _
    rw [hr]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  · unfold EvalArmRef
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    rintro out rfl
    exact hInv

private theorem leaf_ij_discard {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    {t : (bhGameSpec S ℓ (BitVec 512)).Domain}
    {rNone : (bhGameSpec S ℓ (BitVec 512)).Range t}
    (hr : (e2eBhAdapterCodec S ℓ).rdec t (.inr (none, (none, none))) = rNone)
    (i : ℕ) (bP : Bool) (wHon wRef : Bytes)
    (hStepEq : WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i
        (.inl (.inr (boolToParty bP, wHon)))) =
      WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i
        (.inl (.inr (boolToParty bP, wRef))))) :
    StepCoupledEq C K
      (EvalArmHon P ki C K qep decT encT t
        ((Option.map (recvResultEnc (ℓ := ℓ)) <$>
          (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inr (boolToParty bP, wHon))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _)) >>= fun _ =>
          pure (.inr (none, (none, none)), cliAdapterStateToV (ℓ := ℓ) s_ad)) (σ_e2e, log))
      (EvalArmRef P ki C K qep decT encT t
        (bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := BitVec 512)
          (.inr ⟨i, .inl (.inr (boolToParty bP, wRef))⟩) >>= fun _ =>
          pure (rNone, s_ad)) (σ_e2e, log)) := by
  unfold EvalArmHon EvalArmRef bhShallowQueryTarget
  have hr' : ∀ sV : (cliAdapterStateTy S ℓ).denote,
      ((pure (.inr (none, (none, none)), sV) :
        OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
          ((e2eBhAdapterCodec S ℓ).R.denote × (cliAdapterStateTy S ℓ).denote)) >>= fun p =>
        pure ((e2eBhAdapterCodec S ℓ).rdec t p.1, p.2)) =
      pure (rNone, sV) := fun sV => by
    rw [pure_bind]
    change (pure ((e2eBhAdapterCodec S ℓ).rdec t (.inr (none, (none, none))), sV) :
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _) = _
    rw [hr]
  rw [bind_assoc]
  simp_rw [hr']
  simp only [bind_map_left, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [run_simulateQ_drv_sm, run_simulateQ_drv_sm, hStepEq]
  simp only [bind_assoc, pure_bind]
  refine ⟨?_, ?_⟩
  · simp only [map_bind, map_pure]
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    rintro _ ⟨⟨⟨sr, σ'⟩, w⟩, hout, rfl⟩
    exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hInv.no_ack rfl i _
      (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)

private theorem leaf_ij_keep {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p0 : Party) (c0 : Bytes)
    (bP : Bool) (wHon wRef : Bytes)
    (hStepEq : WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i
        (.inl (.inr (boolToParty bP, wHon)))) =
      WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i
        (.inl (.inr (boolToParty bP, wRef))))) :
    StepCoupledEq C K
      (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inr (p0, c0))⟩)
        ((Option.map (recvResultEnc (ℓ := ℓ)) <$>
          (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inr (boolToParty bP, wHon))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _)) >>= fun v =>
          pure (.inr (none, (v, none)), cliAdapterStateToV (ℓ := ℓ) s_ad)) (σ_e2e, log))
      (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inr (p0, c0))⟩)
        (bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := BitVec 512)
          (.inr ⟨i, .inl (.inr (boolToParty bP, wRef))⟩) >>= fun optRr =>
          pure (optRr, s_ad)) (σ_e2e, log)) := by
  unfold EvalArmHon EvalArmRef bhShallowQueryTarget
  dsimp only [e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
  simp only [bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_simulateQ_drv_sm, run_simulateQ_drv_sm, hStepEq]
  simp only [bind_assoc, pure_bind]
  refine ⟨?_, ?_⟩
  · simp only [map_bind, map_pure]
    congr 1; funext ⟨⟨⟨_, optR, _⟩, σ'⟩, w⟩
    rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩ <;> rfl
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    rintro _ ⟨⟨⟨sr, σ'⟩, w⟩, hout, rfl⟩
    exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hInv.no_ack rfl i _
      (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)

private theorem leaf_ij_alice_ack {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p0 : Party) (c0 : Bytes)
    (wHon wRef : Bytes)
    (hStepEq : WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i
        (.inl (.inr (.A, wHon)))) =
      WriterT.run (bhE2EStepLocalSmCoinLogged C K qep decT encT σ_e2e i
        (.inl (.inr (.A, wRef))))) :
    StepCoupledEq C K
      (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inr (p0, c0))⟩)
        ((Option.map (recvResultEnc (ℓ := ℓ)) <$>
          (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inr (.A, wHon))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _)) >>= fun v =>
          pure (.inr (none, (v, none)),
            aliceUpdV v (cliAdapterStateToV (ℓ := ℓ) s_ad) i)) (σ_e2e, log))
      (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inr (p0, c0))⟩)
        (bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := BitVec 512)
          (.inr ⟨i, .inl (.inr (.A, wRef))⟩) >>= fun optRr =>
          pure (optRr, bhShallowAliceUpdate s_ad i optRr)) (σ_e2e, log)) := by
  unfold EvalArmHon EvalArmRef bhShallowQueryTarget
  dsimp only [e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
  simp only [bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_simulateQ_drv_sm, run_simulateQ_drv_sm, hStepEq]
  simp only [bind_assoc, pure_bind]
  refine ⟨?_, ?_⟩
  · simp only [map_bind, map_pure]
    congr 1; funext ⟨⟨⟨_, optR, _⟩, σ'⟩, w⟩
    rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩ <;> rfl
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    rintro _ ⟨⟨⟨sr, σ'⟩, w⟩, hout, rfl⟩
    obtain ⟨hNoAck', hDrv'⟩ := bhShallowAliceUpdate_preserves _ hInv.no_ack i
    exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hNoAck' hDrv' i _
      (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)

private theorem leaf_dl_keep {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p0 : Party) (c0 : Bytes)
    (bP : Bool) (w : Bytes) :
    StepCoupledEq C K
      (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inr (p0, c0)))⟩)
        ((Option.map (recvResultEnc (ℓ := ℓ)) <$>
          (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inl (.inr (boolToParty bP, w)))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _)) >>= fun v =>
          pure (.inr (none, (v, none)), cliAdapterStateToV (ℓ := ℓ) s_ad)) (σ_e2e, log))
      (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inr (p0, c0)))⟩)
        (bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := BitVec 512)
          (.inr ⟨i, .inl (.inl (.inr (boolToParty bP, w)))⟩) >>= fun optRr =>
          pure (optRr, s_ad)) (σ_e2e, log)) := by
  unfold EvalArmHon EvalArmRef bhShallowQueryTarget
  dsimp only [e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
  simp only [bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_simulateQ_drv_sm]
  simp only [bind_assoc, pure_bind]
  refine ⟨?_, ?_⟩
  · simp only [map_bind, map_pure]
    congr 1; funext ⟨⟨⟨_, optR, _⟩, σ'⟩, _⟩
    rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩ <;> rfl
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    rintro _ ⟨⟨⟨sr, σ'⟩, _⟩, hout, rfl⟩
    exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hInv.no_ack rfl i _
      (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)

private theorem leaf_dl_alice_ack {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p0 : Party) (c0 : Bytes) (w : Bytes) :
    StepCoupledEq C K
      (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inr (p0, c0)))⟩)
        ((Option.map (recvResultEnc (ℓ := ℓ)) <$>
          (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inl (.inr (.A, w)))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _)) >>= fun v =>
          pure (.inr (none, (v, none)),
            aliceUpdV v (cliAdapterStateToV (ℓ := ℓ) s_ad) i)) (σ_e2e, log))
      (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inr (p0, c0)))⟩)
        (bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := BitVec 512)
          (.inr ⟨i, .inl (.inl (.inr (.A, w)))⟩) >>= fun optRr =>
          pure (optRr, bhShallowAliceUpdate s_ad i optRr)) (σ_e2e, log)) := by
  unfold EvalArmHon EvalArmRef bhShallowQueryTarget
  dsimp only [e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
  simp only [bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_simulateQ_drv_sm]
  simp only [bind_assoc, pure_bind]
  refine ⟨?_, ?_⟩
  · simp only [map_bind, map_pure]
    congr 1; funext ⟨⟨⟨_, optR, _⟩, σ'⟩, _⟩
    rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩ <;> rfl
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    rintro _ ⟨⟨⟨sr, σ'⟩, _⟩, hout, rfl⟩
    obtain ⟨hNoAck', hDrv'⟩ := bhShallowAliceUpdate_preserves _ hInv.no_ack i
    exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hNoAck' hDrv' i _
      (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)

private theorem leaf_dl_bob_upd {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p0 : Party) (c : Bytes)
    {inst : BHAdapterInstMeta S} (hInst : s_ad.1 i = some inst)
    {m : CryptoVerification.E2E.PreKeyMessageFields} (hm : bhDecodePreKeyMsgE c = some m) :
    StepCoupledEq C K
      (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inr (p0, c)))⟩)
        ((Option.map (recvResultEnc (ℓ := ℓ)) <$>
          (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
            (.inr (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩))) :
            OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) _)) >>= fun v =>
          pure (.inr (none, (v, none)),
            bobUpdV v (cliAdapterStateToV (ℓ := ℓ) s_ad) i (instMetaToV (ℓ := ℓ) inst) m.regId))
        (σ_e2e, log))
      (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inr (p0, c)))⟩)
        (bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := BitVec 512)
          (.inr ⟨i, .inl (.inl (.inr (.B, c)))⟩) >>= fun optRr =>
          pure (optRr, bhShallowBobUpdate s_ad i inst c optRr))
        (σ_e2e, log)) := by
  unfold EvalArmHon EvalArmRef bhShallowQueryTarget
  dsimp only [e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
  simp only [bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_simulateQ_drv_sm]
  simp only [bind_assoc, pure_bind]
  refine ⟨?_, ?_⟩
  · simp only [map_bind, map_pure]
    congr 1; funext ⟨⟨⟨_, optR, _⟩, σ'⟩, _⟩
    dsimp only [CryptoVerification.E2E.bhUnpackSmResp]
    rw [bobUpd_stateToV optR s_ad i inst c m hm]
    rcases optR with _ | ⟨⟩ | ⟨_, _, _⟩ <;> rfl
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    rintro _ ⟨⟨⟨sr, σ'⟩, _⟩, hout, rfl⟩
    obtain ⟨hNoAck', hDrv'⟩ :=
      bhShallowBobUpdate_preserves _ hInv.no_ack i (hInv.no_ack i inst hInst) c
    exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hNoAck' hDrv' i _
      (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)

private theorem bhBaseMirror_noneResp {S : SignalPqxdh.Setup} (d : ModelDriverBase S)
    (kq : SignalPqxdh.KeyIndQuery S) :
    bhBaseMirror d kq .noneResp = d := by
  cases kq <;> rfl

private theorem step_eq_unif {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e) (n : ℕ) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT (.inl n)).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT (.inl n)).run s_ad).run
        (σ_e2e, log)) := by
  change StepCoupledEq C K
    ((do
      let x ← simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inl n))
      pure (x, cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
    ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (do
        let u ← query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inl n)
        pure (u, s_ad))).run (σ_e2e, log))
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  have hq :
      (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inl n))).run
        (σ_e2e, log) =
      ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun r =>
        pure (r, (σ_e2e, log))) := by
    simp [cliE2EDrvImplWithLogState, StateT.run_monadLift, monadLift_self]
  rw [hq]
  refine ⟨?_, ?_⟩
  · simp only [bind_assoc, pure_bind, map_bind, map_pure]
  · simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    rintro _ ⟨a, -, rfl⟩
    exact hInv

private theorem step_eq_ki {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (kq : SignalPqxdh.KeyIndQuery S) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT (.inr (.inl (.inl kq)))).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT (.inr (.inl (.inl kq)))).run
        s_ad).run (σ_e2e, log)) := by
  change StepCoupledEq C K
    (EvalArmHon P ki C K qep decT encT (.inl (.inl kq))
      ((cliAdapterKiOrCtlArm S ℓ decT encT).eval
        (.cons (.inl (keyIndQenc kq))
          (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad)
            (.cons (.inl (.inl (keyIndQenc kq))) .nil)))) (σ_e2e, log))
    (EvalArmRef P ki C K qep decT encT (.inl (.inl kq))
      (bhShallowAdapterGameStep (.inl (.inl kq)) s_ad) (σ_e2e, log))
  unfold EvalArmHon EvalArmRef
  dsimp only [cliAdapterKiOrCtlArm, cliQuery, bhShallowAdapterGameStep, bhShallowQueryTarget,
    bhShallowStepMirrorGuard, Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1,
    Expr.v2, Expr.v3, e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec]
  rw [keyIndQdec_keyIndQenc]
  simp only [bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_simulateQ_drv_ki]
  have hMirEval : ∀ kr : SignalPqxdh.KeyIndResponse,
      (stepBaseMirrorExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
        (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
          cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
        (.snd (.snd (.var (.succ (.succ (.succ .zero))))))
        (.var (.succ .zero)) (.var .zero)).eval
        (.cons (keyIndRenc kr) (.cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
          (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad)
            (.cons (.inl (.inl (keyIndQenc kq))) .nil))))) =
      drvMirrorToV (ℓ := ℓ) (bhBaseMirror s_ad.2.2 kq kr) := by
    intro kr
    rw [eval_stepBaseMirrorExpr (d := s_ad.2.2) (hdrv := rfl)]
    dsimp only [Expr.eval, env_get_zero, env_get_succ]
    rw [keyIndQdec_keyIndQenc, keyIndRdec_keyIndRenc]
  cases hok : !CryptoVerification.E2E.bhDrvKiQueryOk P σ_e2e.toModelDriverBase kq
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hprom : (match kq with
      | .corruptIK u => CryptoVerification.E2E.bhNoOpkRespPromoted σ_e2e.instMeta u
      | _ => false)
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      refine ⟨?_, ?_⟩
      · simp only [map_bind, map_pure]
        congr 1
        funext ⟨kr, st'⟩
        dsimp only
        rw [hMirEval kr, keyIndRdec_keyIndRenc]
        rfl
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        rintro _ ⟨⟨kr, st'⟩, hStep, rfl⟩
        refine ⟨hInv.no_ack, ?_, mirrorKiInv_bhBaseMirror hKi hInv.mirror_ki kq kr hStep,
          Computational.Proofs.E2E.Dsl.SmReachInv.drvSmReachInv_mirror
            (hInv.reach : Computational.Proofs.E2E.Dsl.SmReachInv.DrvSmReachInv C K
              { σ_e2e with st := st' }) kq kr,
          drvNoWhisperTrans_mirror (hInv.no_whisp : DrvNoWhisperTrans { σ_e2e with st := st' })
            kq kr⟩
        dsimp only [CryptoVerification.E2E.bhE2EMirror]
        rw [hInv.drv_eq]
    · simp only [↓reduceIte, pure_bind]
      rw [hMirEval .noneResp, keyIndRdec_keyIndRenc, bhBaseMirror_noneResp]
      refine ⟨?_, ?_⟩
      · simp only [map_pure]
        rfl
      · simp only [support_pure, Set.mem_singleton_iff]
        rintro out rfl
        exact hInv
  · simp only [↓reduceIte, pure_bind]
    rw [hMirEval .noneResp, keyIndRdec_keyIndRenc, bhBaseMirror_noneResp]
    refine ⟨?_, ?_⟩
    · simp only [map_pure]
      rfl
    · simp only [support_pure, Set.mem_singleton_iff]
      rintro out rfl
      exact hInv

set_option linter.unusedSimpArgs false in
private theorem step_eq_ctl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (sid : SignalPqxdh.SessionId S) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT (.inr (.inl (.inr (.startDR sid))))).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT
          (.inr (.inl (.inr (.startDR sid))))).run
        s_ad).run (σ_e2e, log)) := by
  change StepCoupledEq C K
    (EvalArmHon P ki C K qep decT encT (.inl (.inr (.startDR sid)))
      ((cliAdapterKiOrCtlArm S ℓ decT encT).eval
        (.cons (.inr (sidV sid))
          (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad)
            (.cons (.inl (.inr (sidV sid))) .nil)))) (σ_e2e, log))
    (EvalArmRef P ki C K qep decT encT (.inl (.inr (.startDR sid)))
      (bhShallowAdapterGameStep (.inl (.inr (.startDR sid))) s_ad) (σ_e2e, log))
  unfold EvalArmHon EvalArmRef
  dsimp only [cliAdapterKiOrCtlArm, cliQuery, bhShallowAdapterGameStep, bhShallowQueryTarget,
    Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec]
  rw [sidOfV_sidV]
  simp only [bind_assoc, bind_map_left, simulateQ_bind, StateT.run_bind]
  rw [run_simulateQ_drv_ctl]
  simp only [bind_assoc, pure_bind]
  have hGrd : ∀ idx : ℕ,
      (guardPromoteExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
        (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
          cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
        (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
        (.var (.succ (.succ .zero)))).eval
        (.cons idx (.cons (some idx) (.cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad) (.cons (.inl (.inr (sidV sid))) .nil)))))) =
      ((bhShallowStepMirrorGuard (.inr (s_ad.2.2, sid))).2).map (instMetaToV (ℓ := ℓ)) := by
    intro idx
    rw [eval_guardPromoteExpr _ _ s_ad.2.2 _ rfl
      hInv.mirror_ki.prins_length_le hInv.mirror_ki.bundles_length_le
      hInv.mirror_ki.opks_length_le hInv.mirror_ki.sends_length_le]
    dsimp only [Expr.eval, env_get_zero, env_get_succ]
    rw [sidOfV_sidV]
  have hGuardNoAck : ∀ inst : BHAdapterInstMeta S,
      (bhShallowStepMirrorGuard (.inr (s_ad.2.2, sid))).2 = some inst →
      inst.aliceAcked = false := by
    intro inst hg
    dsimp only [bhShallowStepMirrorGuard] at hg
    split at hg
    · cases hg
    · split at hg
      · cases hg
      · split_ifs at hg
        injection hg with hg'; rw [← hg']
  refine ⟨?_, ?_⟩
  · simp only [map_bind]
    congr 1
    funext ⟨optIdx, σ'⟩
    cases optIdx with
    | none =>
      dsimp only [Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v3]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
    | some idx =>
      dsimp only [Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v4,
        Expr.v5]
      rw [hGrd idx]
      cases hG : (bhShallowStepMirrorGuard (.inr (s_ad.2.2, sid))).2 with
      | none =>
        dsimp only [Option.map]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      | some inst =>
        simp (config := { failIfUnchanged := false }) only [Option.map, Comp.eval, Expr.eval,
          Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v5,
          pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        have hTbl : (fun j => if j = idx then some (instMetaToV (ℓ := ℓ) inst)
            else Option.map (instMetaToV (ℓ := ℓ)) (s_ad.1 j)) =
          (fun k => Option.map (instMetaToV (ℓ := ℓ))
            (if k = idx then some inst else s_ad.1 k)) := by
          funext j; by_cases hj : j = idx <;> simp [hj]
        congr 2
        dsimp only [cliAdapterStateToV]
        exact congrArg (fun f => (some idx, f, s_ad.2.1, drvMirrorToV (ℓ := ℓ) s_ad.2.2)) hTbl
  · simp only [mem_support_bind_iff]
    rintro out ⟨⟨optIdx, σ'⟩, hout, hout2⟩
    obtain ⟨hDrv', hMir'⟩ :=
      compositionLocalStart_base_mirror hKi C K (some σ_e2e.b) hInv.drv_eq hInv.mirror_ki sid hout
    have hReach' :=
      Computational.Proofs.E2E.Dsl.SmReachInv.drvSmReachInv_compositionLocalStart ki C K
        (some σ_e2e.b) hInv.reach sid hout
    have hNW' := drvNoWhisperTrans_compositionLocalStart ki C K (some σ_e2e.b) hInv.no_whisp sid
      hout
    cases optIdx with
    | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout2
      subst hout2
      exact ⟨hInv.no_ack, hDrv', hMir', hReach', hNW'⟩
    | some idx =>
      dsimp only at hout2
      cases hG : (bhShallowStepMirrorGuard (.inr (s_ad.2.2, sid))).2 with
      | none =>
        rw [hG] at hout2
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout2
        subst hout2
        exact ⟨hInv.no_ack, hDrv', hMir', hReach', hNW'⟩
      | some inst =>
        rw [hG] at hout2
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout2
        subst hout2
        refine ⟨?_, hDrv', hMir', hReach', hNW'⟩
        intro k inst0 hk
        dsimp only at hk
        by_cases hki : k = idx
        · simp only [hki, ↓reduceIte] at hk
          injection hk with hk'; rw [← hk']; exact hGuardNoAck inst hG
        · simp only [hki, ↓reduceIte] at hk
          exact hInv.no_ack k inst0 hk

private theorem step_eq_tr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p : Party) (m : Plain ℓ) (optR : Option (BitVec 512)) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT
          (.inr (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, optR))))⟩))).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT
          (.inr (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, optR))))⟩))).run
        s_ad).run (σ_e2e, log)) := by
  change StepCoupledEq C K
    (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, optR))))⟩)
      ((cliAdapterTrArm S ℓ decT encT).eval
        (.cons (partyToBool p, (m, optR))
          (.cons (i, smQenc (.inl (.inl (.inl (.inl (p, m, optR))))))
            (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad)
              (.cons (.inr (i, smQenc (.inl (.inl (.inl (.inl (p, m, optR))))))) .nil)))))
      (σ_e2e, log))
    (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, optR))))⟩)
      (bhShallowAdapterGameStep (.inr ⟨i, .inl (.inl (.inl (.inl (p, m, optR))))⟩) s_ad)
      (σ_e2e, log))
  dsimp only [cliAdapterTrArm, cliQuery, bhShallowAdapterGameStep, bhShallowQueryTarget,
    Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5]
  cases hInst : s_ad.1 i with
  | none =>
    have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = none := by
      simp [cliAdapterStateToV, hInst]
    rw [hInstV]
    dsimp only
    exact leaf_ret_none P ki C K qep decT encT hInv rfl
  | some inst =>
    have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = some (instMetaToV (ℓ := ℓ) inst) := by
      simp [cliAdapterStateToV, hInst]
    rw [hInstV]
    unfold EvalArmHon EvalArmRef
    dsimp only [Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
      Expr.v3, Expr.v4, Expr.v5, e2eBhAdapterIface, e2eAdapterIface]
    rw [boolToParty_partyToBool, partyEnc_eq_partyToBool]
    simp only [bind_assoc, bind_map_left, simulateQ_bind, StateT.run_bind]
    rw [run_simulateQ_drv_sm]
    simp only [bind_assoc, pure_bind]
    refine ⟨?_, ?_⟩
    · refine probComp_bind_eq_map_bind _ _ fun ⟨⟨⟨optCt, r2, r3⟩, σ'⟩, w⟩ hout => ?_
      cases optCt with
      | none =>
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp, Comp.eval, Expr.eval,
          adapterNoneSmRespExpr, env_get_zero, env_get_succ, Expr.v4,
          e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      | some ct =>
        have hlen := bhE2EStepLocalSm_tr_len_le C K qep decT encT σ_e2e i p m optR
          (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)
        have hw := wrapSendWire_eq_of_len_le (ℓ := ℓ) inst
          (hInv.no_ack i inst hInst) (partyToBool p) (s_ad.2.1 i) hlen
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp, Comp.eval, Expr.eval,
          eval_adapterPureOp, env_get_zero, env_get_succ, Expr.v0, Expr.v2, Expr.v3, Expr.v4,
          Expr.v5, instMetaToV, cliAdapterStateToV, e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        exact congrArg (fun wire => pure ((some wire, cliAdapterStateToV (ℓ := ℓ) s_ad),
          (σ', log ++ w))) hw
    · simp only [mem_support_bind_iff]
      rintro out ⟨⟨⟨⟨optCt, r2, r3⟩, σ'⟩, w⟩, hout, hout2⟩
      cases optCt <;> {
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp] at hout2
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout2
        subst hout2
        exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hInv.no_ack rfl i _
          (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)
      }

private theorem step_eq_ch {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT
          (.inr (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, optR))))⟩))).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT
          (.inr (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, optR))))⟩))).run
        s_ad).run (σ_e2e, log)) := by
  let chArgs := (partyToBool p, (m0, (m1, optR)))
  change StepCoupledEq C K
    (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, optR))))⟩)
      ((cliAdapterChArm S ℓ decT encT).eval
        (.cons chArgs (.cons (.inl chArgs)
          (.cons (i, smQenc (.inl (.inl (.inl (.inr (p, m0, m1, optR))))))
            (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad)
              (.cons (.inr (i, smQenc (.inl (.inl (.inl (.inr (p, m0, m1, optR))))))) .nil))))))
      (σ_e2e, log))
    (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, optR))))⟩)
      (bhShallowAdapterGameStep (.inr ⟨i, .inl (.inl (.inl (.inr (p, m0, m1, optR))))⟩) s_ad)
      (σ_e2e, log))
  dsimp only [cliAdapterChArm, cliQuery, bhShallowAdapterGameStep, bhShallowQueryTarget,
    Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, Expr.v6]
  cases hInst : s_ad.1 i with
  | none =>
    have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = none := by
      simp [cliAdapterStateToV, hInst]
    rw [hInstV]
    dsimp only
    exact leaf_ret_none P ki C K qep decT encT hInv rfl
  | some inst =>
    have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = some (instMetaToV (ℓ := ℓ) inst) := by
      simp [cliAdapterStateToV, hInst]
    rw [hInstV]
    unfold EvalArmHon EvalArmRef
    dsimp only [Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
      Expr.v3, Expr.v4, Expr.v5, Expr.v6, e2eBhAdapterIface, e2eAdapterIface, chArgs]
    rw [boolToParty_partyToBool, partyEnc_eq_partyToBool]
    simp only [bind_assoc, bind_map_left, simulateQ_bind, StateT.run_bind]
    rw [run_simulateQ_drv_sm]
    simp only [bind_assoc, pure_bind]
    refine ⟨?_, ?_⟩
    · refine probComp_bind_eq_map_bind _ _ fun ⟨⟨⟨optCt, r2, r3⟩, σ'⟩, w⟩ hout => ?_
      cases optCt with
      | none =>
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp, Comp.eval, Expr.eval,
          adapterNoneSmRespExpr, env_get_zero, env_get_succ, Expr.v5,
          e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      | some ct =>
        have hlen := bhE2EStepLocalSm_ch_len_le C K qep decT encT σ_e2e i p m0 m1 optR
          (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)
        have hw := wrapSendWire_eq_of_len_le (ℓ := ℓ) inst
          (hInv.no_ack i inst hInst) (partyToBool p) (s_ad.2.1 i) hlen
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp, Comp.eval, Expr.eval,
          eval_adapterPureOp, env_get_zero, env_get_succ, Expr.v0, Expr.v2, Expr.v3, Expr.v5,
          Expr.v6, instMetaToV, cliAdapterStateToV, e2eBhAdapterCodec, e2eAdapterCodec, smRdec]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        exact congrArg (fun wire => pure ((some wire, cliAdapterStateToV (ℓ := ℓ) s_ad),
          (σ', log ++ w))) hw
    · simp only [mem_support_bind_iff]
      rintro out ⟨⟨⟨⟨optCt, r2, r3⟩, σ'⟩, w⟩, hout, hout2⟩
      cases optCt <;> {
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp] at hout2
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout2
        subst hout2
        exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hInv.no_ack rfl i _
          (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)
      }

private theorem step_eq_cr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p : Party) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT (.inr (.inr ⟨i, .inr p⟩))).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT (.inr (.inr ⟨i, .inr p⟩))).run
        s_ad).run (σ_e2e, log)) := by
  let b0 := partyToBool p
  change StepCoupledEq C K
    (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inr p⟩)
      ((adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
          (drvMirrorTy S ℓ)).eval
        (.cons b0 (.cons (.inr b0) (.cons (.inr (.inr b0)) (.cons (.inr (.inr (.inr b0)))
          (.cons (i, smQenc (.inr p))
            (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad)
              (.cons (.inr (i, smQenc (.inr p))) .nil)))))))) (σ_e2e, log))
    (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inr p⟩)
      (bhShallowAdapterGameStep (.inr ⟨i, .inr p⟩) s_ad) (σ_e2e, log))
  dsimp only [adapterCrArm, bhShallowAdapterGameStep, bhShallowQueryTarget,
    Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v4,
    Expr.v5]
  cases hInst : s_ad.1 i with
  | none =>
    have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = none := by
      simp [cliAdapterStateToV, hInst]
    rw [hInstV]
    dsimp only
    exact leaf_ret_none P ki C K qep decT encT hInv rfl
  | some inst =>
    have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = some (instMetaToV (ℓ := ℓ) inst) := by
      simp [cliAdapterStateToV, hInst]
    rw [hInstV]
    unfold EvalArmHon EvalArmRef
    dsimp only [Comp.eval, Expr.eval, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
      Expr.v5, e2eBhAdapterIface, e2eAdapterIface, b0]
    rw [boolToParty_partyToBool]
    simp only [bind_assoc, bind_map_left, simulateQ_bind, StateT.run_bind]
    rw [run_simulateQ_drv_sm]
    simp only [bind_assoc, pure_bind]
    refine ⟨?_, ?_⟩
    · refine probComp_bind_eq_map_bind _ _ fun ⟨⟨⟨r1, r2, optG⟩, σ'⟩, w⟩ hout => ?_
      cases optG with
      | none =>
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp, Comp.eval, Expr.eval,
          adapterNoneSmRespExpr, env_get_zero, env_get_succ,
          e2eBhAdapterCodec, e2eAdapterCodec, smRdec, Option.map]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      | some g =>
        have hg := bhE2EStepLocalSm_cr_partyReachInv C K qep decT encT hInv.reach i p
          (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)
        have hEnc := encodeSessionRecord_instMetaToV_eq (ℓ := ℓ) inst g hg
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp, Comp.eval, Expr.eval,
          eval_adapterPureOp, E2EPureOp.eval, env_get_zero, env_get_succ,
          Expr.v0, Expr.v2, e2eBhAdapterCodec, e2eAdapterCodec, smRdec, Option.map]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        rw [hEnc]
        rfl
    · simp only [mem_support_bind_iff]
      rintro out ⟨⟨⟨⟨r1, r2, optG⟩, σ'⟩, w⟩, hout, hout2⟩
      cases optG <;> {
        dsimp only [CryptoVerification.E2E.bhUnpackSmResp] at hout2
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout2
        subst hout2
        exact adapterCouplingInv_of_sm_step C K qep decT encT hInv hInv.no_ack rfl i _
          (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hout)
      }

private theorem splitWhisperWire_eval_eq {ℓ : ℕ} (c : Bytes) :
    E2EPureOp.eval ℓ .splitWhisperWire c = bhShallowSplitWhisper c := by
  cases c <;> rfl

set_option linter.unusedSimpArgs false in
private theorem step_eq_dl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p : Party) (c : Bytes) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT
          (.inr (.inr ⟨i, .inl (.inl (.inr (p, c)))⟩))).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT
          (.inr (.inr ⟨i, .inl (.inl (.inr (p, c)))⟩))).run
        s_ad).run (σ_e2e, log)) := by
  let d1 := (partyToBool p, c)
  change StepCoupledEq C K
    (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inr (p, c)))⟩)
      ((cliAdapterDlArm S ℓ decT encT).eval
        (.cons d1 (.cons (.inl d1) (.cons (.inr (.inl d1))
          (.cons (i, smQenc (.inl (.inl (.inr (p, c)))))
            (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad)
              (.cons (.inr (i, smQenc (.inl (.inl (.inr (p, c)))))) .nil))))))) (σ_e2e, log))
    (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inl (.inr (p, c)))⟩)
      (bhShallowAdapterGameStep (.inr ⟨i, .inl (.inl (.inr (p, c)))⟩) s_ad) (σ_e2e, log))
  cases p
  ·
    simp (config := { failIfUnchanged := false }) only [cliAdapterDlArm, cliQuery,
      bhShallowAdapterGameStep, partyToBool, d1, Comp.eval, Expr.eval, eval_adapterPureOp,
      Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
      Expr.v6, Bool.false_eq_true, ite_true, ite_false]
    rw [splitWhisperWire_eval_eq c]
    cases hSplit : bhShallowSplitWhisper c with
    | none =>
      simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval, Env.get,
        env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
        eval_isEmptyBytesExpr, bh_split_wrapWhisperWire]
      cases hcEmp : c.isEmpty
      · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_true,
          ite_false, Comp.eval, Expr.eval, adapterNoneSmRespExpr, Env.get, env_get_zero,
          env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
        exact leaf_ret_none P ki C K qep decT encT hInv rfl
      · simp (config := { failIfUnchanged := false }) only [ite_true, ite_false, Comp.eval,
          Expr.eval, e2eBhAdapterIface, e2eAdapterIface, Env.get, env_get_zero, env_get_succ,
          Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
        exact leaf_dl_keep P ki C K qep decT encT hInv i .A c false c
    | some body =>
      simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval, Env.get,
        env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
        eval_isEmptyBytesExpr, bh_split_wrapWhisperWire]
      cases hbEmp : body.isEmpty
      · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_true,
          ite_false, Comp.eval, Expr.eval, eval_cliAliceUpdateStateExpr, e2eBhAdapterIface,
          e2eAdapterIface, Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
          Expr.v3, Expr.v4, Expr.v5, Expr.v6, boolToParty, pure_bind]
        exact leaf_dl_alice_ack P ki C K qep decT encT hInv i .A c body
      · simp (config := { failIfUnchanged := false }) only [ite_true, ite_false, Comp.eval,
          Expr.eval, adapterNoneSmRespExpr, Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1,
          Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
        exact leaf_ret_none P ki C K qep decT encT hInv rfl
  ·
    simp (config := { failIfUnchanged := false }) only [cliAdapterDlArm, cliQuery,
      bhShallowAdapterGameStep, partyToBool, d1, Comp.eval, Expr.eval, Env.get, env_get_zero,
      env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
      ite_true, ite_false]
    cases hInst : s_ad.1 i with
    | none =>
      have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = none := by
        simp [cliAdapterStateToV, hInst]
      rw [hInstV]
      dsimp only
      exact leaf_ret_none P ki C K qep decT encT hInv rfl
    | some inst =>
      have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = some (instMetaToV (ℓ := ℓ) inst) := by
        simp [cliAdapterStateToV, hInst]
      rw [hInstV]
      simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval, eval_adapterPureOp,
        bhShallowParsePreKey, Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
        Expr.v3, Expr.v4, Expr.v5, Expr.v6]
      rw [parsePreKeyWire_eval_eq]
      cases hm : bhDecodePreKeyMsgE c with
      | none =>
        simp (config := { failIfUnchanged := false }) only [Option.map, Comp.eval, Expr.eval,
          eval_adapterPureOp, Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
          Expr.v3, Expr.v4, Expr.v5, Expr.v6]
        rw [splitWhisperWire_eval_eq c]
        cases hSplit : bhShallowSplitWhisper c with
        | none =>
          simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval,
            eval_adapterPureOp, adapterNoneSmRespExpr, e2eBhAdapterIface, e2eAdapterIface,
            Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
            Expr.v5, Expr.v6]
          exact leaf_ij_discard P ki C K qep decT encT hInv rfl i true
            (E2EPureOp.eval ℓ .wrapWhisperWire c) (bhShallowWrapWhisper c)
            (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp i .B c)
        | some body =>
          simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval,
            eval_adapterPureOp, bhShallowParsePreKey, Env.get, env_get_zero, env_get_succ, Expr.v0,
            Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
          rw [parsePreKeyWire_eval_eq]
          cases hmBody : bhDecodePreKeyMsgE body with
          | none =>
            simp (config := { failIfUnchanged := false }) only [Option.map, Comp.eval, Expr.eval,
              Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
              Expr.v5, Expr.v6, eval_isEmptyBytesExpr, bh_split_wrapWhisperWire]
            cases hbEmp : body.isEmpty
            · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_true,
                ite_false, Comp.eval, Expr.eval, e2eBhAdapterIface, e2eAdapterIface, Env.get,
                env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
                Expr.v6]
              exact leaf_dl_keep P ki C K qep decT encT hInv i .B c true body
            · simp (config := { failIfUnchanged := false }) only [ite_true, ite_false, Comp.eval,
                Expr.eval, eval_adapterPureOp, adapterNoneSmRespExpr, e2eBhAdapterIface,
                e2eAdapterIface, Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
                Expr.v3, Expr.v4, Expr.v5, Expr.v6]
              exact leaf_ij_discard P ki C K qep decT encT hInv rfl i true
                (E2EPureOp.eval ℓ .wrapWhisperWire body) (bhShallowWrapWhisper body)
                (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp
                  i .B body)
          | some mBody =>
            simp (config := { failIfUnchanged := false }) only [Option.map, Comp.eval, Expr.eval,
              adapterNoneSmRespExpr, e2eBhAdapterIface, e2eAdapterIface, Env.get, env_get_zero,
              env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
            exact leaf_ij_discard P ki C K qep decT encT hInv rfl i true c c rfl
      | some m =>
        simp (config := { failIfUnchanged := false }) only [Option.map, Comp.eval, Expr.eval,
          Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
          Expr.v5, Expr.v6, eval_isEmptyBytesExpr, bh_split_wrapWhisperWire]
        cases hmEmp : m.inner.isEmpty
        · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_true,
            ite_false, Comp.eval, Expr.eval, eval_cliBobUpdateStateExpr, e2eBhAdapterIface,
            e2eAdapterIface, Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
            Expr.v3, Expr.v4, Expr.v5, Expr.v6, boolToParty, pure_bind]
          exact leaf_dl_bob_upd P ki C K qep decT encT hInv i .B c hInst hm
        · simp (config := { failIfUnchanged := false }) only [ite_true, ite_false, Comp.eval,
            Expr.eval, eval_adapterPureOp, adapterNoneSmRespExpr, e2eBhAdapterIface,
            e2eAdapterIface, Env.get, env_get_zero, env_get_succ, Expr.v0, Expr.v1, Expr.v2,
            Expr.v3, Expr.v4, Expr.v5, Expr.v6]
          exact leaf_ij_discard P ki C K qep decT encT hInv rfl i true
            (E2EPureOp.eval ℓ .wrapWhisperWire m.inner) (bhShallowWrapWhisper m.inner)
            (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp
              i .B m.inner)

set_option linter.unusedSimpArgs false in
private theorem step_eq_ij {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : AdapterCouplingInv C K s_ad σ_e2e)
    (i : ℕ) (p : Party) (c : Bytes) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT
          (.inr (.inr ⟨i, .inl (.inr (p, c))⟩))).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run (σ_e2e, log))
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT
          (.inr (.inr ⟨i, .inl (.inr (p, c))⟩))).run
        s_ad).run (σ_e2e, log)) := by
  let j1 := (partyToBool p, c)
  change StepCoupledEq C K
    (EvalArmHon P ki C K qep decT encT (.inr ⟨i, .inl (.inr (p, c))⟩)
      ((cliAdapterIjArm S ℓ decT encT).eval
        (.cons j1 (.cons (.inl j1) (.cons (.inr (.inl j1)) (.cons (.inr (.inr (.inl j1)))
          (.cons (i, smQenc (.inl (.inr (p, c))))
            (.cons (cliAdapterStateToV (ℓ := ℓ) s_ad)
              (.cons (.inr (i, smQenc (.inl (.inr (p, c))))) .nil)))))))) (σ_e2e, log))
    (EvalArmRef P ki C K qep decT encT (.inr ⟨i, .inl (.inr (p, c))⟩)
      (bhShallowAdapterGameStep (.inr ⟨i, .inl (.inr (p, c))⟩) s_ad) (σ_e2e, log))
  cases p
  ·
    dsimp only [cliAdapterIjArm, cliQuery, bhShallowAdapterGameStep, partyToBool, j1]
    rw [comp_eval_ite_of_eq (v := false) rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [comp_eval_caseOpt_of_eq (v := bhShallowSplitWhisper c)
      (by dsimp only [Expr.eval, eval_adapterPureOp, Env.get, Expr.v0]
          exact splitWhisperWire_eval_eq c)]
    cases hSplit : bhShallowSplitWhisper c with
    | none =>
      simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval,
        adapterNoneSmRespExpr, Env.get, Expr.v0, Expr.v5]
      exact leaf_ret_none P ki C K qep decT encT hInv rfl
    | some body =>
      dsimp only
      rw [comp_eval_ite_of_eq (v := decide (c.length ≤ stdinCapBytes) && shortCiphertext c)
        (by rw [eval_and_capOkBytesExpr_checkShort_none]; rfl)]
      cases hShort : (decide (c.length ≤ stdinCapBytes) && shortCiphertext c)
      · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_false,
          Comp.eval, Expr.eval, adapterNoneSmRespExpr, Env.get, Expr.v6]
        exact leaf_ret_none P ki C K qep decT encT hInv rfl
      · simp only [ite_true]
        rw [comp_eval_caseOpt_of_eq
          (v := (bhDecodePreKeyMsgE body).map fun m => (m.regId, (hdrV (ℓ := ℓ) (bhHdrOfPreKeyMsg m), m.inner)))
          (by dsimp only [Expr.eval, eval_adapterPureOp, Env.get, Expr.v0]
              exact parsePreKeyWire_eval_eq ℓ body)]
        dsimp (config := { failIfUnchanged := false }) only [bhShallowParsePreKey]
        cases hmBody : bhDecodePreKeyMsgE body with
        | none =>
          dsimp (config := { failIfUnchanged := false }) only [Option.map]
          rw [bh_split_wrapWhisperWire]
          rw [comp_eval_ite_of_eq (v := body.isEmpty)
            (by simp only [eval_isEmptyBytesExpr, Expr.eval, Env.get, Expr.v0])]
          cases hbEmp : body.isEmpty
          · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_false,
              Comp.eval, Expr.eval, eval_cliAliceUpdateStateExpr, e2eBhAdapterIface,
              e2eAdapterIface, Env.get, Expr.v0, Expr.v1, Expr.v5, boolToParty, pure_bind]
            exact leaf_ij_alice_ack P ki C K qep decT encT hInv i .A c body body rfl
          · simp (config := { failIfUnchanged := false }) only [ite_true, Comp.eval,
              Expr.eval, eval_adapterPureOp, e2eBhAdapterIface, e2eAdapterIface, Env.get,
              Expr.v0, Expr.v1, Expr.v5]
            exact leaf_ij_keep P ki C K qep decT encT hInv i .A c false
              (E2EPureOp.eval ℓ .wrapWhisperWire c) (bhShallowWrapWhisper c)
              (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp
                i .A c)
        | some mBody =>
          dsimp (config := { failIfUnchanged := false }) only [Option.map]
          simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval,
            eval_adapterPureOp, eval_cliAliceUpdateStateExpr, e2eBhAdapterIface, e2eAdapterIface,
            Env.get, Expr.v0, Expr.v2, Expr.v6, boolToParty, pure_bind]
          exact leaf_ij_alice_ack P ki C K qep decT encT hInv i .A c
            (E2EPureOp.eval ℓ .wrapWhisperWire body) (bhShallowWrapWhisper body)
            (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp
              i .A body)
  ·
    dsimp only [cliAdapterIjArm, cliQuery, bhShallowAdapterGameStep, partyToBool, j1]
    rw [comp_eval_ite_of_eq (v := true) rfl]
    simp only [ite_true]
    rw [comp_eval_caseOpt_of_eq (v := bhShallowSplitWhisper c)
      (by dsimp only [Expr.eval, eval_adapterPureOp, Env.get, Expr.v0]
          exact splitWhisperWire_eval_eq c)]
    cases hSplit : bhShallowSplitWhisper c with
    | none =>
      rw [comp_eval_caseOpt_of_eq
        (v := (bhDecodePreKeyMsgE c).map fun m => (m.regId, (hdrV (ℓ := ℓ) (bhHdrOfPreKeyMsg m), m.inner)))
        (by dsimp only [Expr.eval, eval_adapterPureOp, Env.get, Expr.v0]
            exact parsePreKeyWire_eval_eq ℓ c)]
      dsimp (config := { failIfUnchanged := false }) only [bhShallowParsePreKey]
      cases hm : bhDecodePreKeyMsgE c with
      | none =>
        dsimp (config := { failIfUnchanged := false }) only [Option.map]
        simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval,
          eval_adapterPureOp, adapterNoneSmRespExpr, e2eBhAdapterIface, e2eAdapterIface,
          Env.get, Expr.v0, Expr.v4, Expr.v6]
        exact leaf_ij_discard P ki C K qep decT encT hInv rfl i true
          (E2EPureOp.eval ℓ .wrapWhisperWire c) (bhShallowWrapWhisper c)
          (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp i .B c)
      | some m =>
        dsimp (config := { failIfUnchanged := false }) only [Option.map]
        rw [comp_eval_ite_of_eq
          (v := decide (c.length ≤ stdinCapBytes) && shortCiphertext c &&
            decide (m.inner.length + 2048 < 2 ^ 32))
          (by rw [eval_and_capOkBytesExpr_checkShort_some]; rfl)]
        cases hCapShort : (decide (c.length ≤ stdinCapBytes) && shortCiphertext c &&
            decide (m.inner.length + 2048 < 2 ^ 32))
        · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_false,
            Comp.eval, Expr.eval, eval_adapterPureOp, adapterNoneSmRespExpr,
            e2eBhAdapterIface, e2eAdapterIface, Env.get, Expr.v1, Expr.v5]
          exact leaf_ij_discard P ki C K qep decT encT hInv rfl i true
            (E2EPureOp.eval ℓ .wrapWhisperWire c) (bhShallowWrapWhisper c)
            (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp i .B c)
        · simp only [ite_true]
          cases hInst : s_ad.1 i with
          | none =>
            have hInstV : (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = none := by
              simp [cliAdapterStateToV, hInst]
            rw [comp_eval_caseOpt_of_eq (v := none)
              (by dsimp only [Expr.eval, Env.get, Expr.v5, Expr.v6]; exact hInstV)]
            simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval,
              e2eBhAdapterIface, e2eAdapterIface, Env.get, Expr.v0, Expr.v1, Expr.v5]
            exact leaf_ij_keep P ki C K qep decT encT hInv i .B c true c c rfl
          | some inst =>
            have hInstV :
                (cliAdapterStateToV (ℓ := ℓ) s_ad).1 i = some (instMetaToV (ℓ := ℓ) inst) := by
              simp [cliAdapterStateToV, hInst]
            rw [comp_eval_caseOpt_of_eq (v := some (instMetaToV (ℓ := ℓ) inst))
              (by dsimp only [Expr.eval, Env.get, Expr.v5, Expr.v6]; exact hInstV)]
            dsimp only
            rw [bh_split_wrapWhisperWire]
            rw [comp_eval_ite_of_eq (v := m.inner.isEmpty)
              (by simp only [eval_isEmptyBytesExpr, Expr.eval, Env.get, Expr.v1])]
            cases hmEmp : m.inner.isEmpty
            · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_false,
                Comp.eval, Expr.eval, e2eBhAdapterIface, e2eAdapterIface, Env.get,
                Expr.v0, Expr.v2, Expr.v6]
              exact leaf_ij_keep P ki C K qep decT encT hInv i .B c true c c rfl
            · simp only [ite_true]
              rw [comp_eval_ite_of_eq (v := (bhShallowUpdateInstMeta inst false false c).1)
                (by dsimp only [Expr.eval, eval_adapterPureOp, env_get_zero, env_get_succ,
                      Expr.v0, Expr.v2, instMetaToV]
                    rw [← partneredInnerBytes_isSome_eq_updateInstMeta_fst (ℓ := ℓ) inst c m hm]
                    cases E2EPureOp.eval ℓ .partneredInnerBytes
                      (inst.bobAccepted, (bhInitRegId inst.sid, (hdrV (ℓ := ℓ) inst.hdr, c))) <;>
                      rfl)]
              cases hEqHdr : (bhShallowUpdateInstMeta inst false false c).1
              · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_false,
                  Comp.eval, Expr.eval, e2eBhAdapterIface, e2eAdapterIface, Env.get,
                  Expr.v0, Expr.v2, Expr.v6]
                exact leaf_ij_keep P ki C K qep decT encT hInv i .B c true c c rfl
              · simp (config := { failIfUnchanged := false }) only [ite_true, Comp.eval,
                  Expr.eval, eval_adapterPureOp, e2eBhAdapterIface, e2eAdapterIface, Env.get,
                  Expr.v0, Expr.v2, Expr.v6]
                exact leaf_ij_keep P ki C K qep decT encT hInv i .B c true
                  (E2EPureOp.eval ℓ .wrapWhisperWire c) (bhShallowWrapWhisper c)
                  (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT
                    hInv.no_whisp i .B c)
    | some body =>
      dsimp only
      rw [comp_eval_ite_of_eq (v := decide (c.length ≤ stdinCapBytes) && shortCiphertext c)
        (by rw [eval_and_capOkBytesExpr_checkShort_none]; rfl)]
      cases hShort : (decide (c.length ≤ stdinCapBytes) && shortCiphertext c)
      · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_false,
          Comp.eval, Expr.eval, eval_adapterPureOp, adapterNoneSmRespExpr,
          e2eBhAdapterIface, e2eAdapterIface, Env.get, Expr.v1, Expr.v5]
        exact leaf_ij_discard P ki C K qep decT encT hInv rfl i true
          (E2EPureOp.eval ℓ .wrapWhisperWire c) (bhShallowWrapWhisper c)
          (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp i .B c)
      · simp only [ite_true]
        rw [comp_eval_caseOpt_of_eq
          (v := (bhDecodePreKeyMsgE body).map fun m => (m.regId, (hdrV (ℓ := ℓ) (bhHdrOfPreKeyMsg m), m.inner)))
          (by dsimp only [Expr.eval, eval_adapterPureOp, Env.get, Expr.v0]
              exact parsePreKeyWire_eval_eq ℓ body)]
        dsimp (config := { failIfUnchanged := false }) only [bhShallowParsePreKey]
        cases hmBody : bhDecodePreKeyMsgE body with
        | none =>
          dsimp (config := { failIfUnchanged := false }) only [Option.map]
          rw [bh_split_wrapWhisperWire]
          rw [comp_eval_ite_of_eq (v := body.isEmpty)
            (by simp only [eval_isEmptyBytesExpr, Expr.eval, Env.get, Expr.v0])]
          cases hbEmp : body.isEmpty
          · simp (config := { failIfUnchanged := false }) only [Bool.false_eq_true, ite_false,
              Comp.eval, Expr.eval, e2eBhAdapterIface, e2eAdapterIface, Env.get,
              Expr.v0, Expr.v5]
            exact leaf_ij_keep P ki C K qep decT encT hInv i .B c true body body rfl
          · simp (config := { failIfUnchanged := false }) only [ite_true,
              Comp.eval, Expr.eval, eval_adapterPureOp, e2eBhAdapterIface, e2eAdapterIface,
              Env.get, Expr.v0, Expr.v1, Expr.v5]
            exact leaf_ij_keep P ki C K qep decT encT hInv i .B c true
              (E2EPureOp.eval ℓ .wrapWhisperWire c) (bhShallowWrapWhisper c)
              (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp
                i .B c)
        | some mBody =>
          dsimp (config := { failIfUnchanged := false }) only [Option.map]
          simp (config := { failIfUnchanged := false }) only [Comp.eval, Expr.eval,
            eval_adapterPureOp, e2eBhAdapterIface, e2eAdapterIface, Env.get,
            Expr.v0, Expr.v1, Expr.v6]
          exact leaf_ij_keep P ki C K qep decT encT hInv i .B c true
            (E2EPureOp.eval ℓ .wrapWhisperWire body) (bhShallowWrapWhisper body)
            (bhE2EStepLocalSmCoinLogged_ij_wrapWhisperWire_eq C K qep decT encT hInv.no_whisp
              i .B body)

private theorem cliHonestStepImplWith_coupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_ad : CliAdapterState S} {σ_log : DrvLogState S ℓ}
    (hInv : AdapterCouplingInv C K s_ad σ_log.1)
    (q : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain) :
    StepCoupledEq C K
      (((cliHonestStepImplWith P ki C K qep decT encT q).run
        (cliAdapterStateToV (ℓ := ℓ) s_ad)).run σ_log)
      (((cliAdapterStepImplWithLogState P ki C K qep decT encT q).run s_ad).run σ_log) := by
  rcases σ_log with ⟨σ_e2e, log⟩
  rcases q with n | ((kq | cq) | ⟨i, (((⟨p, m, optR⟩ | ⟨p, m0, m1, optR⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p⟩)
  · exact step_eq_unif P ki C K qep decT encT hInv n
  · exact step_eq_ki P hKi C K qep decT encT hInv kq
  · cases cq with
    | startDR sid => exact step_eq_ctl P hKi C K qep decT encT hInv sid
  · exact step_eq_tr P ki C K qep decT encT hInv i p m optR
  · exact step_eq_ch P ki C K qep decT encT hInv i p m0 m1 optR
  · exact step_eq_dl P ki C K qep decT encT hInv i p c
  · exact step_eq_ij P ki C K qep decT encT hInv i p c
  · exact step_eq_cr P ki C K qep decT encT hInv i p

private theorem simulateQ_cliHonestStepImplWith_eq_map
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives)
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) α)
    {s_ad : CliAdapterState S} {σ_log : DrvLogState S ℓ}
    (hInv : AdapterCouplingInv C K s_ad σ_log.1) :
    (((simulateQ (cliHonestStepImplWith P ki C K qep decT encT) oa).run
      (cliAdapterStateToV (ℓ := ℓ) s_ad)).run σ_log) =
    (fun p => ((p.1.1, cliAdapterStateToV (ℓ := ℓ) p.1.2), p.2)) <$>
      (((simulateQ (cliAdapterStepImplWithLogState P ki C K qep decT encT) oa).run s_ad).run
        σ_log) := by
  induction oa using OracleComp.inductionOn generalizing s_ad σ_log with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, StateT.run_bind, run_simulateQ_query_bind, StateT.run_bind]
    obtain ⟨hStepEq, hStepInv⟩ := cliHonestStepImplWith_coupled P hKi C K qep decT encT hInv q
    rw [hStepEq, bind_map_left]
    exact probComp_bind_eq_map_bind _ _ fun ⟨⟨u, s_ad'⟩, σ_log'⟩ hout =>
      ih u (hStepInv _ hout)

theorem cliE2EExpWithKiCoinLogged_cliToModelAdapterProg_eq_L_bh_of_ki
    (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) Bool) :
    cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ()) =
      cliE2EExpWithKiCoinLogged secb S P ki C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => B) ()) := by
  have hHonEval :
      (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) () =
      Prod.fst <$>
        ((simulateQ (handlerImpl (C := e2eBhAdapterCodec S ℓ)
          (I := e2eBhAdapterIface S ℓ)
          (cliAdapterHandle decT encT S ℓ)) B).run
          (cliAdapterStateToV (ℓ := ℓ) (cliAdapterInitState S))) := by
    dsimp [CostedReduction.eval, CostedReduction.impl, cliToModelAdapterProg, Comp.eval,
      Expr.eval, Env.get, cliAdapterInitState, cliAdapterStateToV, drvMirrorToV]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    rfl
  have hRefEval :
      (L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => B) () =
      Prod.fst <$>
        ((simulateQ (bhShallowAdapterImpl S ℓ (BitVec 512)) B).run
          (cliAdapterInitState S)) := by
    dsimp [BhShallowRed.eval, L_bh]
    simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  have hSimEq : ∀ b : Bool,
      ((simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ())).run
        { b := b, st := SignalPqxdh.KeyIndState.empty S secb }) =
      ((simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => B) ())).run
        { b := b, st := SignalPqxdh.KeyIndState.empty S secb }) := fun b => by
    apply WriterT.ext
    rw [run_simulateQ_cliE2EDrvImplWithCoinLogged_nil,
      run_simulateQ_cliE2EDrvImplWithCoinLogged_nil]
    congr 1
    rw [hHonEval, hRefEval]
    simp only [map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, StateT.run_bind,
      simulateQ_pure, StateT.run_pure]
    rw [simulateQ_cliE2EDrvImplWith_honest_run, simulateQ_cliE2EDrvImplWithLogState_adapter_run,
      simulateQ_cliHonestStepImplWith_eq_map P hKi C K qep decT encT B
        (adapterCouplingInv_init C K b secb)]
    simp only [bind_map_left]
  unfold cliE2EExpWithKiCoinLogged
  simp only [hSimEq]

theorem cliE2EExpWithKiCoinLogged_cliToModelAdapterProg_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    cliE2EExpWithKiCoinLogged true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) =
      cliE2EExpWithKiCoinLogged true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) :=
  cliE2EExpWithKiCoinLogged_cliToModelAdapterProg_eq_L_bh_of_ki true S P
    (kiFreshKeys_pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT (cliGameAdversaryReassoc A)

theorem cliE2EExpWithKiCoinLogged_pqxdhKeyIndImpl_cliToModelAdapterProg_eq_L_bh
    (useRo secb : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) Bool) :
    cliE2EExpWithKiCoinLogged secb S P (SignalPqxdh.pqxdhKeyIndImpl useRo S P) C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ()) =
      cliE2EExpWithKiCoinLogged secb S P (SignalPqxdh.pqxdhKeyIndImpl useRo S P) C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => B) ()) :=
  cliE2EExpWithKiCoinLogged_cliToModelAdapterProg_eq_L_bh_of_ki secb S P
    (kiFreshKeys_pqxdhKeyIndImpl useRo S P) C K ℓ qep decT encT B

theorem cliE2EExpWithKiCoinLogged_pqxdhKeyIndImpl1KeyRo_cliToModelAdapterProg_eq_L_bh
    (secb : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) Bool) :
    cliE2EExpWithKiCoinLogged secb S P (SignalPqxdh.pqxdhKeyIndImpl1KeyRo S P) C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ()) =
      cliE2EExpWithKiCoinLogged secb S P (SignalPqxdh.pqxdhKeyIndImpl1KeyRo S P) C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => B) ()) :=
  cliE2EExpWithKiCoinLogged_cliToModelAdapterProg_eq_L_bh_of_ki secb S P
    (kiFreshKeys_pqxdhKeyIndImpl1KeyRo S P) C K ℓ qep decT encT B

theorem cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh_of_ki
    (secb : Bool) (S : SignalPqxdh.Setup)
    (P : SignalPqxdh.Primitives)
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) Bool) :
    cliE2EExpWithKi secb S P ki C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ()) =
      cliE2EExpWithKi secb S P ki C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => B) ()) := by
  rw [← cliE2EExpWithKiCoinLogged_fst, ← cliE2EExpWithKiCoinLogged_fst,
    cliE2EExpWithKiCoinLogged_cliToModelAdapterProg_eq_L_bh_of_ki secb S P hKi C K ℓ qep
      decT encT B]

theorem cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) =
      cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) :=
  cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh_of_ki true S P
    (kiFreshKeys_pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT (cliGameAdversaryReassoc A)

theorem cliE2EExpWithKi_pqxdhKeyIndImpl_cliToModelAdapterProg_eq_L_bh
    (useRo secb : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) Bool) :
    cliE2EExpWithKi secb S P (SignalPqxdh.pqxdhKeyIndImpl useRo S P) C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ()) =
      cliE2EExpWithKi secb S P (SignalPqxdh.pqxdhKeyIndImpl useRo S P) C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => B) ()) :=
  cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh_of_ki secb S P
    (kiFreshKeys_pqxdhKeyIndImpl useRo S P) C K ℓ qep decT encT B

theorem cliE2EExpWithKi_pqxdhKeyIndImpl1KeyRo_cliToModelAdapterProg_eq_L_bh
    (secb : Bool) (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) Bool) :
    cliE2EExpWithKi secb S P (SignalPqxdh.pqxdhKeyIndImpl1KeyRo S P) C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ()) =
      cliE2EExpWithKi secb S P (SignalPqxdh.pqxdhKeyIndImpl1KeyRo S P) C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval (fun _ => B) ()) :=
  cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh_of_ki secb S P
    (kiFreshKeys_pqxdhKeyIndImpl1KeyRo S P) C K ℓ qep decT encT B

theorem evalDist_cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ())) =
      evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ())) :=
  congrArg evalDist
    (cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh S P C K ℓ qep decT encT A)

/-- Exact advantage (`boolBias`) equivalence between `cliToModelAdapterProg` and `L_bh` inside
`cliE2EExpWithKi`. -/
theorem boolBias_cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    (evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()))).boolBias =
      (evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()))).boolBias := by
  rw [evalDist_cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh S P C K ℓ qep decT encT A]

end ExperimentEquivalence

/-! ## `Ty.tbl`-backed adapter `cliToModelAdapterProgTbl` -/

section TightTblAdapter
section TightTblAdapterBounds
attribute [local simp] env_get_zero env_get_succ

def packBytesLE : Bytes → ℕ
  | [] => 0
  | b :: bs => b.toNat + 256 * packBytesLE bs

def pack1568Key4 (ub : SignalPqxdh.Bytes) : ℕ × ℕ × ℕ × ℕ :=
  let bs := CryptoVerification.E2E.ofU8 ub
  (packBytesLE ((bs.drop 0).take 392),
   (packBytesLE ((bs.drop 392).take 392),
    (packBytesLE ((bs.drop 784).take 392),
     packBytesLE ((bs.drop 1176).take 392))))

@[reducible] def bundlesTblTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .tbl (.tbl (.tbl (.tbl (.tbl (.tbl (.opt (.prod (FinT S.N_id) (FinT S.N_recv))))))))

@[reducible] def opksTblTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .tbl (.tbl (.tbl (.opt (PB 32))))

@[reducible] def sendsHalfTblTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .tbl (.tbl (.opt (.prod bundleT hdrT)))

/-- Nested `Ty.tbl` mirror type for `ModelDriverBase S`. -/
@[reducible] def drvMirrorTblTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (.tbl (.opt (PB 32)))
    (.prod (bundlesTblTy S ℓ)
      (.prod (opksTblTy ℓ)
        (.prod (sendsHalfTblTy ℓ) (sendsHalfTblTy ℓ))))

@[reducible] def cliAdapterTblStateTy (S : SignalPqxdh.Setup) (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  adapterStateTy (drvMirrorTblTy S ℓ)

def prinsTblOfList {S : SignalPqxdh.Setup}
    (l : List (Fin S.N_id × SignalPqxdh.Bytes)) : ℕ → Option SignalPqxdh.Bytes :=
  l.foldr (fun e tbl k => if k = e.1.val then some e.2 else tbl k) (fun _ => none)

def bundlesTblOfList {S : SignalPqxdh.Setup}
    (l : List ((Fin S.N_id × Fin S.N_recv) × SignalPqxdh.Bytes × SignalPqxdh.Bytes)) :
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Option (Fin S.N_id × Fin S.N_recv) :=
  l.foldr (fun e tbl kJ kSpk k0 k1 k2 k3 =>
    let jKey := (UInt32.ofNat e.1.2.val).toNat
    let spkKey := packBytesLE (CryptoVerification.E2E.ofU8 e.2.1)
    let (p0, (p1, (p2, p3))) := pack1568Key4 e.2.2
    if kJ = jKey ∧ kSpk = spkKey ∧ k0 = p0 ∧ k1 = p1 ∧ k2 = p2 ∧ k3 = p3 then
      some e.1
    else
      tbl kJ kSpk k0 k1 k2 k3)
    (fun _ _ _ _ _ _ => none)

def opksTblOfList {S : SignalPqxdh.Setup}
    (l : List ((Fin S.N_id × Fin S.N_recv × Fin S.N_opk) × SignalPqxdh.Bytes)) :
    ℕ → ℕ → ℕ → Option SignalPqxdh.Bytes :=
  l.foldr (fun e tbl ku kj ko =>
    if ku = e.1.1.val ∧ kj = e.1.2.1.val ∧ ko = e.1.2.2.val then some e.2
    else tbl ku kj ko)
    (fun _ _ _ => none)

def sendsOpkTblOfList {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (l : List (SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr)) :
    ℕ → ℕ → Option ((Ty.prod (bundleT (ℓ := ℓ)) hdrT).denote) :=
  l.foldr (fun e tbl ku ki =>
    match e.1 with
    | .sendOPK u i =>
      if ku = u.val ∧ ki = i.val then some (bundleV (ℓ := ℓ) e.2.1, hdrV (ℓ := ℓ) e.2.2)
      else tbl ku ki
    | _ => tbl ku ki)
    (fun _ _ => none)

def sendsNoOpkTblOfList {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (l : List (SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr)) :
    ℕ → ℕ → Option ((Ty.prod (bundleT (ℓ := ℓ)) hdrT).denote) :=
  l.foldr (fun e tbl ku ki =>
    match e.1 with
    | .sendNoOPK u i =>
      if ku = u.val ∧ ki = i.val then some (bundleV (ℓ := ℓ) e.2.1, hdrV (ℓ := ℓ) e.2.2)
      else tbl ku ki
    | _ => tbl ku ki)
    (fun _ _ => none)

def drvMirrorTblToV {S : SignalPqxdh.Setup} {ℓ : ℕ} (d : ModelDriverBase S) :
    (drvMirrorTblTy S ℓ).denote :=
  (prinsTblOfList d.prins,
   (bundlesTblOfList d.bundles,
    (opksTblOfList d.opks,
     (sendsOpkTblOfList (ℓ := ℓ) d.sends, sendsNoOpkTblOfList (ℓ := ℓ) d.sends))))

def cliAdapterTblStateToV {S : SignalPqxdh.Setup} {ℓ : ℕ} (σ : RefAdapterState S) :
    (cliAdapterTblStateTy S ℓ).denote :=
  (fun k => (σ.1 k).map instMetaToV, (σ.2.1, drvMirrorTblToV σ.2.2))

def natListLitE {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    List ℕ → Expr O Γ (.list .nat)
  | [] => .nil
  | k :: ks => .cons (.nat k) (natListLitE ks)

def byte1ToNatE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 1)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .caseOpt
    (adapterPureOp .spqrParsePreamble
      (adapterPureOp (.bytesWiden 3 29)
        (adapterPureOp (.bytesCat 1 2)
          (.pair e (adapterPureOp (.bytesLit 2 [1#8, 0#8]) .unit)))))
    (.nat 0)
    (adapterPureOp .u8ToNat (.fst .v0))

def pack8BytesE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 8)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .letE e
    (.foldrB 8 (natListLitE (List.range 8)) (.nat 0)
      (.add
        (byte1ToNatE
          (adapterPureOp (.bytesTakeK 8 1)
            (adapterPureOp (.bytesDrop 8) (.pair .v0 .v2))))
        (.mulK 256 .v1)))

def pack32PbytesE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 32)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .letE (adapterPureOp (.pbytesToBytes 32) e)
    (.foldrB 4 (natListLitE (List.range 4)) (.nat 0)
      (.add
        (pack8BytesE
          (adapterPureOp (.bytesTakeK 32 8)
            (adapterPureOp (.bytesDrop 32) (.pair (.mulK 8 .v0) .v2))))
        (.mulK (256 ^ 8) .v1)))

def pack56BytesE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 56)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .letE e
    (.foldrB 7 (natListLitE (List.range 7)) (.nat 0)
      (.add
        (pack8BytesE
          (adapterPureOp (.bytesTakeK 56 8)
            (adapterPureOp (.bytesDrop 56) (.pair (.mulK 8 .v0) .v2))))
        (.mulK (256 ^ 8) .v1)))

def pack392BytesE {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 392)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ .nat :=
  .letE e
    (.foldrB 7 (natListLitE (List.range 7)) (.nat 0)
      (.add
        (pack56BytesE
          (adapterPureOp (.bytesTakeK 392 56)
            (adapterPureOp (.bytesDrop 392) (.pair (.mulK 56 .v0) .v2))))
        (.mulK (256 ^ 56) .v1)))

def pack1568Key4E {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 1568)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (.prod .nat (.prod .nat (.prod .nat .nat))) :=
  .letE (adapterPureOp (.pbytesToBytes 1568) e)
    (.pair
      (pack392BytesE
        (adapterPureOp (.bytesTakeK 1568 392)
          (adapterPureOp (.bytesDrop 1568) (.pair (.nat 0) .v0))))
      (.pair
        (pack392BytesE
          (adapterPureOp (.bytesTakeK 1568 392)
            (adapterPureOp (.bytesDrop 1568) (.pair (.nat 392) .v0))))
        (.pair
          (pack392BytesE
            (adapterPureOp (.bytesTakeK 1568 392)
              (adapterPureOp (.bytesDrop 1568) (.pair (.nat 784) .v0))))
          (pack392BytesE
            (adapterPureOp (.bytesTakeK 1568 392)
              (adapterPureOp (.bytesDrop 1568) (.pair (.nat 1176) .v0)))))))

def tset2E {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl t)))
    (k0 k1 : Expr O Γ .nat) (val : Expr O Γ t) :
    Expr O Γ (.tbl (.tbl t)) :=
  .letE (.pair m (.pair k0 (.pair k1 val)))
    (let m0 := Expr.fst .v0
     let i0 := Expr.fst (.snd .v0)
     let i1 := Expr.fst (.snd (.snd .v0))
     let vE := Expr.snd (.snd (.snd .v0))
     .tset m0 i0 (.tset (.tget m0 i0) i1 vE))

def tset3E {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl (.tbl t))))
    (k0 k1 k2 : Expr O Γ .nat) (val : Expr O Γ t) :
    Expr O Γ (.tbl (.tbl (.tbl t))) :=
  .letE (.pair m (.pair k0 (.pair k1 (.pair k2 val))))
    (.letE (.tget (.fst .v0) (.fst (.snd .v0)))
      (let m0 := Expr.fst .v1
       let i0 := Expr.fst (.snd .v1)
       let i1 := Expr.fst (.snd (.snd .v1))
       let i2 := Expr.fst (.snd (.snd (.snd .v1)))
       let vE := Expr.snd (.snd (.snd (.snd .v1)))
       .tset m0 i0 (.tset .v0 i1 (.tset (.tget .v0 i1) i2 vE))))

def tset6E {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl (.tbl (.tbl (.tbl (.tbl t)))))))
    (k0 k1 k2 k3 k4 k5 : Expr O Γ .nat) (val : Expr O Γ t) :
    Expr O Γ (.tbl (.tbl (.tbl (.tbl (.tbl (.tbl t)))))) :=
  .letE (.pair m (.pair k0 (.pair k1 (.pair k2 (.pair k3 (.pair k4 (.pair k5 val)))))))
    (.letE (.tget (.fst .v0) (.fst (.snd .v0)))
      (.letE (.tget .v0 (.fst (.snd (.snd .v1))))
        (.letE (.tget .v0 (.fst (.snd (.snd (.snd .v2)))))
          (let tup := Expr.v3
           let m0 := Expr.fst tup
           let i0 := Expr.fst (.snd tup)
           let i1 := Expr.fst (.snd (.snd tup))
           let i2 := Expr.fst (.snd (.snd (.snd tup)))
           let i3 := Expr.fst (.snd (.snd (.snd (.snd tup))))
           let i4 := Expr.fst (.snd (.snd (.snd (.snd (.snd tup)))))
           let i5 := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd tup))))))
           let vE := Expr.snd (.snd (.snd (.snd (.snd (.snd (.snd tup))))))
           .tset m0 i0
             (.tset .v2 i1
               (.tset .v1 i2
                 (tset3E .v0 i3 i4 i5 vE)))))))

def stepBaseMirrorTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ) :=
  .letE (.pair drv (.pair kq kr))
    (.caseSum (.fst (.snd .v0))
      (.caseSum (.snd (.snd .v1))
        (.fst .v2)
        (.caseSum .v0
          (.pair
            (.tset (.fst (.fst .v3)) (adapterPureOp (.finVal S.N_id) .v2) (.some (.fst .v0)))
            (.snd (.fst .v3)))
          (.fst .v3)))
      (.caseSum .v0
        (.fst .v2)
        (.caseSum .v0
          (.caseSum (.snd (.snd .v3))
            (.fst .v4)
            (.caseSum .v0
              (.fst .v5)
              (.caseSum .v0
                (.fst .v6)
                (.caseSum .v0
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (let pqspkB := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd .v0))))))
                     .letE (pack1568Key4E pqspkB)
                       (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTblTy S ℓ) :=
                          .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                        let ujE := Expr.v6
                        let spkB := Expr.fst (.snd (.snd .v1))
                        let jKeyE := adapterPureOp .pu32ToNat
                          (adapterPureOp .pu32OfNat (adapterPureOp (.finVal S.N_recv) (.snd ujE)))
                        let spkKeyE := pack32PbytesE spkB
                        .pair (.fst dE)
                          (.pair
                            (tset6E (.fst (.snd dE)) jKeyE spkKeyE
                              (.fst .v0) (.fst (.snd .v0))
                              (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
                              (.some ujE))
                            (.snd (.snd dE)))))
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))
          (.caseSum .v0
            (.caseSum (.snd (.snd .v4))
              (.fst .v5)
              (.caseSum .v0
                (.fst .v6)
                (.caseSum .v0
                  (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTblTy S ℓ) :=
                     .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
                   let ujo := Expr.v3
                   .pair (.fst dE)
                     (.pair (.fst (.snd dE))
                       (.pair
                         (tset3E (.fst (.snd (.snd dE)))
                           (adapterPureOp (.finVal S.N_id) (.fst ujo))
                           (adapterPureOp (.finVal S.N_recv) (.fst (.snd ujo)))
                           (adapterPureOp (.finVal S.N_opk) (.snd (.snd ujo)))
                           (.some .v0))
                         (.snd (.snd (.snd dE))))))
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
            (.caseSum .v0
              (.caseSum (.snd (.snd .v5))
                (.fst .v6)
                (.caseSum .v0
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                    (.caseSum .v0
                      (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
                      (.caseSum .v0
                        (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                        (.caseSum .v0
                          (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTblTy S ℓ) :=
                             .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                           let uib := Expr.v6
                           let bndE := Expr.snd (.snd uib)
                           .pair (.fst dE)
                             (.pair (.fst (.snd dE))
                               (.pair (.fst (.snd (.snd dE)))
                                 (.pair
                                   (tset2E (.fst (.snd (.snd (.snd dE))))
                                     (adapterPureOp (.finVal S.N_id) (.fst uib))
                                     (adapterPureOp (.finVal S.N_send_opk) (.fst (.snd uib)))
                                     (.some (.pair bndE .v0)))
                                   (.snd (.snd (.snd (.snd dE))))))))
                          (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))))))
              (.caseSum .v0
                (.caseSum (.snd (.snd .v6))
                  (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.caseSum .v0
                    (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))
                    (.caseSum .v0
                      (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
                      (.caseSum .v0
                        (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                        (.caseSum .v0
                          (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
                          (.caseSum .v0
                            (let dE : Expr (e2eAdapterOps ℓ decT encT) _ (drvMirrorTblTy S ℓ) :=
                               .fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
                             let uib := Expr.v6
                             let bndE := Expr.snd (.snd uib)
                             .pair (.fst dE)
                               (.pair (.fst (.snd dE))
                                 (.pair (.fst (.snd (.snd dE)))
                                   (.pair
                                     (.fst (.snd (.snd (.snd dE))))
                                     (tset2E (.snd (.snd (.snd (.snd dE))))
                                       (adapterPureOp (.finVal S.N_id) (.fst uib))
                                       (adapterPureOp (.finVal S.N_send_no_opk) (.fst (.snd uib)))
                                       (.some (.pair bndE .v0)))))))
                            (.fst (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))))))))
                (.fst .v6)))))))

def guardPromoteTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    Expr (e2eAdapterOps ℓ decT encT) Γ (.opt adapterInstMetaT) :=
  .letE (.pair drv sid)
    (let sendsLookup : Expr (e2eAdapterOps ℓ decT encT) _ (.opt (.prod bundleT hdrT)) :=
       .caseSum (.snd .v0)
         (.tget
           (.tget (.fst (.snd (.snd (.snd (.fst .v1)))))
             (adapterPureOp (.finVal S.N_id) (.fst .v0)))
           (adapterPureOp (.finVal S.N_send_opk) (.snd .v0)))
         (.caseSum .v0
           (.tget
             (.tget (.snd (.snd (.snd (.snd (.fst .v2)))))
               (adapterPureOp (.finVal S.N_id) (.fst .v0)))
             (adapterPureOp (.finVal S.N_send_no_opk) (.snd .v0)))
           .none)
     .caseOpt sendsLookup
       .none
       (let bnd := Expr.fst .v0
        let hdr := Expr.snd .v0
        let bndSpkB := Expr.fst (.snd (.snd bnd))
        let bndPqspkB := Expr.fst (.snd (.snd (.snd (.snd (.snd (.snd bnd))))))
        let hdrSpkId := Expr.fst (.snd (.snd hdr))
        let hdrPqspkId := Expr.fst (.snd (.snd (.snd (.snd hdr))))
        let preOk :=
          Expr.and (adapterPureOp .pu32Eq (.pair hdrSpkId hdrPqspkId))
            (.and (.eqN (adapterPureOp (.pbytesLen 32) bndSpkB) (.nat 32))
                  (.eqN (adapterPureOp (.pbytesLen 1568) bndPqspkB) (.nat 1568)))
        .ite preOk
          (.letE (pack1568Key4E bndPqspkB)
            (let bnd' := Expr.fst .v1
             let hdr' := Expr.snd .v1
             let bndSpkB' := Expr.fst (.snd (.snd bnd'))
             let hdrSpkId' := Expr.fst (.snd (.snd hdr'))
             let bndTbl := Expr.fst (.snd (.fst .v2))
             let foundBnd :=
               Expr.tget
                 (.tget
                   (.tget
                     (.tget
                       (.tget
                         (.tget bndTbl (adapterPureOp .pu32ToNat hdrSpkId'))
                         (pack32PbytesE bndSpkB'))
                       (.fst .v0))
                     (.fst (.snd .v0)))
                   (.fst (.snd (.snd .v0))))
                 (.snd (.snd (.snd .v0)))
             .caseOpt foundBnd
               .none
               (let uResp := Expr.fst .v0
                let bnd2 := Expr.fst .v2
                let prinsOk : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
                  .caseOpt
                    (.tget (.fst (.fst .v3)) (adapterPureOp (.finVal S.N_id) uResp))
                    (.bool false)
                    (adapterPureOp (.pbytesEq 32 32) (.pair .v0 (.fst (.fst .v3))))
                let bndOpkOpt := Expr.fst (.snd (.snd (.snd (.snd bnd2))))
                let opkOk : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
                  .caseOpt bndOpkOpt
                    (.bool true)
                    (.caseOpt
                      (.tget
                        (.tget
                          (.tget (.fst (.snd (.snd (.fst .v4))))
                            (adapterPureOp (.finVal S.N_id) (.fst .v1)))
                          (adapterPureOp (.finVal S.N_recv) (.snd .v1)))
                        (adapterPureOp .pu32ToNat (.fst .v0)))
                      (.bool false)
                      (adapterPureOp (.pbytesEq 32 32) (.pair .v0 (.snd .v1))))
                .ite (.and prinsOk opkOk)
                  (let regIdA := initRegIdExpr (.snd .v3)
                   let regIdB := adapterPureOp .u32OfNat (adapterPureOp (.finVal S.N_id) uResp)
                   let hdr2 := Expr.snd .v2
                   .some (.pair (.pair regIdA (.pair regIdB (.pair regIdA hdr2))) (.bool false)))
                  .none)))
          .none))

def cliBobUpdateStateTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (σVar : Var (.opt recvResultT :: Γ) (cliAdapterTblStateTy S ℓ))
    (instIdxVar : Var (.opt recvResultT :: Γ) .nat)
    (instVar : Var (.opt recvResultT :: Γ) adapterInstMetaT)
    (mRegIdVar : Var (.opt recvResultT :: Γ) U32) :
    Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ) (cliAdapterTblStateTy S ℓ) :=
  .caseOpt .v0 (.var σVar)
    (.caseSum .v0 (.var (.succ (.succ σVar)))
      (let σE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ σVar))
       let idxE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instIdxVar))
       let instE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instVar))
       let mRegE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ mRegIdVar))
       let regIdA := Expr.fst (.fst instE)
       let regIdB := Expr.fst (.snd (.fst instE))
       let oldBobRem := Expr.fst (.snd (.snd (.fst instE)))
       let instHdr := Expr.snd (.snd (.snd (.fst instE)))
       let bobAcc := Expr.snd instE
       let newBobRem := Expr.ite (.not bobAcc) mRegE oldBobRem
       let newInst := Expr.pair (.pair regIdA (.pair regIdB (.pair newBobRem instHdr))) (.bool true)
       .pair (.tset (.fst σE) idxE (.some newInst)) (.snd σE)))

def cliAliceUpdateStateTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (σVar : Var (.opt recvResultT :: Γ) (cliAdapterTblStateTy S ℓ))
    (instIdxVar : Var (.opt recvResultT :: Γ) .nat) :
    Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ) (cliAdapterTblStateTy S ℓ) :=
  .caseOpt .v0 (.var σVar)
    (.caseSum .v0 (.var (.succ (.succ σVar)))
      (let σE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ σVar))
       let idxE := Expr.var (O := e2eAdapterOps ℓ decT encT) (.succ (.succ instIdxVar))
       .pair (.fst σE)
         (.pair (.tset (.fst (.snd σE)) idxE (.bool true))
                (.snd (.snd σE)))))

def cliAdapterKiOrCtlArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.sum (keyIndQT S) (sidT S), cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseSum .v0
    (.bind (cliQuery E2EAdapterTag.ki .v0)
      (.ret (.pair (.inl (.inl .v0))
        (.pair (.fst .v3)
          (.pair (.fst (.snd .v3))
            (stepBaseMirrorTblExpr (.snd (.snd .v3)) .v1 .v0))))))
    (.bind (cliQuery E2EAdapterTag.ctl .v0)
      (.caseOpt .v0
        (.ret (.pair (.inl (.inr .none)) .v3))
        (.caseOpt (guardPromoteTblExpr (.snd (.snd .v4)) .v2)
          (.ret (.pair (.inl (.inr (.some .v0))) .v4))
          (.ret (.pair (.inl (.inr (.some .v1)))
            (.pair (.tset (.fst .v5) .v1 (.some .v0)) (.snd .v5)))))))

def cliAdapterTrArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (.prod PlainT (.opt BV512)),
       .prod .nat smQT, cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseOpt (.tget (.fst .v2) (.fst .v1))
    (.ret (.pair adapterNoneSmRespExpr .v2))
    (.bind (cliQuery E2EAdapterTag.tr (.pair (.fst .v2) .v1))
      (.caseOpt .v0
        (.ret (.pair adapterNoneSmRespExpr .v4))
        (let regIdA := Expr.fst (.fst .v2)
         let instHdr := Expr.snd (.snd (.snd (.fst .v2)))
         let wire :=
           Expr.ite (.fst .v3)
             (adapterPureOp .wrapWhisperWire .v0)
             (.ite (.tget (.fst (.snd .v5)) (.fst .v4))
               (adapterPureOp .wrapWhisperWire .v0)
               (adapterPureOp .wrapPreKeyWire (.pair regIdA (.pair instHdr .v0))))
         .ret (.pair (.inr (.pair (.some wire) (.pair .none .none))) .v5))))

def cliAdapterChArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseOpt (.tget (.fst .v3) (.fst .v2))
    (.ret (.pair adapterNoneSmRespExpr .v3))
    (.bind (cliQuery E2EAdapterTag.ch (.pair (.fst .v3) .v1))
      (.caseOpt .v0
        (.ret (.pair adapterNoneSmRespExpr .v5))
        (let regIdA := Expr.fst (.fst .v2)
         let instHdr := Expr.snd (.snd (.snd (.fst .v2)))
         let wire :=
           Expr.ite (.fst .v3)
             (adapterPureOp .wrapWhisperWire .v0)
             (.ite (.tget (.fst (.snd .v6)) (.fst .v5))
               (adapterPureOp .wrapWhisperWire .v0)
               (adapterPureOp .wrapPreKeyWire (.pair regIdA (.pair instHdr .v0))))
         .ret (.pair (.inr (.pair (.some wire) (.pair .none .none))) .v6))))

def cliAdapterDlArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (B 32),
       .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .ite (.fst .v0)
    (.caseOpt (.tget (.fst .v4) (.fst .v3))
      (.ret (.pair adapterNoneSmRespExpr .v4))
      (.caseOpt (adapterPureOp .parsePreKeyWire (.snd .v1))
        (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v1))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v4) (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
            (.ret (.pair adapterNoneSmRespExpr .v6)))
          (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
            (.ite (isEmptyBytesExpr .v0)
              (.bind (cliQuery E2EAdapterTag.ij
                  (.pair (.fst .v5) (.pair (.bool true) (adapterPureOp .wrapWhisperWire .v0))))
                (.ret (.pair adapterNoneSmRespExpr
                  (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
              (.bind (cliQuery E2EAdapterTag.dl (.pair (.fst .v5) (.pair (.bool true) .v0)))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
            (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) (.pair (.bool true) (.snd .v3))))
              (.ret (.pair adapterNoneSmRespExpr
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))
        (.ite (isEmptyBytesExpr (.snd (.snd .v0)))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v5)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd (.snd .v0))))))
            (.ret (.pair adapterNoneSmRespExpr
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
          (.bind (.ret (.fst .v5))
            (.bind (.ret (.fst .v1))
              (.bind (cliQuery E2EAdapterTag.dl (.pair .v1 .v4))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (cliBobUpdateStateTblExpr
                    (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                    (.succ (.succ .zero))
                    (.succ (.succ (.succ (.succ .zero))))
                    (.succ .zero))))))))))
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.ite (isEmptyBytesExpr (.snd .v0))
        (.bind (cliQuery E2EAdapterTag.dl (.pair (.fst .v3) .v0))
          (.ret (.pair (.inr (.pair .none (.pair .v0 .none))) .v5)))
        (.ret (.pair adapterNoneSmRespExpr .v4)))
      (.ite (isEmptyBytesExpr .v0)
        (.ret (.pair adapterNoneSmRespExpr .v5))
        (.bind (.ret (.fst .v4))
          (.bind (cliQuery E2EAdapterTag.dl (.pair .v0 (.pair (.bool false) .v1)))
            (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
              (cliAliceUpdateStateTblExpr
                (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
                (.succ .zero))))))))

def cliAdapterIjArmTbl (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.prod .bool (B 32),
       .sum (.prod .bool (B 32)) .bool,
       .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool),
       .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
         (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)),
       .prod .nat smQT, cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .ite (.fst .v0)
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.caseOpt (adapterPureOp .parsePreKeyWire (.snd .v0))
        (.bind (cliQuery E2EAdapterTag.ij
            (.pair (.fst .v4) (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v0)))))
          (.ret (.pair adapterNoneSmRespExpr .v6)))
        (.ite (.and (capOkBytesExpr (.snd .v1))
            (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) (.some (.snd (.snd .v0))))))
          (.caseOpt (.tget (.fst .v6) (.fst .v5))
            (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v5) .v1))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (let bobAcc := Expr.snd .v0
             let regIdA := Expr.fst (.fst .v0)
             let instHdr := Expr.snd (.snd (.snd (.fst .v0)))
             let eqHdrExpr : Expr (e2eAdapterOps ℓ decT encT) _ .bool :=
               .caseOpt (adapterPureOp .partneredInnerBytes
                   (.pair bobAcc (.pair regIdA (.pair instHdr (.snd .v2)))))
                 (.bool false) (.bool true)
             .ite (isEmptyBytesExpr (.snd (.snd .v1)))
               (.ite eqHdrExpr
                 (.bind (cliQuery E2EAdapterTag.ij
                     (.pair (.fst .v6)
                       (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v2)))))
                   (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                     (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
                 (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) .v2))
                   (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                     (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
               (.bind (cliQuery E2EAdapterTag.ij (.pair (.fst .v6) .v2))
                 (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                   (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v5)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
            (.ret (.pair adapterNoneSmRespExpr
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
      (.ite (.and (capOkBytesExpr (.snd .v1))
          (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) .none)))
        (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
          (.ite (isEmptyBytesExpr .v0)
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5)
                  (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5) (.pair (.bool true) .v0)))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
          (.bind (cliQuery E2EAdapterTag.ij
              (.pair (.fst .v6)
                (.pair (.bool true) (adapterPureOp .wrapWhisperWire .v1))))
            (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
              (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
        (.bind (cliQuery E2EAdapterTag.ij
            (.pair (.fst .v5)
              (.pair (.bool true) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
          (.ret (.pair adapterNoneSmRespExpr
            (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
    (.caseOpt (adapterPureOp .splitWhisperWire (.snd .v0))
      (.ret (.pair adapterNoneSmRespExpr .v5))
      (.ite (.and (capOkBytesExpr (.snd .v1))
          (adapterPureOp .checkShortCiphertext (.pair (.snd .v1) .none)))
        (.caseOpt (adapterPureOp .parsePreKeyWire .v0)
          (.ite (isEmptyBytesExpr .v0)
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair (.fst .v5)
                  (.pair (.bool false) (adapterPureOp .wrapWhisperWire (.snd .v1)))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (.var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))
            (.bind (.ret (.fst .v5))
              (.bind (cliQuery E2EAdapterTag.ij (.pair .v0 (.pair (.bool false) .v1)))
                (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                  (cliAliceUpdateStateTblExpr
                    (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))
                    (.succ .zero)))))))
          (.bind (.ret (.fst .v6))
            (.bind (cliQuery E2EAdapterTag.ij
                (.pair .v0 (.pair (.bool false) (adapterPureOp .wrapWhisperWire .v2))))
              (.ret (.pair (.inr (.pair .none (.pair .v0 .none)))
                (cliAliceUpdateStateTblExpr
                  (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))
                  (.succ .zero)))))))
        (.ret (.pair adapterNoneSmRespExpr .v6))))

def cliAdapterHandleTbl {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseSum (.var (.succ .zero))
    (cliAdapterKiOrCtlArmTbl S ℓ decT encT)
    (.caseSum (.snd .v0)
      (cliAdapterTrArmTbl S ℓ decT encT)
      (.caseSum .v0
        (cliAdapterChArmTbl S ℓ decT encT)
        (.caseSum .v0
          (cliAdapterDlArmTbl S ℓ decT encT)
          (.caseSum .v0
            (cliAdapterIjArmTbl S ℓ decT encT)
            (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
              (drvMirrorTblTy S ℓ))))))

/-- Budget-independent `Ty.tbl`-backed `CostedReduction` adapter `cliToModelAdapterProgTbl`. -/
def cliToModelAdapterProgTbl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProgHonest S ℓ decT encT where
  σ := cliAdapterTblStateTy S ℓ
  init :=
    .ret (.pair
      .unit
      (.pair (.tconst .none)
        (.pair (.tconst (.bool false))
          (.pair (.tconst .none)
            (.pair (.tconst (.tconst (.tconst (.tconst (.tconst (.tconst .none))))))
              (.pair (.tconst (.tconst (.tconst .none)))
                (.pair (.tconst (.tconst .none)) (.tconst (.tconst .none)))))))))
  handle := cliAdapterHandleTbl decT encT S ℓ
  finish := .ret (.var (.succ .zero))

private def natListLitCost : List ℕ → ℕ
  | [] => 1
  | k :: ks => bits k + natListLitCost ks + 1

private theorem natListLitE_cost {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    ∀ (ns : List ℕ), (natListLitE (O := O) (Γ := Γ) ns).cost = natListLitCost ns
  | [] => rfl
  | _ :: ks => by simp only [natListLitE, Expr.cost, natListLitE_cost ks, natListLitCost]

private theorem natListLitE_size {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    ∀ (ns : List ℕ), (natListLitE (O := O) (Γ := Γ) ns).size = natListLitCost ns
  | [] => rfl
  | _ :: ks => by simp only [natListLitE, Expr.size, natListLitE_size ks, natListLitCost]

private theorem bits_256_pow_8 : bits (256 ^ 8) = 65 := by
  have hp : (256 : ℕ) ^ 8 = 2 ^ 64 := by
    rw [show (256 : ℕ) = 2 ^ 8 by decide, ← Nat.pow_mul]
  rw [hp, ReductionDsl.bits, Nat.log_pow (by decide : 1 < 2)]

private theorem bits_pow_mul {a b k : ℕ} (ha : a = 2 ^ b) : bits (a ^ k) = b * k + 1 := by
  subst ha
  rw [← Nat.pow_mul, ReductionDsl.bits, Nat.log_pow (by decide : 1 < 2)]

private theorem bits_256_pow_56 : bits (256 ^ 56) = 449 :=
  (bits_pow_mul (b := 8) (k := 56) (by decide)).trans (by omega)

private theorem byte1ToNatE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 62 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 1)),
      (byte1ToNatE e).cost = e.cost + c := by
  have hB0 : bits 0 = 1 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    dsimp only [byte1ToNatE, adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim,
      e2ePureOps, Expr.cost, E2EPureOp.cost, List.length_cons, List.length_nil, Expr.v0]
    simp only [PNat.val_ofNat, hB0, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack8BytesE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 824 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 8)),
      (pack8BytesE e).cost = e.cost + c := by
  obtain ⟨cb, hcb, hb⟩ := byte1ToNatE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL8 : natListLitCost (List.range 8) = 27 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB256 : bits 256 = 9 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack8BytesE
    dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_cost, hb]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v2]
    simp only [PNat.val_ofNat, hL8, hB0, hB256, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack32PbytesE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 3960 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 32)),
      (pack32PbytesE e).cost = e.cost + c := by
  obtain ⟨c8, hc8, h8⟩ := pack8BytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL4 : natListLitCost (List.range 4) = 11 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256_8 := bits_256_pow_8
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack32PbytesE
    dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_cost, h8]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v2]
    simp only [PNat.val_ofNat, hL4, hB0, hB8, hB256_8, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack56BytesE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 7200 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 56)),
      (pack56BytesE e).cost = e.cost + c := by
  obtain ⟨c8, hc8, h8⟩ := pack8BytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL7 : natListLitCost (List.range 7) = 23 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256_8 := bits_256_pow_8
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack56BytesE
    dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_cost, h8]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v2]
    simp only [PNat.val_ofNat, hL7, hB0, hB8, hB256_8, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack392BytesE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 59600 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 392)),
      (pack392BytesE e).cost = e.cost + c := by
  obtain ⟨c56, hc56, h56⟩ := pack56BytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL7 : natListLitCost (List.range 7) = 23 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB56 : bits 56 = 6 := by decide
  have hB256_56 := bits_256_pow_56
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack392BytesE
    dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_cost, h56]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v2]
    simp only [PNat.val_ofNat, hL7, hB0, hB56, hB256_56, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack1568Key4E_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 254200 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 1568)),
      (pack1568Key4E e).cost = e.cost + c := by
  obtain ⟨c392, hc392, h392⟩ := pack392BytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hB0 : bits 0 = 1 := by decide
  have hB392 : bits 392 = 9 := by decide
  have hB784 : bits 784 = 10 := by decide
  have hB1176 : bits 1176 = 11 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack1568Key4E
    dsimp only [Expr.cost]
    rw [h392, h392, h392, h392]
    simp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, PNat.val_ofNat, hB0, hB392, hB784, hB1176, Nat.add_assoc]
    rfl
  case hB =>
    linarith

private theorem stepBaseMirrorTblExpr_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    (stepBaseMirrorTblExpr drv kq kr).cost ≤ drv.cost + kq.cost + kr.cost + 260000 := by
  obtain ⟨c1568, hc1568, h1568⟩ := pack1568Key4E_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  obtain ⟨c32, hc32, h32⟩ := pack32PbytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  dsimp only [stepBaseMirrorTblExpr, tset6E, tset3E, tset2E, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [h1568, h32]
  dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
    Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v1]
  omega

private theorem guardPromoteTblExpr_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (guardPromoteTblExpr drv sid).cost ≤ drv.cost + sid.cost + 261000 := by
  obtain ⟨c1568, hc1568, h1568⟩ := pack1568Key4E_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  obtain ⟨c32, hc32, h32⟩ := pack32PbytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hB32 : bits 32 = 6 := by decide
  have hB1568 : bits 1568 = 11 := by decide
  dsimp only [guardPromoteTblExpr, initRegIdExpr, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  rw [h1568, h32]
  dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
    Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  simp only [PNat.val_ofNat, hB32, hB1568]
  omega

private theorem cliAdapterKiOrCtlArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterKiOrCtlArmTbl S ℓ decT encT).cost ≤ 261800 := by
  have hMir := stepBaseMirrorTblExpr_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
           cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v3)) .v1 .v0
  have hGrd := guardPromoteTblExpr_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
           cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v4)) .v2
  dsimp only [cliAdapterKiOrCtlArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hMir hGrd ⊢
  omega

private theorem cliAdapterTrArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterTrArmTbl S ℓ decT encT).cost ≤ 512 + 4 * (ℓ / 32) := by
  dsimp only [cliAdapterTrArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.cost, Expr.cost, cost_adapterPureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
  omega

private theorem cliAdapterChArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterChArmTbl S ℓ decT encT).cost ≤ 512 + 5 * (ℓ / 32) := by
  dsimp only [cliAdapterChArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.cost, Expr.cost, cost_adapterPureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  omega

private theorem cliAdapterDlArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterDlArmTbl S ℓ decT encT).cost ≤ 1024 + 4 * (ℓ / 32) := by
  have hB32 : bits (32 : ℕ+) = 6 := by decide
  have hB0 : bits 0 = 1 := by decide
  dsimp only [cliAdapterDlArmTbl, cliBobUpdateStateTblExpr, cliAliceUpdateStateTblExpr,
    isEmptyBytesExpr, cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr,
    Comp.cost, Expr.cost, cost_adapterPureOp, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2,
    Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hB32, hB0]
  omega

private theorem cliAdapterIjArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterIjArmTbl S ℓ decT encT).cost ≤ 1024 + 4 * (ℓ / 32) := by
  have hB32 : bits (32 : ℕ+) = 6 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hBCap : bits stdinCapBytes = 21 := by decide
  dsimp only [cliAdapterIjArmTbl, cliAliceUpdateStateTblExpr, isEmptyBytesExpr, capOkBytesExpr,
    cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr, Comp.cost, Expr.cost,
    cost_adapterPureOp, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, Expr.v6]
  rw [hB32, hB0, hBCap]
  omega

theorem totalCost_cliToModelAdapterProgTbl_le_bhAdapterCostBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).totalCost (b.q_total + qStart + qDR) ≤
      CryptoVerification.E2E.bhAdapterCostBudget S b qStart qDR ℓ := by
  let R := cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT
  let qTot := b.q_total + qStart + qDR
  let P := 2 ^ 6 * (4 * ℓ + 2 ^ 12)
  have hInitFin : R.init.cost + R.finish.cost ≤ P := by
    dsimp only [R, P, cliToModelAdapterProgTbl, Comp.cost, Expr.cost]
    omega
  have hHandle : R.handle.cost ≤ 262000 + 8 * (ℓ / 32) := by
    have h1 := cliAdapterKiOrCtlArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
    have h2 := cliAdapterTrArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
    have h3 := cliAdapterChArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
    have h4 := cliAdapterDlArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
    have h5 := cliAdapterIjArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
    have h6 := adapterCrArm_cost S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
      (drvMirrorTblTy S ℓ)
    dsimp only [R, cliToModelAdapterProgTbl, cliAdapterHandleTbl, Comp.cost, Expr.cost, Expr.v0]
    omega
  have hCodec : (e2eBhAdapterCodec S ℓ).codecCost ≤ 64 := by
    dsimp [e2eBhAdapterCodec, e2eAdapterCodec]
    omega
  have hStep : max (e2eBhAdapterIface S ℓ).uCost
      (R.handle.cost + (e2eBhAdapterCodec S ℓ).codecCost) ≤ P := by
    dsimp only [e2eBhAdapterIface, e2eAdapterIface, P]
    omega
  calc R.totalCost qTot
      = (R.init.cost + R.finish.cost) +
          qTot * max (e2eBhAdapterIface S ℓ).uCost
            (R.handle.cost + (e2eBhAdapterCodec S ℓ).codecCost) := by
        dsimp only [CostedReduction.totalCost]; omega
    _ ≤ 1 * P + qTot * P :=
        Nat.add_le_add (by simpa only [Nat.one_mul] using hInitFin) (Nat.mul_le_mul_left qTot hStep)
    _ = (qTot + 1) * P := by rw [← Nat.add_mul, Nat.add_comm]
    _ = 2 ^ 6 * (qTot + 1) * (4 * ℓ + 2 ^ 12) := by
        dsimp only [P]
        rw [← Nat.mul_assoc, Nat.mul_comm (qTot + 1) (2 ^ 6), Nat.mul_assoc]
    _ ≤ CryptoVerification.E2E.bhAdapterCostBudget S b qStart qDR ℓ := by
        unfold CryptoVerification.E2E.bhAdapterCostBudget
        dsimp only [qTot]
        exact Nat.mul_le_mul_left _ (by omega)

private theorem byte1ToNatE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 32 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 1)),
      (byte1ToNatE e).size = e.size + c := by
  have hB0 : bits 0 = 1 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    dsimp only [byte1ToNatE, adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim,
      e2ePureOps, Expr.size, E2EPureOp.opSize, List.length_cons, List.length_nil, Expr.v0]
    simp only [hB0, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack8BytesE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 128 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 8)),
      (pack8BytesE e).size = e.size + c := by
  obtain ⟨cb, hcb, hb⟩ := byte1ToNatE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL8 : natListLitCost (List.range 8) = 27 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256 : bits 256 = 9 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack8BytesE
    dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_size, hb]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v2]
    simp only [hL8, hB0, hB8, hB256, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack32PbytesE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 256 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 32)),
      (pack32PbytesE e).size = e.size + c := by
  obtain ⟨c8, hc8, h8⟩ := pack8BytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL4 : natListLitCost (List.range 4) = 11 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB4 : bits 4 = 3 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256_8 := bits_256_pow_8
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack32PbytesE
    dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_size, h8]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v2]
    simp only [hL4, hB0, hB4, hB8, hB256_8, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack56BytesE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 256 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 56)),
      (pack56BytesE e).size = e.size + c := by
  obtain ⟨c8, hc8, h8⟩ := pack8BytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL7 : natListLitCost (List.range 7) = 23 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB7 : bits 7 = 3 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256_8 := bits_256_pow_8
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack56BytesE
    dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_size, h8]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v2]
    simp only [hL7, hB0, hB7, hB8, hB256_8, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack392BytesE_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 800 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 392)),
      (pack392BytesE e).size = e.size + c := by
  obtain ⟨c56, hc56, h56⟩ := pack56BytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL7 : natListLitCost (List.range 7) = 23 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB7 : bits 7 = 3 := by decide
  have hB56 : bits 56 = 6 := by decide
  have hB256_56 := bits_256_pow_56
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack392BytesE
    dsimp only [Expr.size, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_size, h56]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v2]
    simp only [hL7, hB0, hB7, hB56, hB256_56, Nat.add_assoc]
    rfl
  case hB =>
    omega

private theorem pack1568Key4E_size_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 3400 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 1568)),
      (pack1568Key4E e).size = e.size + c := by
  obtain ⟨c392, hc392, h392⟩ := pack392BytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hB0 : bits 0 = 1 := by decide
  have hB392 : bits 392 = 9 := by decide
  have hB784 : bits 784 = 10 := by decide
  have hB1176 : bits 1176 = 11 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack1568Key4E
    dsimp only [Expr.size]
    rw [h392, h392, h392, h392]
    simp only [Nat.zero_add, adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim,
      e2ePureOps, Expr.size, E2EPureOp.opSize, Expr.v0, hB0, hB392, hB784, hB1176, Nat.add_assoc]
    rfl
  case hB =>
    linarith

private theorem stepBaseMirrorTblExpr_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    (stepBaseMirrorTblExpr drv kq kr).size ≤
      32 * drv.size + 32 * kq.size + 32 * kr.size + 6000 := by
  obtain ⟨c1568, hc1568, h1568⟩ := pack1568Key4E_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  obtain ⟨c32, hc32, h32⟩ := pack32PbytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  dsimp only [stepBaseMirrorTblExpr, tset6E, tset3E, tset2E, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [h1568, h32]
  dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
    Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v1]
  omega

private theorem guardPromoteTblExpr_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (guardPromoteTblExpr drv sid).size ≤ 16 * drv.size + 16 * sid.size + 6000 := by
  obtain ⟨c1568, hc1568, h1568⟩ := pack1568Key4E_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  obtain ⟨c32, hc32, h32⟩ := pack32PbytesE_size_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hB32 : bits 32 = 6 := by decide
  have hB1568 : bits 1568 = 11 := by decide
  dsimp only [guardPromoteTblExpr, initRegIdExpr, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  rw [h1568, h32]
  dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
    Expr.size, E2EPureOp.opSize, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  simp only [hB32, hB1568]
  omega

private theorem cliAdapterKiOrCtlArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterKiOrCtlArmTbl S ℓ decT encT).size ≤ 14000 := by
  have hMir := stepBaseMirrorTblExpr_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
           cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v3)) .v1 .v0
  have hGrd := guardPromoteTblExpr_size_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
           cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v4)) .v2
  dsimp only [cliAdapterKiOrCtlArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hMir hGrd ⊢
  omega

private theorem cliAdapterTrArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterTrArmTbl S ℓ decT encT).size ≤ 256 := by
  dsimp only [cliAdapterTrArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
  omega

private theorem cliAdapterChArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterChArmTbl S ℓ decT encT).size ≤ 256 := by
  dsimp only [cliAdapterChArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  omega

private theorem cliAdapterDlArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterDlArmTbl S ℓ decT encT).size ≤ 1024 := by
  have hB0 : bits 0 = 1 := by decide
  dsimp only [cliAdapterDlArmTbl, cliBobUpdateStateTblExpr, cliAliceUpdateStateTblExpr,
    isEmptyBytesExpr, cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr,
    Comp.size, Expr.size, Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp,
    E2EPureOp.opSize, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hB0]
  omega

private theorem cliAdapterIjArmTbl_size_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterIjArmTbl S ℓ decT encT).size ≤ 1536 := by
  have hB0 : bits 0 = 1 := by decide
  have hBCap : bits stdinCapBytes = 21 := by decide
  dsimp only [cliAdapterIjArmTbl, cliAliceUpdateStateTblExpr, isEmptyBytesExpr, capOkBytesExpr,
    cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr, Comp.size, Expr.size,
    Computational.Proofs.E2E.Dsl.TablesHonest.size_adapterPureOp, E2EPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hB0, hBCap]
  omega

theorem size_cliToModelAdapterProgTbl_le_reductionSizeBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget := by
  have h1 := cliAdapterKiOrCtlArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h2 := cliAdapterTrArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h3 := cliAdapterChArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h4 := cliAdapterDlArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h5 := cliAdapterIjArmTbl_size_le (S := S) (ℓ := ℓ) decT encT
  have h6 := Computational.Proofs.E2E.Dsl.TablesHonest.adapterCrArm_size S ℓ
    BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT (drvMirrorTblTy S ℓ)
  dsimp only [CostedReduction.size, _root_.ReductionDsl.reductionSizeBudget,
    cliToModelAdapterProgTbl, cliAdapterHandleTbl, Comp.size, Expr.size, Expr.v0]
  omega

theorem size_cliToModelAdapterProgTbl_le_bhAdapterCostBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * bits (CryptoVerification.E2E.bhAdapterCostBudget S b qStart qDR ℓ) :=
  Nat.le_trans (size_cliToModelAdapterProgTbl_le_reductionSizeBudget decT encT)
    (Nat.le_add_right _ _)

theorem totalQueries_cliToModelAdapterProgTbl_eq
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).totalQueries
      (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, cliToModelAdapterProgTbl, cliAdapterHandleTbl,
    cliAdapterKiOrCtlArmTbl, cliAdapterTrArmTbl, cliAdapterChArmTbl, cliAdapterDlArmTbl,
    cliAdapterIjArmTbl, adapterCrArm, cliQuery, Comp.queries]

theorem totalQueries_cliToModelAdapterProgTbl_le
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q :=
  (totalQueries_cliToModelAdapterProgTbl_eq (S := S) (ℓ := ℓ) decT encT q).le

/-- Unconditional `GRedBounded` in `bhAdapterCostBudget` for `cliToModelAdapterProgTbl`. -/
theorem gRedBounded_cliToModelAdapterProgTbl_bhAdapterCostBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    GRedBounded (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
      (CryptoVerification.E2E.bhAdapterCostBudget S b qStart qDR ℓ) :=
  gRedBounded_of_bounds (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT)
    (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
    (CryptoVerification.E2E.bhAdapterCostBudget S b qStart qDR ℓ)
    (totalCost_cliToModelAdapterProgTbl_le_bhAdapterCostBudget decT encT b qStart qDR)
    (size_cliToModelAdapterProgTbl_le_bhAdapterCostBudget decT encT b qStart qDR)
    (totalQueries_cliToModelAdapterProgTbl_le decT encT (b.q_total + qStart + qDR))
    (e2eAdapterOps_sizeHonest ℓ decT encT)
    (e2eSamplers_sizeHonest ℓ)

private theorem cliAdapterHandleTbl_queries {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterHandleTbl decT encT S ℓ).queries (fun _ => 1) (fun _ => 0) = 1 := by
  have h1 : (cliAdapterKiOrCtlArmTbl S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterKiOrCtlArmTbl, cliQuery, Comp.queries]
  have h2 : (cliAdapterTrArmTbl S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterTrArmTbl, cliQuery, Comp.queries]
  have h3 : (cliAdapterChArmTbl S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterChArmTbl, cliQuery, Comp.queries]
  have h4 : (cliAdapterDlArmTbl S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterDlArmTbl, cliQuery, Comp.queries]
  have h5 : (cliAdapterIjArmTbl S ℓ decT encT).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [cliAdapterIjArmTbl, cliQuery, Comp.queries]
  have h6 : (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
      (drvMirrorTblTy S ℓ)).queries (fun _ => 1) (fun _ => 0) = 1 := by
    simp [adapterCrArm, Comp.queries]
  simp [cliAdapterHandleTbl, Comp.queries, h1, h2, h3, h4, h5, h6]

set_option linter.unusedSimpArgs false in
private theorem isQueryBoundP_cliAdapterHandleTbl_eval_ij_cr
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool)
    (s : (cliAdapterTblStateTy S ℓ).denote) (i : ℕ)
    (sq_ij_cr : (Party × Bytes) ⊕ Party)
    (hpFalse : pInst i = false) :
    ((cliAdapterHandleTbl decT encT S ℓ).eval
      (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc
        (.inr ⟨i, match sq_ij_cr with
          | .inl pc => .inl (.inr pc)
          | .inr p => .inr p⟩)) .nil))).IsQueryBoundP
      (fun q => bhClassifyTarget pKi pCtl pInst q = true) 0 := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi pCtl pInst q = true
  rcases sq_ij_cr with ⟨p, c⟩ | p
  · unfold cliAdapterHandleTbl
    refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
      (qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
        (qb0_caseSum_inl P_tgt rfl ?_))))
    unfold cliAdapterIjArmTbl cliQuery
    cases p <;>
    · repeat' first
        | with_reducible exact qb0_ret P_tgt
        | with_reducible apply qb0_ite P_tgt
        | (with_reducible apply qb0_caseOpt P_tgt) <;> try intro _
        | with_reducible apply qb0_bind_ret P_tgt
        | refine qb0_bind P_tgt
            (qb0_query P_tgt (by
              simp only [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget,
                bhClassifyTargetOnly, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
                Expr.v3, Expr.v4, Expr.v5, Expr.v6, Env.get, hpFalse, Bool.false_eq_true,
                not_false_eq_true]))
            (fun _ => ?_)
  · unfold cliAdapterHandleTbl
    refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
      (qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
        (qb0_caseSum_inr P_tgt rfl ?_))))
    unfold adapterCrArm
    refine qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => ?_)
    refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ =>
      qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => qb0_ret P_tgt))
    simp only [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget,
      bhClassifyTargetOnly, Expr.eval, Expr.v0, Expr.v1, Expr.v5, Env.get, hpFalse,
      Bool.false_eq_true, not_false_eq_true]

set_option linter.unusedSimpArgs false in
private theorem isQueryBoundP_cliAdapterHandleTbl_eval
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (pCtl : BHDRCtlQuery S → Bool) (pInst : ℕ → Bool)
    (s : (cliAdapterTblStateTy S ℓ).denote) (t : (bhGameSpec S ℓ (BitVec 512)).Domain) :
    ((cliAdapterHandleTbl decT encT S ℓ).eval
      (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
      (fun q => bhClassifyTarget pKi pCtl pInst q = true)
      (if bhClassifyGameOnly pKi pCtl pInst t then 1 else 0) := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi pCtl pInst q = true
  by_cases hp : bhClassifyGameOnly pKi pCtl pInst t = true
  · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hp))]
    rw [← cliAdapterHandleTbl_queries (S := S) (ℓ := ℓ) decT encT]
    exact Comp.queryBound_eval P_tgt (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl)
      (isQueryBoundP_e2eBhAdapterIface_fwdU pKi pCtl pInst)
      (cliAdapterHandleTbl decT encT S ℓ)
      (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc t) .nil))
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hp h))]
    have hpFalse : bhClassifyGameOnly pKi pCtl pInst t = false :=
      Bool.eq_false_iff.mpr hp
    rcases t with (kq | cq) | ⟨i, sq⟩
    · simp only [bhClassifyGameOnly] at hpFalse
      unfold cliAdapterHandleTbl
      refine qb0_caseSum_inl P_tgt rfl ?_
      unfold cliAdapterKiOrCtlArmTbl cliQuery
      refine qb0_caseSum_inl P_tgt rfl ?_
      refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ => qb0_ret P_tgt)
      simp [P_tgt, e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec,
        bhClassifyTarget, bhClassifyTargetOnly, Expr.eval, Expr.v0, Env.get, hpFalse]
    · rcases cq with ⟨sid⟩
      simp only [bhClassifyGameOnly] at hpFalse
      unfold cliAdapterHandleTbl
      refine qb0_caseSum_inl P_tgt rfl ?_
      unfold cliAdapterKiOrCtlArmTbl cliQuery
      refine qb0_caseSum_inr P_tgt rfl ?_
      refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ => ?_)
      · simp [P_tgt, e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec,
          bhCtlUnStart, bhClassifyTarget, bhClassifyTargetOnly, Expr.eval, Expr.v0, Env.get, hpFalse]
      · exact qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ =>
          qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => qb0_ret P_tgt))
    · simp only [bhClassifyGameOnly] at hpFalse
      rcases sq with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
      · unfold cliAdapterHandleTbl
        refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inl P_tgt rfl ?_)
        unfold cliAdapterTrArmTbl cliQuery
        refine qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => ?_)
        refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ =>
          qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => qb0_ret P_tgt))
        simp [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget, bhClassifyTargetOnly,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, hpFalse]
      · unfold cliAdapterHandleTbl
        refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
          (qb0_caseSum_inl P_tgt rfl ?_))
        unfold cliAdapterChArmTbl cliQuery
        refine qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => ?_)
        refine qb0_bind P_tgt (qb0_query P_tgt ?_) (fun _ =>
          qb0_caseOpt P_tgt (qb0_ret P_tgt) (fun _ => qb0_ret P_tgt))
        simp [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget, bhClassifyTargetOnly,
          Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get, hpFalse]
      · unfold cliAdapterHandleTbl
        refine qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inr P_tgt rfl
          (qb0_caseSum_inr P_tgt rfl (qb0_caseSum_inl P_tgt rfl ?_)))
        unfold cliAdapterDlArmTbl cliQuery
        cases p <;>
        · repeat' first
            | with_reducible exact qb0_ret P_tgt
            | with_reducible apply qb0_ite P_tgt
            | (with_reducible apply qb0_caseOpt P_tgt) <;> try intro _
            | with_reducible apply qb0_bind_ret P_tgt
            | refine qb0_bind P_tgt
                (qb0_query P_tgt (by
                  simp only [P_tgt, e2eBhAdapterIface, e2eAdapterIface, bhClassifyTarget,
                    bhClassifyTargetOnly, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
                    Expr.v3, Expr.v4, Expr.v5, Expr.v6, Env.get, hpFalse, Bool.false_eq_true,
                    not_false_eq_true]))
                (fun _ => ?_)
      · exact isQueryBoundP_cliAdapterHandleTbl_eval_ij_cr decT encT pKi pCtl pInst s i (.inl (p, c))
          hpFalse
      · exact isQueryBoundP_cliAdapterHandleTbl_eval_ij_cr decT encT pKi pCtl pInst s i (.inr p)
          hpFalse

theorem isQueryBoundP_cliToModelAdapterProgTbl_eval
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (pKi : SignalPqxdh.KeyIndQuery S → Bool) (pCtl : BHDRCtlQuery S → Bool)
    (pInst : ℕ → Bool)
    (A : CliGameAdversary S ℓ (BitVec 512)) (n : ℕ)
    (h : A.run.IsQueryBoundP (fun q => bhClassifyComposed pKi pCtl pInst q = true) n) :
    ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()).IsQueryBoundP
      (fun q => bhClassifyTarget pKi pCtl pInst q = true) n := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi pCtl pInst q = true
  have hAdv := isQueryBoundP_bhAdvRun pKi pCtl pInst A n h
  have hstep : ∀ (q : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain)
      (s : (cliAdapterTblStateTy S ℓ).denote),
      (((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).impl q).run s).IsQueryBoundP
        P_tgt (if bhClassifyGame pKi pCtl pInst q = true then 1 else 0) := by
    intro q s
    cases q with
    | inl m =>
      show ((e2eBhAdapterIface S ℓ).fwdU m >>= fun a => pure (a, s)).IsQueryBoundP P_tgt 0
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (isQueryBoundP_e2eBhAdapterIface_fwdU pKi pCtl pInst m)
        (fun a _ => isQueryBoundP_pure P_tgt (a, s) 0)
    | inr t =>
      show ((cliAdapterHandleTbl decT encT S ℓ).eval
          (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc t) .nil)) >>=
          fun p => pure ((e2eBhAdapterCodec S ℓ).rdec t p.1, p.2)).IsQueryBoundP
        P_tgt (if bhClassifyGameOnly pKi pCtl pInst t = true then 1 else 0)
      simpa only [Nat.add_zero] using isQueryBoundP_bind
        (isQueryBoundP_cliAdapterHandleTbl_eval decT encT pKi pCtl pInst s t)
        (fun p _ => isQueryBoundP_pure P_tgt ((e2eBhAdapterCodec S ℓ).rdec t p.1, p.2) 0)
  have hsim := simulateQ_run_stateT_of_step_le hstep hAdv
  have hinit :
      ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).init.eval
        (Env.cons (t := .unit) () Env.nil)).IsQueryBoundP P_tgt 0 := by
    dsimp only [cliToModelAdapterProgTbl]
    exact qb0_ret P_tgt
  have hfin : ∀ s' b,
      ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).finish.eval
        (Env.cons s' (Env.cons b Env.nil))).IsQueryBoundP P_tgt 0 := by
    intro s' b
    dsimp only [cliToModelAdapterProgTbl]
    exact qb0_ret P_tgt
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit
    (fun ⟨a, s⟩ _ =>
      isQueryBoundP_bind (hsim s)
        (fun ⟨b, s'⟩ _ => hfin s' b))).mono (by omega)

/-- Per-instance `IsQueryBoundP` transfer for `cliToModelAdapterProgTbl`. -/
theorem cliToModelAdapterProgTbl_perInstanceQueryBounds
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hA : CliGameAdversaryPerInstanceBounded A b qStart qs) :
    let B_A :=
      (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval
        (fun _ => cliGameAdversaryReassoc A) ()
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
      b.q_on ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
      (∑ k ∈ Finset.range qStart, qs k) ∧
    (∀ k < qStart, B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      (qs k)) := by
  rcases hA with ⟨⟨hRo, hSend, hRecv, hTot, hOn, hCtl, hDr⟩, hStart, hInst⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) A b.q_ro
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [simp [bhClassifyComposed];
          (cases kq <;> simp [bhClassifyComposed]); simp [bhClassifyComposed];
          simp [bhClassifyComposed]]) hRo)
  · exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (fun _ => false) (fun _ => false) A S.N_send_tot
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [simp [bhClassifyComposed];
          (cases kq <;> simp [bhClassifyComposed]); simp [bhClassifyComposed];
          simp [bhClassifyComposed]]) hSend)
  · exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (fun _ => false) (fun _ => false) A S.N_recv_tot
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [simp [bhClassifyComposed];
          (cases kq <;> simp [bhClassifyComposed]); simp [bhClassifyComposed];
          simp [bhClassifyComposed]]) hRecv)
  · exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun _ => true) (fun _ => false) (fun _ => false) A b.q_total
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> simp [bhClassifyComposed]) hTot)
  · exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) A b.q_on
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> [simp [bhClassifyComposed];
          (cases kq <;> simp [bhClassifyComposed]); simp [bhClassifyComposed];
          simp [bhClassifyComposed]]) hOn)
  · exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun _ => false) (fun _ => true) (fun _ => false) A S.N_send_tot
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> simp [bhClassifyComposed]) hCtl)
  · exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun _ => false) (fun _ => true) (fun _ => false) A qStart
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> simp [bhClassifyComposed]) hStart)
  · exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun _ => false) (fun _ => false) (fun _ => true) A (∑ k ∈ Finset.range qStart, qs k)
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;> simp [bhClassifyComposed]) hDr)
  · intro k hk
    exact isQueryBoundP_cliToModelAdapterProgTbl_eval decT encT
      (fun _ => false) (fun _ => false) (fun i => i == k) A (qs k)
      (isQueryBoundP_congr_pred_local
        (by rintro (((m | kq) | cq) | ⟨i, sq⟩) <;>
          simp [bhClassifyComposed, bhIsInstQueryWithSpqr]) (hInst k hk))

end TightTblAdapterBounds

open CryptoVerification.E2E (ofU8)

section TblAdapterCouplingHelpers
set_option linter.unusedSimpArgs false

private theorem packBytesLE_append (xs ys : Bytes) :
    packBytesLE (xs ++ ys) = packBytesLE xs + 256 ^ xs.length * packBytesLE ys := by
  induction xs with
  | nil => simp [packBytesLE]
  | cons b xs ih =>
    simp only [List.cons_append, packBytesLE, List.length_cons, ih, Nat.pow_succ]
    ring

private theorem packBytesLE_lt (xs : Bytes) :
    packBytesLE xs < 256 ^ xs.length := by
  induction xs with
  | nil => simp [packBytesLE]
  | cons b xs ih =>
    have hb : b.toNat < 256 := b.isLt
    simp only [packBytesLE, List.length_cons, Nat.pow_succ]
    nlinarith

private theorem packBytesLE_inj_of_length_eq {xs ys : Bytes} (hlen : xs.length = ys.length)
    (heq : packBytesLE xs = packBytesLE ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [packBytesLE] at heq
      have hx : x.toNat < 256 := x.isLt
      have hy : y.toNat < 256 := y.isLt
      have hxy : x.toNat = y.toNat := by omega
      have hrest : packBytesLE xs = packBytesLE ys := by omega
      rw [BitVec.eq_of_toNat_eq hxy, ih hlen hrest]

private theorem ofU8_inj {xs ys : SignalPqxdh.Bytes} (h : ofU8 xs = ofU8 ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp [ofU8] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [ofU8] at h
    | cons y ys =>
      simp only [ofU8, List.map_cons, List.cons.injEq] at h
      have hxy : x = y := UInt8.eq_of_toBitVec_eq h.1
      rw [hxy, ih h.2]

private theorem pack1568Key4_inj {xs ys : SignalPqxdh.Bytes}
    (hx : xs.length = 1568) (hy : ys.length = 1568)
    (h : pack1568Key4 xs = pack1568Key4 ys) : xs = ys := by
  unfold pack1568Key4 at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  have hbx : (ofU8 xs).length = 1568 := by simp [ofU8, hx]
  have hby : (ofU8 ys).length = 1568 := by simp [ofU8, hy]
  have eqSlice : ∀ off : ℕ, off + 392 ≤ 1568 →
      packBytesLE (((ofU8 xs).drop off).take 392) =
      packBytesLE (((ofU8 ys).drop off).take 392) →
      ((ofU8 xs).drop off).take 392 = ((ofU8 ys).drop off).take 392 := by
    intro off hoff heq
    exact packBytesLE_inj_of_length_eq
      (by rw [List.length_take, List.length_drop, List.length_take, List.length_drop]; omega) heq
  have s0 := eqSlice 0 (by omega) h0
  have s1 := eqSlice 392 (by omega) h1
  have s2 := eqSlice 784 (by omega) h2
  have s3 := eqSlice 1176 (by omega) h3
  have hdecomp : ∀ bs : Bytes, bs.length = 1568 →
      bs = (bs.drop 0).take 392 ++ (bs.drop 392).take 392 ++
           (bs.drop 784).take 392 ++ (bs.drop 1176).take 392 := by
    intro bs hbs
    have d3 : bs.drop 1176 = (bs.drop 1176).take 392 :=
      (List.take_of_length_le (by rw [List.length_drop]; omega)).symm
    have d2 : bs.drop 784 = (bs.drop 784).take 392 ++ (bs.drop 1176).take 392 := by
      rw [← d3]
      conv_lhs => rw [← List.take_append_drop 392 (bs.drop 784)]
      simp only [List.drop_drop]
    have d1 : bs.drop 392 = (bs.drop 392).take 392 ++ (bs.drop 784).take 392 ++
        (bs.drop 1176).take 392 := by
      rw [List.append_assoc, ← d2]
      conv_lhs => rw [← List.take_append_drop 392 (bs.drop 392)]
      simp only [List.drop_drop]
    rw [List.append_assoc, List.append_assoc, ← List.append_assoc ((bs.drop 392).take 392), ← d1]
    simp only [List.drop_zero]
    exact (List.take_append_drop 392 bs).symm
  apply ofU8_inj
  rw [hdecomp (ofU8 xs) hbx, hdecomp (ofU8 ys) hby, s0, s1, s2, s3]

private theorem foldr_congr_mem {α β : Type} {f g : α → β → β} {l : List α} (z : β)
    (h : ∀ x ∈ l, ∀ acc, f x acc = g x acc) :
    l.foldr f z = l.foldr g z := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

private theorem foldr_range_packBytesLE (k m : ℕ) :
    ∀ (bs : Bytes), bs.length = k * m →
      (List.range k).foldr (fun i acc => packBytesLE ((bs.drop (m * i)).take m) + 256 ^ m * acc) 0 =
        packBytesLE bs := by
  induction k with
  | zero =>
    intro bs hbs
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at hbs
    subst hbs
    simp [packBytesLE]
  | succ k ih =>
    intro bs hbs
    rw [Nat.succ_mul] at hbs
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    have hdrop_len : (bs.drop m).length = k * m := by
      rw [List.length_drop]; omega
    have htake_len : (bs.take m).length = m := by
      rw [List.length_take]; omega
    have hcongr :
        (List.range k).foldr
          (fun x acc => packBytesLE ((bs.drop (m * (x + 1))).take m) + 256 ^ m * acc) 0 =
        (List.range k).foldr
          (fun x acc => packBytesLE (((bs.drop m).drop (m * x)).take m) + 256 ^ m * acc) 0 := by
      refine foldr_congr_mem 0 fun x _ acc => ?_
      have hm : m * (x + 1) = m + m * x := by ring
      rw [hm, List.drop_drop]
    rw [hcongr, ih (bs.drop m) hdrop_len]
    simp only [Nat.mul_zero, List.drop_zero]
    have hsplit : bs = bs.take m ++ bs.drop m := (List.take_append_drop m bs).symm
    conv_rhs => rw [hsplit]
    rw [packBytesLE_append, htake_len]

private theorem eval_natListLitE {ℓ : ℕ} {O : _root_.ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} (ks : List ℕ) (ρ : Env Γ) :
    (natListLitE (O := O) ks).eval ρ = ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [natListLitE, Expr.eval, ih]

private theorem msgPreamble_byte_1_0 (b : BitVec 8) :
    (match CryptoVerification.LibsignalSpqrV1.msgPreamble [b, 1#8, 0#8] with
      | .ok p => some (p.version, (p.epoch, (p.index, p.remaining.take [b, 1#8, 0#8].length)))
      | .error _ => none) = some (b, (1#64, (0, []))) := by
  revert b
  decide

private theorem eval_byte1ToNatE {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 1)) (ρ : Env Γ) (b : BitVec 8)
    (he : e.eval ρ = [b]) :
    (byte1ToNatE e).eval ρ = b.toNat := by
  have h1 : (adapterPureOp (decT := decT) (encT := encT) (.bytesLit 2 [1#8, 0#8])
      (Γ := Γ) .unit).eval ρ = [1#8, 0#8] := eval_adapterPureOp _ _ _
  have h2 : (adapterPureOp (decT := decT) (encT := encT) (.bytesCat 1 2)
      (.pair e (adapterPureOp (.bytesLit 2 [1#8, 0#8]) .unit))).eval ρ = [b, 1#8, 0#8] := by
    refine (eval_adapterPureOp _ _ _).trans ?_
    change e.eval ρ ++ _ = [b, 1#8, 0#8]
    rw [he, h1]; rfl
  have h3 : (adapterPureOp (decT := decT) (encT := encT) (.bytesWiden 3 29)
      (adapterPureOp (.bytesCat 1 2)
        (.pair e (adapterPureOp (.bytesLit 2 [1#8, 0#8]) .unit)))).eval ρ = [b, 1#8, 0#8] :=
    (eval_adapterPureOp _ _ _).trans h2
  have h4 : (adapterPureOp (decT := decT) (encT := encT) .spqrParsePreamble
      (adapterPureOp (.bytesWiden 3 29)
        (adapterPureOp (.bytesCat 1 2)
          (.pair e (adapterPureOp (.bytesLit 2 [1#8, 0#8]) .unit))))).eval ρ =
      some (b, (1#64, (0, []))) :=
    (eval_adapterPureOp _ _ _).trans
      ((congrArg (E2EPureOp.eval ℓ .spqrParsePreamble) h3).trans (msgPreamble_byte_1_0 b))
  unfold byte1ToNatE
  rw [Expr.eval, h4]
  rfl

private theorem eval_pack8BytesE {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 8)) (ρ : Env Γ) (bs : Bytes)
    (he : e.eval ρ = bs) (hbs : bs.length = 8) :
    (pack8BytesE e).eval ρ = packBytesLE bs := by
  unfold pack8BytesE
  dsimp only [Expr.eval]
  rw [he, eval_natListLitE]
  have htake8 : (List.range 8).take 8 = List.range 8 := by decide
  rw [htake8]
  rw [foldr_congr_mem 0 (g := fun i acc => packBytesLE ((bs.drop (1 * i)).take 1) + 256 ^ 1 * acc)]
  · exact foldr_range_packBytesLE 8 1 bs (by omega)
  · intro i hi acc
    rw [List.mem_range] at hi
    have hget : (bs.drop i).take 1 = [bs[i]'(by omega)] := by
      rw [List.take_one_drop_eq_of_lt_length (by omega)]; rfl
    have h1 : (adapterPureOp (decT := decT) (encT := encT) (.bytesDrop 8)
        (Γ := Ty.nat :: Ty.nat :: B 8 :: Γ) (.pair .v0 .v2)).eval
        (.cons i (.cons acc (.cons bs ρ))) = bs.drop i := eval_adapterPureOp _ _ _
    have h2 : (adapterPureOp (decT := decT) (encT := encT) (.bytesTakeK 8 1)
        (Γ := Ty.nat :: Ty.nat :: B 8 :: Γ)
        (adapterPureOp (.bytesDrop 8) (.pair .v0 .v2))).eval
        (.cons i (.cons acc (.cons bs ρ))) = [bs[i]'(by omega)] :=
      (eval_adapterPureOp _ _ _).trans ((congrArg (fun x : Bytes => x.take 1) h1).trans hget)
    change (byte1ToNatE _).eval _ + 256 * acc = _
    rw [eval_byte1ToNatE _ _ _ h2]
    simp only [Nat.one_mul, pow_one, hget, packBytesLE, Nat.mul_zero, Nat.add_zero]

private theorem eval_pack32PbytesE {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 32)) (ρ : Env Γ) (ub : SignalPqxdh.Bytes)
    (he : e.eval ρ = ub) (hub : ub.length = 32) :
    (pack32PbytesE e).eval ρ = packBytesLE (ofU8 ub) := by
  have hbs : (ofU8 ub).length = 32 := by simp [ofU8, hub]
  have hp : (adapterPureOp (decT := decT) (encT := encT) (.pbytesToBytes 32) e).eval ρ =
      ofU8 ub := (eval_adapterPureOp _ _ _).trans (congrArg ofU8 he)
  unfold pack32PbytesE
  dsimp only [Expr.eval]
  rw [hp, eval_natListLitE]
  have htake4 : (List.range 4).take 4 = List.range 4 := by decide
  rw [htake4]
  rw [foldr_congr_mem 0 (g := fun i acc =>
    packBytesLE (((ofU8 ub).drop (8 * i)).take 8) + 256 ^ 8 * acc)]
  · exact foldr_range_packBytesLE 4 8 (ofU8 ub) (by omega)
  · intro i hi acc
    rw [List.mem_range] at hi
    have h1 : (adapterPureOp (decT := decT) (encT := encT) (.bytesDrop 32)
        (Γ := Ty.nat :: Ty.nat :: B 32 :: Γ) (.pair (.mulK 8 .v0) .v2)).eval
        (.cons i (.cons acc (.cons (ofU8 ub) ρ))) = (ofU8 ub).drop (8 * i) := eval_adapterPureOp _ _ _
    have h2 : (adapterPureOp (decT := decT) (encT := encT) (.bytesTakeK 32 8)
        (Γ := Ty.nat :: Ty.nat :: B 32 :: Γ)
        (adapterPureOp (.bytesDrop 32) (.pair (.mulK 8 .v0) .v2))).eval
        (.cons i (.cons acc (.cons (ofU8 ub) ρ))) = ((ofU8 ub).drop (8 * i)).take 8 :=
      (eval_adapterPureOp _ _ _).trans (congrArg (fun x : Bytes => x.take 8) h1)
    change (pack8BytesE _).eval _ + 256 ^ 8 * acc = _
    rw [eval_pack8BytesE _ _ _ h2 (by rw [List.length_take, List.length_drop]; omega)]

private theorem eval_pack56BytesE {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 56)) (ρ : Env Γ) (bs : Bytes)
    (he : e.eval ρ = bs) (hbs : bs.length = 56) :
    (pack56BytesE e).eval ρ = packBytesLE bs := by
  unfold pack56BytesE
  dsimp only [Expr.eval]
  rw [he, eval_natListLitE]
  have htake7 : (List.range 7).take 7 = List.range 7 := by decide
  rw [htake7]
  rw [foldr_congr_mem 0 (g := fun i acc => packBytesLE ((bs.drop (8 * i)).take 8) + 256 ^ 8 * acc)]
  · exact foldr_range_packBytesLE 7 8 bs (by omega)
  · intro i hi acc
    rw [List.mem_range] at hi
    have h1 : (adapterPureOp (decT := decT) (encT := encT) (.bytesDrop 56)
        (Γ := Ty.nat :: Ty.nat :: B 56 :: Γ) (.pair (.mulK 8 .v0) .v2)).eval
        (.cons i (.cons acc (.cons bs ρ))) = bs.drop (8 * i) := eval_adapterPureOp _ _ _
    have h2 : (adapterPureOp (decT := decT) (encT := encT) (.bytesTakeK 56 8)
        (Γ := Ty.nat :: Ty.nat :: B 56 :: Γ)
        (adapterPureOp (.bytesDrop 56) (.pair (.mulK 8 .v0) .v2))).eval
        (.cons i (.cons acc (.cons bs ρ))) = (bs.drop (8 * i)).take 8 :=
      (eval_adapterPureOp _ _ _).trans (congrArg (fun x : Bytes => x.take 8) h1)
    change (pack8BytesE _).eval _ + 256 ^ 8 * acc = _
    rw [eval_pack8BytesE _ _ _ h2 (by rw [List.length_take, List.length_drop]; omega)]

private theorem eval_pack392BytesE {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 392)) (ρ : Env Γ) (bs : Bytes)
    (he : e.eval ρ = bs) (hbs : bs.length = 392) :
    (pack392BytesE e).eval ρ = packBytesLE bs := by
  unfold pack392BytesE
  dsimp only [Expr.eval]
  rw [he, eval_natListLitE]
  have htake7 : (List.range 7).take 7 = List.range 7 := by decide
  rw [htake7]
  rw [foldr_congr_mem 0 (g := fun i acc =>
    packBytesLE ((bs.drop (56 * i)).take 56) + 256 ^ 56 * acc)]
  · exact foldr_range_packBytesLE 7 56 bs (by omega)
  · intro i hi acc
    rw [List.mem_range] at hi
    have h1 : (adapterPureOp (decT := decT) (encT := encT) (.bytesDrop 392)
        (Γ := Ty.nat :: Ty.nat :: B 392 :: Γ) (.pair (.mulK 56 .v0) .v2)).eval
        (.cons i (.cons acc (.cons bs ρ))) = bs.drop (56 * i) := eval_adapterPureOp _ _ _
    have h2 : (adapterPureOp (decT := decT) (encT := encT) (.bytesTakeK 392 56)
        (Γ := Ty.nat :: Ty.nat :: B 392 :: Γ)
        (adapterPureOp (.bytesDrop 392) (.pair (.mulK 56 .v0) .v2))).eval
        (.cons i (.cons acc (.cons bs ρ))) = (bs.drop (56 * i)).take 56 :=
      (eval_adapterPureOp _ _ _).trans (congrArg (fun x : Bytes => x.take 56) h1)
    change (pack56BytesE _).eval _ + 256 ^ 56 * acc = _
    rw [eval_pack56BytesE _ _ _ h2 (by rw [List.length_take, List.length_drop]; omega)]

private theorem eval_pack1568Key4E {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 1568)) (ρ : Env Γ) (ub : SignalPqxdh.Bytes)
    (he : e.eval ρ = ub) (hub : ub.length = 1568) :
    (pack1568Key4E e).eval ρ = pack1568Key4 ub := by
  have hbs : (ofU8 ub).length = 1568 := by simp [ofU8, hub]
  have hp : (adapterPureOp (decT := decT) (encT := encT) (.pbytesToBytes 1568) e).eval ρ =
      ofU8 ub := (eval_adapterPureOp _ _ _).trans (congrArg ofU8 he)
  have hlimb : ∀ off : ℕ, off + 392 ≤ 1568 →
      (pack392BytesE (decT := decT) (encT := encT) (Γ := B 1568 :: Γ)
        (adapterPureOp (.bytesTakeK 1568 392)
          (adapterPureOp (.bytesDrop 1568) (.pair (.nat off) .v0)))).eval
        (.cons (ofU8 ub) ρ) = packBytesLE (((ofU8 ub).drop off).take 392) := by
    intro off hoff
    have h1 : (adapterPureOp (decT := decT) (encT := encT) (.bytesDrop 1568)
        (Γ := B 1568 :: Γ) (.pair (.nat off) .v0)).eval (.cons (ofU8 ub) ρ) =
        (ofU8 ub).drop off := eval_adapterPureOp _ _ _
    have h2 : (adapterPureOp (decT := decT) (encT := encT) (.bytesTakeK 1568 392)
        (Γ := B 1568 :: Γ)
        (adapterPureOp (.bytesDrop 1568) (.pair (.nat off) .v0))).eval (.cons (ofU8 ub) ρ) =
        ((ofU8 ub).drop off).take 392 :=
      (eval_adapterPureOp _ _ _).trans (congrArg (fun x : Bytes => x.take 392) h1)
    exact eval_pack392BytesE _ _ _ h2 (by rw [List.length_take, List.length_drop]; omega)
  unfold pack1568Key4E pack1568Key4
  dsimp only [Expr.eval]
  rw [hp, hlimb 0 (by omega), hlimb 392 (by omega), hlimb 784 (by omega), hlimb 1176 (by omega)]

private theorem eval_tset2E {ℓ : ℕ} {O : _root_.ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl t))) (k0 k1 : Expr O Γ .nat) (val : Expr O Γ t)
    (ρ : Env Γ) (i0 i1 : ℕ) :
    ((tset2E m k0 k1 val).eval ρ) i0 i1 =
      if i0 = k0.eval ρ ∧ i1 = k1.eval ρ then val.eval ρ else (m.eval ρ) i0 i1 := by
  by_cases h0 : i0 = k0.eval ρ <;> by_cases h1 : i1 = k1.eval ρ <;>
    simp [tset2E, Expr.eval, Expr.v0, _root_.ReductionDsl.Env.get, h0, h1]

private theorem eval_tset3E {ℓ : ℕ} {O : _root_.ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl (.tbl t)))) (k0 k1 k2 : Expr O Γ .nat) (val : Expr O Γ t)
    (ρ : Env Γ) (i0 i1 i2 : ℕ) :
    ((tset3E m k0 k1 k2 val).eval ρ) i0 i1 i2 =
      if i0 = k0.eval ρ ∧ i1 = k1.eval ρ ∧ i2 = k2.eval ρ then val.eval ρ
      else (m.eval ρ) i0 i1 i2 := by
  by_cases h0 : i0 = k0.eval ρ <;> by_cases h1 : i1 = k1.eval ρ <;>
    by_cases h2 : i2 = k2.eval ρ <;>
    simp [tset3E, Expr.eval, Expr.v0, Expr.v1, _root_.ReductionDsl.Env.get, h0, h1, h2]

private theorem eval_tset6E {ℓ : ℕ} {O : _root_.ReductionDsl.Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (m : Expr O Γ (.tbl (.tbl (.tbl (.tbl (.tbl (.tbl t)))))))
    (k0 k1 k2 k3 k4 k5 : Expr O Γ .nat) (val : Expr O Γ t)
    (ρ : Env Γ) (i0 i1 i2 i3 i4 i5 : ℕ) :
    ((tset6E m k0 k1 k2 k3 k4 k5 val).eval ρ) i0 i1 i2 i3 i4 i5 =
      if i0 = k0.eval ρ ∧ i1 = k1.eval ρ ∧ i2 = k2.eval ρ ∧
         i3 = k3.eval ρ ∧ i4 = k4.eval ρ ∧ i5 = k5.eval ρ then val.eval ρ
      else (m.eval ρ) i0 i1 i2 i3 i4 i5 := by
  dsimp only [tset6E, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, _root_.ReductionDsl.Env.get]
  by_cases h0 : i0 = k0.eval ρ <;> by_cases h1 : i1 = k1.eval ρ <;>
    by_cases h2 : i2 = k2.eval ρ <;>
    by_cases h3 : i3 = k3.eval ρ ∧ i4 = k4.eval ρ ∧ i5 = k5.eval ρ <;>
    simp [h0, h1, h2, h3, eval_tset3E, Expr.eval, _root_.ReductionDsl.Env.get]

private theorem sendsOpkTblOfList_eq_find? {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (l : List (SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr))
    (u : Fin S.N_id) (i : Fin S.N_send_opk) :
    sendsOpkTblOfList (ℓ := ℓ) l u.val i.val =
      (l.find? (fun (s, _, _) => s == .sendOPK u i)).map
        (fun (_, bnd, hdr) => (CryptoVerification.E2E.Costed.bundleV (ℓ := ℓ) bnd,
          CryptoVerification.E2E.Costed.hdrV (ℓ := ℓ) hdr)) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨s, bnd, hdr⟩
    cases s with
    | sendOPK u' i' =>
      simp only [sendsOpkTblOfList, List.foldr_cons, List.find?_cons]
      by_cases h : u.val = u'.val ∧ i.val = i'.val
      · have heq : SignalPqxdh.SessionId.sendOPK u' i' = .sendOPK u i := by
          rw [Fin.ext h.1.symm, Fin.ext h.2.symm]
        simp [h, heq]
      · have hne : (SignalPqxdh.SessionId.sendOPK u' i' == .sendOPK u i) = false := by
          rw [beq_eq_false_iff_ne]
          intro hc; cases hc; exact h ⟨rfl, rfl⟩
        simp [h, hne, ← ih]; rfl
    | sendNoOPK _ _ =>
      simp [sendsOpkTblOfList, ← ih]
    | recvOPK _ _ _ =>
      simp [sendsOpkTblOfList, ← ih]
    | recvNoOPK _ _ _ =>
      simp [sendsOpkTblOfList, ← ih]

private theorem sendsNoOpkTblOfList_eq_find? {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (l : List (SignalPqxdh.SessionId S × SignalPqxdh.PreKeyBundleInput × SignalPqxdh.HandshakeHdr))
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) :
    sendsNoOpkTblOfList (ℓ := ℓ) l u.val i.val =
      (l.find? (fun (s, _, _) => s == .sendNoOPK u i)).map
        (fun (_, bnd, hdr) => (CryptoVerification.E2E.Costed.bundleV (ℓ := ℓ) bnd,
          CryptoVerification.E2E.Costed.hdrV (ℓ := ℓ) hdr)) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨s, bnd, hdr⟩
    cases s with
    | sendNoOPK u' i' =>
      simp only [sendsNoOpkTblOfList, List.foldr_cons, List.find?_cons]
      by_cases h : u.val = u'.val ∧ i.val = i'.val
      · have heq : SignalPqxdh.SessionId.sendNoOPK u' i' = .sendNoOPK u i := by
          rw [Fin.ext h.1.symm, Fin.ext h.2.symm]
        simp [h, heq]
      · have hne : (SignalPqxdh.SessionId.sendNoOPK u' i' == .sendNoOPK u i) = false := by
          rw [beq_eq_false_iff_ne]
          intro hc; cases hc; exact h ⟨rfl, rfl⟩
        simp [h, hne, ← ih]; rfl
    | sendOPK _ _ =>
      simp [sendsNoOpkTblOfList, ← ih]
    | recvOPK _ _ _ =>
      simp [sendsNoOpkTblOfList, ← ih]
    | recvNoOPK _ _ _ =>
      simp [sendsNoOpkTblOfList, ← ih]

private theorem bundlesTblOfList_eq_find? {S : SignalPqxdh.Setup}
    (l : List ((Fin S.N_id × Fin S.N_recv) × SignalPqxdh.Bytes × SignalPqxdh.Bytes))
    (hSz : ∀ e ∈ l, e.2.1.length = 32 ∧ e.2.2.length = 1568)
    (bnd : SignalPqxdh.PreKeyBundleInput) (hdr : SignalPqxdh.HandshakeHdr)
    (hSpk : bnd.spkB.length = 32) (hPq : bnd.pqspkB.length = 1568)
    (hHdrId : hdr.spkId = hdr.pqspkId) :
    bundlesTblOfList l hdr.spkId.toNat (packBytesLE (ofU8 bnd.spkB))
      (pack1568Key4 bnd.pqspkB).1 (pack1568Key4 bnd.pqspkB).2.1
      (pack1568Key4 bnd.pqspkB).2.2.1 (pack1568Key4 bnd.pqspkB).2.2.2 =
    (l.find? (fun ((_, j), (spkB, pqspkB)) =>
      spkB == bnd.spkB && pqspkB == bnd.pqspkB &&
      hdr.spkId == UInt32.ofNat j.val &&
      hdr.pqspkId == UInt32.ofNat j.val)).map Prod.fst := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨⟨u, j⟩, spkB, pqspkB⟩
    obtain ⟨heSpk, hePq⟩ := hSz _ (List.mem_cons_self ..)
    have ih' := ih (fun x hx => hSz x (List.mem_cons_of_mem _ hx))
    simp only [bundlesTblOfList, List.foldr_cons, List.find?_cons]
    have hEqSpk : (packBytesLE (ofU8 bnd.spkB) = packBytesLE (ofU8 spkB)) ↔ spkB = bnd.spkB := by
      constructor
      · intro hp
        exact (ofU8_inj (packBytesLE_inj_of_length_eq (by simp [ofU8, hSpk, heSpk]) hp)).symm
      · rintro rfl; rfl
    have hEqPq :
        ((pack1568Key4 bnd.pqspkB).1 = (pack1568Key4 pqspkB).1 ∧
         (pack1568Key4 bnd.pqspkB).2.1 = (pack1568Key4 pqspkB).2.1 ∧
         (pack1568Key4 bnd.pqspkB).2.2.1 = (pack1568Key4 pqspkB).2.2.1 ∧
         (pack1568Key4 bnd.pqspkB).2.2.2 = (pack1568Key4 pqspkB).2.2.2) ↔
        pqspkB = bnd.pqspkB := by
      constructor
      · rintro ⟨h0, h1, h2, h3⟩
        exact (pack1568Key4_inj hPq hePq (Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3)))).symm
      · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
    have hEqJ : hdr.spkId.toNat = (UInt32.ofNat j.val).toNat ↔ hdr.spkId = UInt32.ofNat j.val :=
      ⟨fun h => UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h), congrArg UInt32.toNat⟩
    by_cases hCond :
        hdr.spkId.toNat = (UInt32.ofNat j.val).toNat ∧
        packBytesLE (ofU8 bnd.spkB) = packBytesLE (ofU8 spkB) ∧
        (pack1568Key4 bnd.pqspkB).1 = (pack1568Key4 pqspkB).1 ∧
        (pack1568Key4 bnd.pqspkB).2.1 = (pack1568Key4 pqspkB).2.1 ∧
        (pack1568Key4 bnd.pqspkB).2.2.1 = (pack1568Key4 pqspkB).2.2.1 ∧
        (pack1568Key4 bnd.pqspkB).2.2.2 = (pack1568Key4 pqspkB).2.2.2
    · obtain ⟨hj, hs, hp0, hp1, hp2, hp3⟩ := hCond
      have h1 : spkB = bnd.spkB := hEqSpk.mp hs
      have h2 : pqspkB = bnd.pqspkB := hEqPq.mp ⟨hp0, hp1, hp2, hp3⟩
      have h3 : hdr.spkId = UInt32.ofNat j.val := hEqJ.mp hj
      have h4 : hdr.pqspkId = UInt32.ofNat j.val := hHdrId.symm.trans h3
      simp [hs, hp0, hp1, hp2, hp3, h1, h2, h3, h4]
    · have hBool :
          (spkB == bnd.spkB && pqspkB == bnd.pqspkB &&
           hdr.spkId == UInt32.ofNat j.val && hdr.pqspkId == UInt32.ofNat j.val) = false := by
        rw [Bool.eq_false_iff]
        intro hT
        simp only [Bool.and_eq_true, beq_iff_eq] at hT
        rcases hT with ⟨⟨⟨h1, h2⟩, h3⟩, _⟩
        exact hCond ⟨hEqJ.mpr h3, hEqSpk.mpr h1, hEqPq.mpr h2⟩
      simp only [hCond, ↓reduceIte, hBool]
      exact ih'

private theorem prinsTblOfList_eq_any {S : SignalPqxdh.Setup}
    (l : List (Fin S.N_id × SignalPqxdh.Bytes))
    (hNodup : (l.map Prod.fst).Nodup)
    (u : Fin S.N_id) (ikB : SignalPqxdh.Bytes) :
    (match prinsTblOfList l u.val with
      | none => false
      | some pk => pk == ikB) =
    l.any (fun (u', pk) => u' == u && pk == ikB) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨u', pk'⟩
    rw [List.map_cons, List.nodup_cons] at hNodup
    obtain ⟨hNotMem, hNodupRest⟩ := hNodup
    simp only [prinsTblOfList, List.foldr_cons, List.any_cons]
    by_cases hu : u.val = u'.val
    · have huEq : u' = u := Fin.ext hu.symm
      have hNone : rest.any (fun (u'', pk) => u'' == u && pk == ikB) = false := by
        rw [List.any_eq_false]
        rintro ⟨u'', pk⟩ hmem
        simp only [Bool.and_eq_true, beq_iff_eq, not_and]
        intro hu'' _
        exact hNotMem (List.mem_map.mpr ⟨(u'', pk), hmem, hu''.trans huEq.symm⟩)
      rw [hNone]
      simp [hu, huEq]
    · have huNe : (u' == u) = false := by
        rw [beq_eq_false_iff_ne]; intro hc; exact hu (congrArg Fin.val hc.symm)
      simp [hu, huNe, ← ih hNodupRest]
      rfl

private theorem opksTblOfList_eq_any {S : SignalPqxdh.Setup}
    (l : List ((Fin S.N_id × Fin S.N_recv × Fin S.N_opk) × SignalPqxdh.Bytes))
    (hNodup : (l.map Prod.fst).Nodup)
    (u : Fin S.N_id) (j : Fin S.N_recv) (opkId : UInt32) (opkPk : SignalPqxdh.Bytes) :
    (match opksTblOfList l u.val j.val opkId.toNat with
      | none => false
      | some pk => pk == opkPk) =
    l.any (fun ((u', j', o), pk) =>
      u' == u && j' == j && UInt32.ofNat o.val == opkId &&
      o.val == opkId.toNat && pk == opkPk) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨⟨u', j', o⟩, pk'⟩
    rw [List.map_cons, List.nodup_cons] at hNodup
    obtain ⟨hNotMem, hNodupRest⟩ := hNodup
    simp only [opksTblOfList, List.foldr_cons, List.any_cons]
    by_cases hk : u.val = u'.val ∧ j.val = j'.val ∧ opkId.toNat = o.val
    · obtain ⟨hu, hj, ho⟩ := hk
      have huEq : u' = u := Fin.ext hu.symm
      have hjEq : j' = j := Fin.ext hj.symm
      have hoU32 : UInt32.ofNat o.val = opkId := by
        rw [← ho]; exact UInt32.ofNat_toNat
      have hRestFalse : rest.any (fun ((u'', j'', o''), pk) =>
          u'' == u && j'' == j && UInt32.ofNat o''.val == opkId &&
          o''.val == opkId.toNat && pk == opkPk) = false := by
        rw [List.any_eq_false]
        rintro ⟨⟨u'', j'', o''⟩, pk⟩ hmem
        simp only [Bool.and_eq_true, beq_iff_eq]
        rintro ⟨⟨⟨⟨hu'', hj''⟩, _⟩, ho''⟩, _⟩
        have hEqKey : (u'', j'', o'') = (u', j', o) := by
          rw [hu'', hj'', huEq, hjEq, Fin.ext (ho''.trans ho)]
        exact hNotMem (List.mem_map.mpr ⟨((u'', j'', o''), pk), hmem, hEqKey⟩)
      rw [hRestFalse]
      simp [hu, hj, ho, huEq, hjEq, hoU32]
    · have hHeadFalse :
          (u' == u && j' == j && UInt32.ofNat o.val == opkId &&
           o.val == opkId.toNat && pk' == opkPk) = false := by
        rw [Bool.eq_false_iff]
        intro hT
        simp only [Bool.and_eq_true, beq_iff_eq] at hT
        rcases hT with ⟨⟨⟨⟨rfl, rfl⟩, _⟩, ho⟩, _⟩
        exact hk ⟨rfl, rfl, ho.symm⟩
      simp only [hk, ↓reduceIte, hHeadFalse, Bool.false_or]
      exact ih hNodupRest

private theorem eval_stepBaseMirrorTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT)
    (d : ModelDriverBase S) (ρ : Env Γ)
    (hdrv : drv.eval ρ = drvMirrorTblToV (ℓ := ℓ) d)
    (hBndLen : ∀ u j b, keyIndQdec (ℓ := ℓ) (kq.eval ρ) = .genSPK u j →
      keyIndRdec (ℓ := ℓ) (kr.eval ρ) = .bundleResp b →
      b.spkB.length = 32 ∧ b.pqspkB.length = 1568) :
    (stepBaseMirrorTblExpr drv kq kr).eval ρ =
      drvMirrorTblToV (ℓ := ℓ)
        (bhBaseMirror d (keyIndQdec (ℓ := ℓ) (kq.eval ρ)) (keyIndRdec (ℓ := ℓ) (kr.eval ρ))) := by
  unfold stepBaseMirrorTblExpr
  change Expr.eval _
    (Env.cons (t := .prod (drvMirrorTblTy S ℓ) (.prod (keyIndQT S) keyIndRT))
      (drv.eval ρ, (kq.eval ρ, kr.eval ρ)) ρ) = _
  rw [hdrv]
  generalize kq.eval ρ = qv at *
  generalize kr.eval ρ = rv at *
  dsimp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6,
    env_get_zero, env_get_succ]
  rcases qv with
      u | (u | (⟨u, j⟩ | (⟨u, j, o⟩ | (⟨u, i, bnd⟩ | (⟨u, i, bnd⟩ | rest)))))
  · rcases rv with _ | (⟨ik, info⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;> rfl
  · rcases rv with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;> rfl
  · rcases rv with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _)))))))))
    all_goals try rfl
    rcases b with ⟨ikB, idSig, spkB, spkSig, opkB?, pqspk, pqspkB, pqspkSig⟩
    have ⟨hSpk, hPq⟩ := hBndLen u j _ rfl rfl
    dsimp only [bhBaseMirror, keyIndQdec, keyIndRdec, CryptoVerification.E2E.Costed.bundleOfV,
      drvMirrorTblToV] at hSpk hPq ⊢
    try simp only [_root_.ReductionDsl.Env.get]
    congr 1; congr 1
    funext i0 i1 i2 i3 i4 i5
    rw [eval_tset6E]
    simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v6, _root_.ReductionDsl.Env.get,
      eval_adapterPureOp, E2EPureOp.eval]
    rw [eval_pack1568Key4E _ _ pqspkB (by simp [Expr.eval, Expr.v0, _root_.ReductionDsl.Env.get]) hPq,
      eval_pack32PbytesE _ _ spkB (by simp [Expr.eval, Expr.v0, Expr.v1, _root_.ReductionDsl.Env.get]) hSpk]
    simp only [Expr.eval, _root_.ReductionDsl.Env.get, bundlesTblOfList, List.foldr_cons]
  · rcases rv with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _)))))))))
    all_goals try rfl
    dsimp only [bhBaseMirror, keyIndQdec, keyIndRdec, drvMirrorTblToV]
    try simp only [_root_.ReductionDsl.Env.get]
    congr 1; congr 1; congr 1
    funext i0 i1 i2
    rw [eval_tset3E]
    simp [Expr.eval, Expr.v0, Expr.v3, _root_.ReductionDsl.Env.get,
      eval_adapterPureOp, E2EPureOp.eval, opksTblOfList]
    by_cases hcond : i0 = u.val ∧ i1 = j.val ∧ i2 = o.val <;> simp only [hcond, ↓reduceIte]
  · rcases rv with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _)))))))))
    all_goals try rfl
    dsimp only [bhBaseMirror, keyIndQdec, keyIndRdec, drvMirrorTblToV]
    try simp only [_root_.ReductionDsl.Env.get]
    congr 1; congr 1; congr 1; congr 1
    funext i0 i1
    rw [eval_tset2E]
    simp [Expr.eval, Expr.v0, Expr.v6, _root_.ReductionDsl.Env.get,
      eval_adapterPureOp, E2EPureOp.eval, sendsOpkTblOfList,
      Computational.Proofs.E2E.Dsl.TablesHonest.bundleV_bundleOfV,
      Computational.Proofs.E2E.Dsl.TablesHonest.hdrV_hdrOfV]
    by_cases hcond : i0 = u.val ∧ i1 = i.val <;> simp only [hcond, ↓reduceIte]
  · rcases rv with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _)))))))))
    all_goals try rfl
    dsimp only [bhBaseMirror, keyIndQdec, keyIndRdec, drvMirrorTblToV]
    try simp only [_root_.ReductionDsl.Env.get]
    congr 1; congr 1; congr 1; congr 1
    funext i0 i1
    rw [eval_tset2E]
    simp [Expr.eval, Expr.v0, Expr.v6, _root_.ReductionDsl.Env.get,
      eval_adapterPureOp, E2EPureOp.eval, sendsNoOpkTblOfList,
      Computational.Proofs.E2E.Dsl.TablesHonest.bundleV_bundleOfV,
      Computational.Proofs.E2E.Dsl.TablesHonest.hdrV_hdrOfV]
    by_cases hcond : i0 = u.val ∧ i1 = i.val <;> simp only [hcond, ↓reduceIte]
  · rcases rest with _ | (_ | (_ | (_ | (_ | (_ | (_ | _)))))) <;>
      rcases rv with _ | (⟨ik, _⟩ | (pk | (_ | (b | (h | (_ | (_ | (_ | (_ | _))))))))) <;>
      rfl

private theorem eval_caseOpt {S0 : Sig} {O0 : _root_.ReductionDsl.Ops S0}
    {Γ0 : List (Ty S0)} {t u : Ty S0}
    (a : Expr O0 Γ0 (.opt t)) (b : Expr O0 Γ0 u) (c : Expr O0 (t :: Γ0) u) (ρ : Env Γ0) :
    (Expr.caseOpt a b c).eval ρ =
      match a.eval ρ with
      | none => b.eval ρ
      | some v => c.eval (Env.cons v ρ) := rfl

set_option linter.unusedSimpArgs false in
private theorem eval_guardPromoteTblExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S))
    (d : ModelDriverBase S) (ρ : Env Γ)
    (hdrv : drv.eval ρ = drvMirrorTblToV (ℓ := ℓ) d)
    (hSendsInit : ∀ x ∈ d.sends,
      (match x.1 with | .sendOPK _ _ | .sendNoOPK _ _ => true | _ => false) = true)
    (hBundlesSz : ∀ e ∈ d.bundles, e.2.1.length = 32 ∧ e.2.2.length = 1568)
    (hPrinsNodup : (d.prins.map Prod.fst).Nodup)
    (hOpksNodup : (d.opks.map Prod.fst).Nodup) :
    (guardPromoteTblExpr drv sid).eval ρ =
      ((bhShallowStepMirrorGuard
        (.inr (d, sidOfV (ℓ := ℓ) (sid.eval ρ)))).2).map (instMetaToV (ℓ := ℓ)) := by
  unfold guardPromoteTblExpr
  change Expr.eval _
    (Env.cons (t := .prod (drvMirrorTblTy S ℓ) (sidT S)) (drv.eval ρ, sid.eval ρ) ρ) = _
  rw [hdrv]
  generalize sid.eval ρ = sv at *
  let ρ0 := Env.cons (t := .prod (drvMirrorTblTy S ℓ) (sidT S)) (drvMirrorTblToV (ℓ := ℓ) d, sv) ρ
  let sendsLookupE : Expr (e2eAdapterOps ℓ decT encT)
      (.prod (drvMirrorTblTy S ℓ) (sidT S) :: Γ) (.opt (.prod bundleT hdrT)) :=
    .caseSum (.snd .v0)
      (.tget
        (.tget (.fst (.snd (.snd (.snd (.fst .v1)))))
          (adapterPureOp (.finVal S.N_id) (.fst .v0)))
        (adapterPureOp (.finVal S.N_send_opk) (.snd .v0)))
      (.caseSum .v0
        (.tget
          (.tget (.snd (.snd (.snd (.snd (.fst .v2)))))
            (adapterPureOp (.finVal S.N_id) (.fst .v0)))
          (adapterPureOp (.finVal S.N_send_no_opk) (.snd .v0)))
        .none)
  have hSendsEq :
      sendsLookupE.eval ρ0 =
      (d.sends.find? (fun (s, _, _) => s == sidOfV (ℓ := ℓ) sv)).map
        (fun (_, bnd, hdr) => (bundleV (ℓ := ℓ) bnd, hdrV (ℓ := ℓ) hdr)) := by
    rcases sv with ⟨u, i⟩ | (⟨u, i⟩ | (⟨k, j, o⟩ | ⟨k, j, l⟩))
    · simp only [sendsLookupE, ρ0, Expr.eval, Expr.v0, Expr.v1, _root_.ReductionDsl.Env.get,
        eval_adapterPureOp, E2EPureOp.eval, drvMirrorTblToV, sidOfV]
      exact sendsOpkTblOfList_eq_find? d.sends u i
    · simp only [sendsLookupE, ρ0, Expr.eval, Expr.v0, Expr.v1, Expr.v2, _root_.ReductionDsl.Env.get,
        eval_adapterPureOp, E2EPureOp.eval, drvMirrorTblToV, sidOfV]
      exact sendsNoOpkTblOfList_eq_find? d.sends u i
    · simp only [sendsLookupE, ρ0, Expr.eval, Expr.v0, _root_.ReductionDsl.Env.get, sidOfV]
      symm; rw [Option.map_eq_none_iff, List.find?_eq_none]
      rintro ⟨s, _, _⟩ hmem
      have hInit := hSendsInit _ hmem
      cases s <;> simp at hInit ⊢
    · simp only [sendsLookupE, ρ0, Expr.eval, Expr.v0, _root_.ReductionDsl.Env.get, sidOfV]
      symm; rw [Option.map_eq_none_iff, List.find?_eq_none]
      rintro ⟨s, _, _⟩ hmem
      have hInit := hSendsInit _ hmem
      cases s <;> simp at hInit ⊢
  dsimp only [bhShallowStepMirrorGuard]
  rw [eval_caseOpt, hSendsEq]
  cases hFindSend : d.sends.find? (fun (s, _, _) => s == sidOfV (ℓ := ℓ) sv) with
  | none => rfl
  | some sbh =>
    rcases sbh with ⟨sFound, bnd, hdr⟩
    dsimp only [Option.map]
    by_cases hPre : hdr.spkId = hdr.pqspkId ∧ bnd.spkB.length = 32 ∧ bnd.pqspkB.length = 1568
    · obtain ⟨hHdrId, hSpk, hPq⟩ := hPre
      have hPreTrue :
          (hdr.spkId == hdr.pqspkId &&
           (decide (bnd.spkB.length = 32) && decide (bnd.pqspkB.length = 1568))) = true := by
        simp [hHdrId, hSpk, hPq]
      simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, _root_.ReductionDsl.Env.get,
        eval_adapterPureOp, E2EPureOp.eval, bundleV, hdrV, PNat.val_ofNat, hPreTrue, ↓reduceIte]
      rw [eval_pack1568Key4E _ _ bnd.pqspkB
        (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v2, ρ0, _root_.ReductionDsl.Env.get, bundleV]) hPq]
      simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, ρ0, _root_.ReductionDsl.Env.get,
        eval_adapterPureOp, E2EPureOp.eval, bundleV, hdrV, drvMirrorTblToV]
      rw [eval_pack32PbytesE _ _ bnd.spkB
        (by simp [Expr.eval, Expr.v0, Expr.v1, Expr.v2, ρ0, _root_.ReductionDsl.Env.get, bundleV]) hSpk]
      rw [bundlesTblOfList_eq_find? d.bundles hBundlesSz bnd hdr hSpk hPq hHdrId]
      cases hBnd : d.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
          spkB == bnd.spkB && pqspkB == bnd.pqspkB &&
          hdr.spkId == UInt32.ofNat j.val && hdr.pqspkId == UInt32.ofNat j.val) with
      | none => rfl
      | some ujSpk =>
        rcases ujSpk with ⟨⟨u_resp, j_resp⟩, spkPair⟩
        dsimp only [Option.map]
        have hPrins := prinsTblOfList_eq_any d.prins hPrinsNodup u_resp bnd.ikB
        cases hopk : bnd.opkB? with
        | none =>
          have hOpkEq : bhBaseOpkOk d u_resp j_resp bnd = true := by
            simp [bhBaseOpkOk, hopk]
          simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, ρ0, _root_.ReductionDsl.Env.get,
            eval_adapterPureOp, E2EPureOp.eval, bundleV, hdrV, drvMirrorTblToV, hopk]
          conv_rhs => simp only [← hPrins, hOpkEq]
          cases prinsTblOfList d.prins u_resp.val with
          | none => simp
          | some pk =>
            by_cases h1 : pk = bnd.ikB
            · subst h1
              simp [instMetaToV, hdrV, eval_initRegIdExpr, Expr.eval, _root_.ReductionDsl.Env.get, ρ0]
            · simp [h1]
        | some opkPair =>
          rcases opkPair with ⟨opkId, opkPk⟩
          have hOpks := opksTblOfList_eq_any d.opks hOpksNodup u_resp j_resp opkId opkPk
          have hOpkEq : bhBaseOpkOk d u_resp j_resp bnd =
              match opksTblOfList d.opks u_resp.val j_resp.val opkId.toNat with
              | none => false
              | some pk => pk == opkPk := by
            simp [bhBaseOpkOk, hopk, ← hOpks]
          simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, ρ0,
            _root_.ReductionDsl.Env.get, eval_adapterPureOp, E2EPureOp.eval, bundleV, hdrV,
            drvMirrorTblToV, hopk]
          conv_rhs => simp only [← hPrins, hOpkEq]
          cases prinsTblOfList d.prins u_resp.val with
          | none => simp
          | some pk =>
            cases opksTblOfList d.opks u_resp.val j_resp.val opkId.toNat with
            | none => simp
            | some pk2 =>
              by_cases h1 : pk = bnd.ikB <;> by_cases h2 : pk2 = opkPk
              · subst h1; subst h2
                simp [instMetaToV, hdrV, eval_initRegIdExpr, Expr.eval, _root_.ReductionDsl.Env.get, ρ0]
              · simp [h1, h2]
              · simp [h1, h2]
              · simp [h1, h2]
    · have hPreFalse :
          (hdr.spkId == hdr.pqspkId &&
           (decide (bnd.spkB.length = 32) && decide (bnd.pqspkB.length = 1568))) = false := by
        rw [Bool.eq_false_iff]; intro hT
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hT
        exact hPre ⟨hT.1, hT.2.1, hT.2.2⟩
      have hBndNone :
          d.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
            spkB == bnd.spkB && pqspkB == bnd.pqspkB &&
            hdr.spkId == UInt32.ofNat j.val && hdr.pqspkId == UInt32.ofNat j.val) = none := by
        rw [List.find?_eq_none]
        rintro ⟨⟨u, j⟩, spkB, pqspkB⟩ hmem hT
        obtain ⟨heSpk, hePq⟩ := hBundlesSz _ hmem
        simp only [Bool.and_eq_true, beq_iff_eq] at hT
        rcases hT with ⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩
        exact hPre ⟨h1.trans h2.symm, heSpk, hePq⟩
      rw [hBndNone]
      simp only [Expr.eval, Expr.v0, Expr.v1, Expr.v2, _root_.ReductionDsl.Env.get,
        eval_adapterPureOp, E2EPureOp.eval, bundleV, hdrV, PNat.val_ofNat, hPreFalse,
        Bool.false_eq_true, ↓reduceIte, Option.map]

end TblAdapterCouplingHelpers
attribute [local simp] env_get_zero env_get_succ

private theorem pqxdhKeyIndImpl1KeyReal_genSPK_bundleResp_lengths
    {S : SignalPqxdh.Setup} (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (st st' : SignalPqxdh.KeyIndState S) (b : SignalPqxdh.PreKeyBundleInput)
    (h : (.bundleResp b, st') ∈
      support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (.genSPK u j)).run st)) :
    b.spkB.length = 32 ∧ b.pqspkB.length = 1568 := by
  dsimp only [SignalPqxdh.pqxdhKeyIndImpl1KeyReal, SignalPqxdh.pqxdhKeyIndImpl] at h
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
  split_ifs at h with hDup
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
    nomatch h
  · cases hFind : st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hFind] at h
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
      nomatch h
    | some pEntry =>
      rw [hFind] at h
      simp only [SignalPqxdh.sampleKemKeyGen, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
      rcases h with ⟨spkSk, _, _, _, seed, _, _, _, heq⟩
      injection heq with hResp _
      injection hResp with hb
      subst hb
      exact ⟨hP.x25519Base_len spkSk, (hP.kemKeyGen_valid seed).1⟩

private def BundlesValidLen {S : SignalPqxdh.Setup} (d : ModelDriverBase S) : Prop :=
  ∀ e ∈ d.bundles, e.2.1.length = 32 ∧ e.2.2.length = 1568

private theorem bundlesValidLen_bhBaseMirror {S : SignalPqxdh.Setup}
    (P : SignalPqxdh.Primitives) (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    {d : ModelDriverBase S} {st st' : SignalPqxdh.KeyIndState S}
    (hBnd : BundlesValidLen d)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (hStep : (kr, st') ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st)) :
    BundlesValidLen (bhBaseMirror d kq kr) := by
  cases kq with
  | genSPK u j =>
    cases kr with
    | bundleResp b =>
      have hLen := pqxdhKeyIndImpl1KeyReal_genSPK_bundleResp_lengths P hP u j st st' b hStep
      intro e he
      dsimp only [bhBaseMirror] at he
      rcases List.mem_cons.mp he with rfl | he'
      · exact hLen
      · exact hBnd e he'
    | _ => exact hBnd
  | _ =>
    cases kr <;> exact hBnd

private theorem env_get_zero_rfl {S0 : Sig} {Γ0 : List (Ty S0)} {t0 : Ty S0}
    (v : t0.denote) (ρ : Env Γ0) :
    (Env.cons v ρ).get Var.zero = v := rfl

private theorem env_get_succ_rfl {S0 : Sig} {Γ0 : List (Ty S0)} {t0 u0 : Ty S0}
    (v : u0.denote) (ρ : Env Γ0) (i : Var Γ0 t0) :
    (Env.cons v ρ).get (Var.succ i) = ρ.get i := rfl

private theorem MirrorKiInv.sends_init {S : SignalPqxdh.Setup} {d : ModelDriverBase S}
    {st : SignalPqxdh.KeyIndState S} (h : MirrorKiInv d st) :
    ∀ x ∈ d.sends,
      (match x.1 with | .sendOPK _ _ | .sendNoOPK _ _ => true | _ => false) = true := by
  rintro ⟨sid, b, hdr⟩ hx
  have h1 := (h.sends_sub (sid, b, hdr) hx).1
  cases sid <;> simp [initSidToSum?] at h1 ⊢

private def replaceDrv {ℓ : ℕ} {A B : Type} (b : B)
    (s : (ℕ → Option (adapterInstMetaT (ℓ := ℓ)).denote) × (ℕ → Bool) × A) :
    (ℕ → Option (adapterInstMetaT (ℓ := ℓ)).denote) × (ℕ → Bool) × B :=
  (s.1, (s.2.1, b))

private structure TblListCouplingInv {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (s_lst : (cliAdapterStateTy S ℓ).denote) (σ_e2e : BHE2EDrvState S ℓ) : Prop where
  mirror_ki : MirrorKiInv σ_e2e.toModelDriverBase σ_e2e.st
  bundles_sz : BundlesValidLen σ_e2e.toModelDriverBase
  drv_eq : s_lst.2.2 = drvMirrorToV (ℓ := ℓ) σ_e2e.toModelDriverBase

private theorem tblListCouplingInv_init {S : SignalPqxdh.Setup} {ℓ : ℕ} (b secb : Bool) :
    TblListCouplingInv (S := S) (ℓ := ℓ)
      (cliAdapterStateToV (ℓ := ℓ) (cliAdapterInitState S))
      { b := b, st := SignalPqxdh.KeyIndState.empty S secb } where
  mirror_ki := mirrorKiInv_empty _
  bundles_sz := fun _ h => nomatch h
  drv_eq := rfl

private def TblStepCoupledEq {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    (c_tbl : ProbComp ((α × (cliAdapterTblStateTy S ℓ).denote) × DrvLogState S ℓ))
    (c_lst : ProbComp ((α × (cliAdapterStateTy S ℓ).denote) × DrvLogState S ℓ)) : Prop :=
  c_tbl = (fun p =>
    ((p.1.1, replaceDrv (drvMirrorTblToV (ℓ := ℓ) p.2.1.toModelDriverBase) p.1.2), p.2)) <$>
      c_lst ∧
  ∀ out ∈ support c_lst, TblListCouplingInv out.1.2 out.2.1

private def cliHonestTblStepImplWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    QueryImpl (unifSpec + bhGameSpec S ℓ (BitVec 512))
      (StateT (cliAdapterTblStateTy S ℓ).denote (StateT (DrvLogState S ℓ) ProbComp)) := fun q =>
  StateT.mk fun s =>
    simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      ((handlerImpl (C := e2eBhAdapterCodec S ℓ)
        (I := e2eBhAdapterIface S ℓ)
        (cliAdapterHandleTbl decT encT S ℓ) q).run s)

private theorem simulateQ_cliE2EDrvImplWith_honestTbl_run
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} {α : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) α)
    (s : (cliAdapterTblStateTy S ℓ).denote) (σ_log : DrvLogState S ℓ) :
    (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      ((simulateQ (handlerImpl (C := e2eBhAdapterCodec S ℓ)
        (I := e2eBhAdapterIface S ℓ)
        (cliAdapterHandleTbl decT encT S ℓ)) oa).run s)).run σ_log =
    (((simulateQ (cliHonestTblStepImplWith P ki C K qep decT encT) oa).run s).run σ_log) := by
  induction oa using OracleComp.inductionOn generalizing s σ_log with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, simulateQ_bind, StateT.run_bind, run_simulateQ_query_bind,
      StateT.run_bind]
    exact bind_congr fun ⟨⟨r, s'⟩, σ_log'⟩ => ih r s' σ_log'

private theorem probComp_map_congr_support {α β : Type}
    (oa : ProbComp α) {f g : α → β}
    (h : ∀ a ∈ support oa, f a = g a) :
    f <$> oa = g <$> oa := by
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact probComp_bind_congr_support oa fun a ha => congrArg pure (h a ha)

private theorem run_simulateQ_map {ι : Type} {T : OracleSpec ι} {S0 α β : Type}
    (impl : QueryImpl T (StateT S0 ProbComp)) (f : α → β) (oa : OracleComp T α) (s : S0) :
    (simulateQ impl (f <$> oa)).run s = (fun p => (f p.1, p.2)) <$> (simulateQ impl oa).run s := by
  simp only [map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]

private def SmArmCoupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (dTbl : (drvMirrorTblTy S ℓ).denote) (dLst : (drvMirrorTy S ℓ).denote)
    (cTbl : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      ((e2eBhAdapterCodec S ℓ).R.denote × (cliAdapterTblStateTy S ℓ).denote))
    (cLst : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      ((e2eBhAdapterCodec S ℓ).R.denote × (cliAdapterStateTy S ℓ).denote)) : Prop :=
  cTbl = (fun p => (p.1, replaceDrv dTbl p.2)) <$> cLst ∧
  ∀ σ_e2e log out,
    out ∈ support ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT) cLst).run
      (σ_e2e, log)) →
    out.1.2.2.2 = dLst ∧ out.2.1.toModelDriverBase = σ_e2e.toModelDriverBase ∧ out.2.1.st = σ_e2e.st

private theorem support_run_drv_sm_bind {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt β : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (cont : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq →
      OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
        (β × (cliAdapterStateTy S ℓ).denote))
    (dLst : (drvMirrorTy S ℓ).denote)
    (hCont : ∀ r σ_e2e' log' out,
      out ∈ support ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT) (cont r)).run
        (σ_e2e', log')) →
      out.1.2.2.2 = dLst ∧ out.2.1.toModelDriverBase = σ_e2e'.toModelDriverBase ∧
        out.2.1.st = σ_e2e'.st)
    (σ_e2e : BHE2EDrvState S ℓ) (log : List (BitVec 512))
    (out : (β × (cliAdapterStateTy S ℓ).denote) × DrvLogState S ℓ)
    (hout : out ∈ support ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (.inr (.inr ⟨i, sq⟩))) >>=
        cont)).run (σ_e2e, log))) :
    out.1.2.2.2 = dLst ∧ out.2.1.toModelDriverBase = σ_e2e.toModelDriverBase ∧
      out.2.1.st = σ_e2e.st := by
  simp only [simulateQ_bind, StateT.run_bind] at hout
  rw [run_simulateQ_drv_sm] at hout
  simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hout
  rcases hout with ⟨⟨⟨smR, σ_mid⟩, w⟩, hSm, hRest⟩
  have hBaseMid := bhE2EStepLocalSm_base_st_eq C K qep decT encT i sq
    (mem_support_bhE2EStepLocalSm_of_coinLogged C K qep decT encT hSm)
  obtain ⟨hd, hb, hst⟩ := hCont _ σ_mid (log ++ w) out hRest
  exact ⟨hd, hb.trans hBaseMid.1, hst.trans hBaseMid.2⟩

private theorem smArm_ret {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))}
    {e1 : Expr (e2eAdapterOps ℓ decT encT) Γ1
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {e2 : Expr (e2eAdapterOps ℓ decT encT) Γ2
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (h : e1.eval ρ1 = ((e2.eval ρ2).1, replaceDrv dTbl (e2.eval ρ2).2))
    (hd : (e2.eval ρ2).2.2.2 = dLst) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.ret (I := e2eBhAdapterIface S ℓ) e1).eval ρ1)
      ((Comp.ret (I := e2eBhAdapterIface S ℓ) e2).eval ρ2) := by
  refine ⟨?_, ?_⟩
  · dsimp only [Comp.eval]; rw [h, map_pure]
  · intro σ_e2e log out hout
    simp only [Comp.eval, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨hd, rfl, rfl⟩

private theorem smArm_ret_pair {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))}
    {r1 : Expr (e2eAdapterOps ℓ decT encT) Γ1 (e2eBhAdapterCodec S ℓ).R}
    {s1 : Expr (e2eAdapterOps ℓ decT encT) Γ1 (cliAdapterTblStateTy S ℓ)}
    {r2 : Expr (e2eAdapterOps ℓ decT encT) Γ2 (e2eBhAdapterCodec S ℓ).R}
    {s2 : Expr (e2eAdapterOps ℓ decT encT) Γ2 (cliAdapterStateTy S ℓ)}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (hr : r1.eval ρ1 = r2.eval ρ2)
    (hs : s1.eval ρ1 = replaceDrv dTbl (s2.eval ρ2))
    (hd : (s2.eval ρ2).2.2 = dLst) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.ret (I := e2eBhAdapterIface S ℓ) (.pair r1 s1)).eval ρ1)
      ((Comp.ret (I := e2eBhAdapterIface S ℓ) (.pair r2 s2)).eval ρ2) := by
  apply smArm_ret
  · dsimp only [Expr.eval]; rw [hr, hs]
  · exact hd

private theorem eval_cliBobUpdateStateTblExpr_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))}
    (σ1 : Var (.opt recvResultT :: Γ1) (cliAdapterTblStateTy S ℓ))
    (idx1 : Var (.opt recvResultT :: Γ1) .nat)
    (inst1 : Var (.opt recvResultT :: Γ1) adapterInstMetaT)
    (mReg1 : Var (.opt recvResultT :: Γ1) U32)
    (σ2 : Var (.opt recvResultT :: Γ2) (cliAdapterStateTy S ℓ))
    (idx2 : Var (.opt recvResultT :: Γ2) .nat)
    (inst2 : Var (.opt recvResultT :: Γ2) adapterInstMetaT)
    (mReg2 : Var (.opt recvResultT :: Γ2) U32)
    (dTbl : (drvMirrorTblTy S ℓ).denote) (dLst : (drvMirrorTy S ℓ).denote)
    (optRr : (Ty.opt (recvResultT (ℓ := ℓ))).denote) (ρ1 : Env Γ1) (ρ2 : Env Γ2)
    (hσ : (Env.cons optRr ρ1).get σ1 = replaceDrv dTbl ((Env.cons optRr ρ2).get σ2))
    (hd : ((Env.cons optRr ρ2).get σ2).2.2 = dLst)
    (hidx : (Env.cons optRr ρ1).get idx1 = (Env.cons optRr ρ2).get idx2)
    (hinst : (Env.cons optRr ρ1).get inst1 = (Env.cons optRr ρ2).get inst2)
    (hmReg : (Env.cons optRr ρ1).get mReg1 = (Env.cons optRr ρ2).get mReg2) :
    (cliBobUpdateStateTblExpr (decT := decT) (encT := encT) σ1 idx1 inst1 mReg1).eval
        (.cons optRr ρ1) =
      replaceDrv dTbl
        ((cliBobUpdateStateExpr (decT := decT) (encT := encT) σ2 idx2 inst2 mReg2).eval
          (.cons optRr ρ2)) ∧
    (((cliBobUpdateStateExpr (decT := decT) (encT := encT) σ2 idx2 inst2 mReg2).eval
        (.cons optRr ρ2)).2.2 = dLst) := by
  cases optRr with
  | none =>
    dsimp only [cliBobUpdateStateTblExpr, cliBobUpdateStateExpr, Expr.eval, Expr.v0]
    simp only [env_get_zero]
    exact ⟨hσ, hd⟩
  | some rr =>
    cases rr with
    | inl x =>
      dsimp only [cliBobUpdateStateTblExpr, cliBobUpdateStateExpr, Expr.eval, Expr.v0]
      simp only [env_get_zero, env_get_succ]
      exact ⟨hσ, hd⟩
    | inr y =>
      dsimp only [cliBobUpdateStateTblExpr, cliBobUpdateStateExpr, Expr.eval, Expr.v0]
      simp only [env_get_zero_rfl, env_get_succ_rfl, hσ, hidx, hinst, hmReg]
      exact ⟨rfl, hd⟩

private theorem eval_cliAliceUpdateStateTblExpr_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))}
    (σ1 : Var (.opt recvResultT :: Γ1) (cliAdapterTblStateTy S ℓ))
    (idx1 : Var (.opt recvResultT :: Γ1) .nat)
    (σ2 : Var (.opt recvResultT :: Γ2) (cliAdapterStateTy S ℓ))
    (idx2 : Var (.opt recvResultT :: Γ2) .nat)
    (dTbl : (drvMirrorTblTy S ℓ).denote) (dLst : (drvMirrorTy S ℓ).denote)
    (optRr : (Ty.opt (recvResultT (ℓ := ℓ))).denote) (ρ1 : Env Γ1) (ρ2 : Env Γ2)
    (hσ : (Env.cons optRr ρ1).get σ1 = replaceDrv dTbl ((Env.cons optRr ρ2).get σ2))
    (hd : ((Env.cons optRr ρ2).get σ2).2.2 = dLst)
    (hidx : (Env.cons optRr ρ1).get idx1 = (Env.cons optRr ρ2).get idx2) :
    (cliAliceUpdateStateTblExpr (decT := decT) (encT := encT) σ1 idx1).eval (.cons optRr ρ1) =
      replaceDrv dTbl
        ((cliAliceUpdateStateExpr (decT := decT) (encT := encT) σ2 idx2).eval (.cons optRr ρ2)) ∧
    (((cliAliceUpdateStateExpr (decT := decT) (encT := encT) σ2 idx2).eval
        (.cons optRr ρ2)).2.2 = dLst) := by
  cases optRr with
  | none =>
    dsimp only [cliAliceUpdateStateTblExpr, cliAliceUpdateStateExpr, Expr.eval, Expr.v0]
    simp only [env_get_zero]
    exact ⟨hσ, hd⟩
  | some rr =>
    cases rr with
    | inl x =>
      dsimp only [cliAliceUpdateStateTblExpr, cliAliceUpdateStateExpr, Expr.eval, Expr.v0]
      simp only [env_get_zero, env_get_succ]
      exact ⟨hσ, hd⟩
    | inr y =>
      dsimp only [cliAliceUpdateStateTblExpr, cliAliceUpdateStateExpr, Expr.eval, Expr.v0]
      simp only [env_get_zero_rfl, env_get_succ_rfl, hσ, hidx]
      exact ⟨rfl, hd⟩

private theorem smArm_ret_bob {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))}
    {r1 : Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ1) (e2eBhAdapterCodec S ℓ).R}
    {r2 : Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ2) (e2eBhAdapterCodec S ℓ).R}
    {σ1 : Var (.opt recvResultT :: Γ1) (cliAdapterTblStateTy S ℓ)}
    {idx1 : Var (.opt recvResultT :: Γ1) .nat}
    {inst1 : Var (.opt recvResultT :: Γ1) adapterInstMetaT}
    {mReg1 : Var (.opt recvResultT :: Γ1) U32}
    {σ2 : Var (.opt recvResultT :: Γ2) (cliAdapterStateTy S ℓ)}
    {idx2 : Var (.opt recvResultT :: Γ2) .nat}
    {inst2 : Var (.opt recvResultT :: Γ2) adapterInstMetaT}
    {mReg2 : Var (.opt recvResultT :: Γ2) U32}
    {optRr : (Ty.opt (recvResultT (ℓ := ℓ))).denote}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (hr : r1.eval (.cons optRr ρ1) = r2.eval (.cons optRr ρ2))
    (hσ : (Env.cons optRr ρ1).get σ1 = replaceDrv dTbl ((Env.cons optRr ρ2).get σ2))
    (hd : ((Env.cons optRr ρ2).get σ2).2.2 = dLst)
    (hidx : (Env.cons optRr ρ1).get idx1 = (Env.cons optRr ρ2).get idx2)
    (hinst : (Env.cons optRr ρ1).get inst1 = (Env.cons optRr ρ2).get inst2)
    (hmReg : (Env.cons optRr ρ1).get mReg1 = (Env.cons optRr ρ2).get mReg2) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.ret (I := e2eBhAdapterIface S ℓ)
          (.pair r1 (cliBobUpdateStateTblExpr σ1 idx1 inst1 mReg1))).eval (.cons optRr ρ1))
      ((Comp.ret (I := e2eBhAdapterIface S ℓ)
          (.pair r2 (cliBobUpdateStateExpr σ2 idx2 inst2 mReg2))).eval (.cons optRr ρ2)) := by
  obtain ⟨hs, hd'⟩ := eval_cliBobUpdateStateTblExpr_eq decT encT σ1 idx1 inst1 mReg1
    σ2 idx2 inst2 mReg2 dTbl dLst optRr ρ1 ρ2 hσ hd hidx hinst hmReg
  exact smArm_ret_pair hr hs hd'

private theorem smArm_ret_alice {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))}
    {r1 : Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ1) (e2eBhAdapterCodec S ℓ).R}
    {r2 : Expr (e2eAdapterOps ℓ decT encT) (.opt recvResultT :: Γ2) (e2eBhAdapterCodec S ℓ).R}
    {σ1 : Var (.opt recvResultT :: Γ1) (cliAdapterTblStateTy S ℓ)}
    {idx1 : Var (.opt recvResultT :: Γ1) .nat}
    {σ2 : Var (.opt recvResultT :: Γ2) (cliAdapterStateTy S ℓ)}
    {idx2 : Var (.opt recvResultT :: Γ2) .nat}
    {optRr : (Ty.opt (recvResultT (ℓ := ℓ))).denote}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (hr : r1.eval (.cons optRr ρ1) = r2.eval (.cons optRr ρ2))
    (hσ : (Env.cons optRr ρ1).get σ1 = replaceDrv dTbl ((Env.cons optRr ρ2).get σ2))
    (hd : ((Env.cons optRr ρ2).get σ2).2.2 = dLst)
    (hidx : (Env.cons optRr ρ1).get idx1 = (Env.cons optRr ρ2).get idx2) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.ret (I := e2eBhAdapterIface S ℓ)
          (.pair r1 (cliAliceUpdateStateTblExpr σ1 idx1))).eval (.cons optRr ρ1))
      ((Comp.ret (I := e2eBhAdapterIface S ℓ)
          (.pair r2 (cliAliceUpdateStateExpr σ2 idx2))).eval (.cons optRr ρ2)) := by
  obtain ⟨hs, hd'⟩ := eval_cliAliceUpdateStateTblExpr_eq decT encT σ1 idx1 σ2 idx2
    dTbl dLst optRr ρ1 ρ2 hσ hd hidx
  exact smArm_ret_pair hr hs hd'

private theorem smArm_ite {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))}
    {b1 : Expr (e2eAdapterOps ℓ decT encT) Γ1 .bool}
    {b2 : Expr (e2eAdapterOps ℓ decT encT) Γ2 .bool}
    {t1 f1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) Γ1
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {t2 f2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) Γ2
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (hb : b1.eval ρ1 = b2.eval ρ2)
    (ht : SmArmCoupled P ki C K qep decT encT dTbl dLst (t1.eval ρ1) (t2.eval ρ2))
    (hf : SmArmCoupled P ki C K qep decT encT dTbl dLst (f1.eval ρ1) (f2.eval ρ2)) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.ite b1 t1 f1).eval ρ1) ((Comp.ite b2 t2 f2).eval ρ2) := by
  dsimp only [Comp.eval]
  rw [hb]
  cases b2.eval ρ2
  · exact hf
  · exact ht

private theorem smArm_caseOpt {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    {e1 : Expr (e2eAdapterOps ℓ decT encT) Γ1 (.opt t)}
    {e2 : Expr (e2eAdapterOps ℓ decT encT) Γ2 (.opt t)}
    {n1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) Γ1
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {n2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) Γ2
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {s1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (t :: Γ1)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {s2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (t :: Γ2)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (he : e1.eval ρ1 = e2.eval ρ2)
    (hn : SmArmCoupled P ki C K qep decT encT dTbl dLst (n1.eval ρ1) (n2.eval ρ2))
    (hs : ∀ v, SmArmCoupled P ki C K qep decT encT dTbl dLst
      (s1.eval (.cons v ρ1)) (s2.eval (.cons v ρ2))) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.caseOpt e1 n1 s1).eval ρ1) ((Comp.caseOpt e2 n2 s2).eval ρ2) := by
  dsimp only [Comp.eval]
  rw [he]
  cases e2.eval ρ2 with
  | none => exact hn
  | some v => exact hs v

private theorem smArm_caseSum {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))} {a b : Ty (e2eSig ℓ)}
    {e1 : Expr (e2eAdapterOps ℓ decT encT) Γ1 (.sum a b)}
    {e2 : Expr (e2eAdapterOps ℓ decT encT) Γ2 (.sum a b)}
    {l1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (a :: Γ1)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {l2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (a :: Γ2)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {r1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (b :: Γ1)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {r2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (b :: Γ2)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (he : e1.eval ρ1 = e2.eval ρ2)
    (hl : ∀ u, SmArmCoupled P ki C K qep decT encT dTbl dLst
      (l1.eval (.cons u ρ1)) (l2.eval (.cons u ρ2)))
    (hr : ∀ v, SmArmCoupled P ki C K qep decT encT dTbl dLst
      (r1.eval (.cons v ρ1)) (r2.eval (.cons v ρ2))) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.caseSum e1 l1 r1).eval ρ1) ((Comp.caseSum e2 l2 r2).eval ρ2) := by
  dsimp only [Comp.eval]
  rw [he]
  cases e2.eval ρ2 with
  | inl u => exact hl u
  | inr v => exact hr v

private theorem smArm_caseSum_inr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))} {a b : Ty (e2eSig ℓ)}
    {e1 : Expr (e2eAdapterOps ℓ decT encT) Γ1 (.sum a b)}
    {e2 : Expr (e2eAdapterOps ℓ decT encT) Γ2 (.sum a b)}
    {l1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (a :: Γ1)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {l2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (a :: Γ2)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {r1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (b :: Γ1)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {r2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (b :: Γ2)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2} {v : b.denote}
    (he1 : e1.eval ρ1 = .inr v)
    (he2 : e2.eval ρ2 = .inr v)
    (hr : SmArmCoupled P ki C K qep decT encT dTbl dLst
      (r1.eval (.cons v ρ1)) (r2.eval (.cons v ρ2))) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.caseSum e1 l1 r1).eval ρ1) ((Comp.caseSum e2 l2 r2).eval ρ2) := by
  dsimp only [Comp.eval]
  rw [he1, he2]
  exact hr

private theorem smArm_bind_ret {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    {e1 : Expr (e2eAdapterOps ℓ decT encT) Γ1 t}
    {e2 : Expr (e2eAdapterOps ℓ decT encT) Γ2 t}
    {k1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (t :: Γ1)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {k2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ) (t :: Γ2)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (he : e1.eval ρ1 = e2.eval ρ2)
    (hk : ∀ v, SmArmCoupled P ki C K qep decT encT dTbl dLst
      (k1.eval (.cons v ρ1)) (k2.eval (.cons v ρ2))) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.bind (.ret e1) k1).eval ρ1) ((Comp.bind (.ret e2) k2).eval ρ2) := by
  dsimp only [Comp.eval]
  rw [he, pure_bind, pure_bind]
  exact hk (e2.eval ρ2)

private theorem smArm_query {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives}
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    {C : Crypto} {K : MlKem} {qep : ℕ}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {dTbl : (drvMirrorTblTy S ℓ).denote} {dLst : (drvMirrorTy S ℓ).denote}
    {Γ1 Γ2 : List (Ty (e2eSig ℓ))}
    (g : E2EAdapterTag) (hg : g ≠ .ki ∧ g ≠ .ctl)
    {e1 : Expr (e2eAdapterOps ℓ decT encT) Γ1 ((e2eBhAdapterIface S ℓ).dom g)}
    {e2 : Expr (e2eAdapterOps ℓ decT encT) Γ2 ((e2eBhAdapterIface S ℓ).dom g)}
    {k1 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      ((e2eBhAdapterIface S ℓ).cod g :: Γ1)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ))}
    {k2 : Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      ((e2eBhAdapterIface S ℓ).cod g :: Γ2)
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterStateTy S ℓ))}
    {ρ1 : Env Γ1} {ρ2 : Env Γ2}
    (he : e1.eval ρ1 = e2.eval ρ2)
    (hk : ∀ v, SmArmCoupled P ki C K qep decT encT dTbl dLst
      (k1.eval (.cons v ρ1)) (k2.eval (.cons v ρ2))) :
    SmArmCoupled P ki C K qep decT encT dTbl dLst
      ((Comp.bind (Comp.query (I := e2eBhAdapterIface S ℓ) g e1) k1).eval ρ1)
      ((Comp.bind (Comp.query (I := e2eBhAdapterIface S ℓ) g e2) k2).eval ρ2) := by
  refine ⟨?_, ?_⟩
  · dsimp only [Comp.eval]
    rw [he, map_bind]
    congr 1; funext v; exact (hk v).1
  · intro σ_e2e log out hout
    dsimp only [Comp.eval] at hout
    cases g with
    | ki => exact False.elim (hg.1 rfl)
    | ctl => exact False.elim (hg.2 rfl)
    | tr =>
      generalize e2.eval ρ2 = x at hout
      rcases x with ⟨i, p, m, r⟩
      rw [bind_map_left] at hout
      exact support_run_drv_sm_bind P ki C K qep decT encT i _ _ dLst
        (fun r' => (hk _).2) σ_e2e log out hout
    | ch =>
      generalize e2.eval ρ2 = x at hout
      rcases x with ⟨i, p, m0, m1, r⟩
      rw [bind_map_left] at hout
      exact support_run_drv_sm_bind P ki C K qep decT encT i _ _ dLst
        (fun r' => (hk _).2) σ_e2e log out hout
    | dl =>
      generalize e2.eval ρ2 = x at hout
      rcases x with ⟨i, p, c⟩
      rw [bind_map_left] at hout
      exact support_run_drv_sm_bind P ki C K qep decT encT i _ _ dLst
        (fun r' => (hk _).2) σ_e2e log out hout
    | ij =>
      generalize e2.eval ρ2 = x at hout
      rcases x with ⟨i, p, c⟩
      rw [bind_map_left] at hout
      exact support_run_drv_sm_bind P ki C K qep decT encT i _ _ dLst
        (fun r' => (hk _).2) σ_e2e log out hout
    | cr =>
      generalize e2.eval ρ2 = x at hout
      rcases x with ⟨i, p⟩
      rw [bind_map_left] at hout
      exact support_run_drv_sm_bind P ki C K qep decT encT i _ _ dLst
        (fun r' => (hk _).2) σ_e2e log out hout

private theorem smArm_tr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (dTbl : (drvMirrorTblTy S ℓ).denote) (s_lst : (cliAdapterStateTy S ℓ).denote)
    (trArgs : (Ty.prod .bool (.prod (PlainT (ℓ := ℓ)) (.opt BV512))).denote)
    (iSmQ : (Ty.prod .nat (smQT (ℓ := ℓ))).denote)
    (qv : (e2eBhAdapterCodec S ℓ).Q.denote) :
    SmArmCoupled P ki C K qep decT encT dTbl s_lst.2.2
      ((cliAdapterTrArmTbl S ℓ decT encT).eval
        (.cons trArgs (.cons iSmQ (.cons (replaceDrv dTbl s_lst) (.cons qv .nil)))))
      ((cliAdapterTrArm S ℓ decT encT).eval
        (.cons trArgs (.cons iSmQ (.cons s_lst (.cons qv .nil))))) := by
  dsimp only [cliAdapterTrArmTbl, cliAdapterTrArm, cliQuery]
  refine smArm_caseOpt rfl (smArm_ret_pair rfl rfl rfl) fun inst => ?_
  refine smArm_query .tr ⟨by decide, by decide⟩ rfl fun optCt => ?_
  exact smArm_caseOpt rfl (smArm_ret_pair rfl rfl rfl) fun ct => smArm_ret_pair rfl rfl rfl

private theorem smArm_ch {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (dTbl : (drvMirrorTblTy S ℓ).denote) (s_lst : (cliAdapterStateTy S ℓ).denote)
    (chArgs : (Ty.prod .bool (.prod (PlainT (ℓ := ℓ)) (.prod PlainT (.opt BV512)))).denote)
    (s1 : (Ty.sum (.prod .bool (.prod (PlainT (ℓ := ℓ)) (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))).denote)
    (iSmQ : (Ty.prod .nat (smQT (ℓ := ℓ))).denote)
    (qv : (e2eBhAdapterCodec S ℓ).Q.denote) :
    SmArmCoupled P ki C K qep decT encT dTbl s_lst.2.2
      ((cliAdapterChArmTbl S ℓ decT encT).eval
        (.cons chArgs (.cons s1 (.cons iSmQ (.cons (replaceDrv dTbl s_lst) (.cons qv .nil))))))
      ((cliAdapterChArm S ℓ decT encT).eval
        (.cons chArgs (.cons s1 (.cons iSmQ (.cons s_lst (.cons qv .nil)))))) := by
  dsimp only [cliAdapterChArmTbl, cliAdapterChArm, cliQuery]
  refine smArm_caseOpt rfl (smArm_ret_pair rfl rfl rfl) fun inst => ?_
  refine smArm_query .ch ⟨by decide, by decide⟩ rfl fun optCt => ?_
  exact smArm_caseOpt rfl (smArm_ret_pair rfl rfl rfl) fun ct => smArm_ret_pair rfl rfl rfl

private theorem smArm_dl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (dTbl : (drvMirrorTblTy S ℓ).denote) (s_lst : (cliAdapterStateTy S ℓ).denote)
    (dlArgs : (Ty.prod .bool (B (ℓ := ℓ) 32)).denote)
    (s2 : (Ty.sum (.prod .bool (B (ℓ := ℓ) 32)) (.sum (.prod .bool (B 32)) .bool)).denote)
    (s1 : (Ty.sum (.prod .bool (.prod (PlainT (ℓ := ℓ)) (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))).denote)
    (iSmQ : (Ty.prod .nat (smQT (ℓ := ℓ))).denote)
    (qv : (e2eBhAdapterCodec S ℓ).Q.denote) :
    SmArmCoupled P ki C K qep decT encT dTbl s_lst.2.2
      ((cliAdapterDlArmTbl S ℓ decT encT).eval
        (.cons dlArgs (.cons s2 (.cons s1 (.cons iSmQ
          (.cons (replaceDrv dTbl s_lst) (.cons qv .nil)))))))
      ((cliAdapterDlArm S ℓ decT encT).eval
        (.cons dlArgs (.cons s2 (.cons s1 (.cons iSmQ (.cons s_lst (.cons qv .nil))))))) := by
  dsimp only [cliAdapterDlArmTbl, cliAdapterDlArm, cliQuery]
  refine smArm_ite rfl ?_ ?_
  · refine smArm_caseOpt rfl (smArm_ret_pair rfl rfl rfl) fun inst => ?_
    refine smArm_caseOpt rfl ?_ fun pk => ?_
    · refine smArm_caseOpt rfl ?_ fun body => ?_
      · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
      · refine smArm_caseOpt rfl ?_ fun pkInner => ?_
        · refine smArm_ite rfl ?_ ?_
          · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
          · exact smArm_query .dl ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
        · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
    · refine smArm_ite rfl ?_ ?_
      · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
      · refine smArm_bind_ret rfl fun instIdx => ?_
        refine smArm_bind_ret rfl fun mRegId => ?_
        refine smArm_query .dl ⟨by decide, by decide⟩ rfl fun optRr => ?_
        exact smArm_ret_bob rfl rfl rfl rfl rfl rfl
  · refine smArm_caseOpt rfl ?_ fun body => ?_
    · refine smArm_ite rfl ?_ ?_
      · exact smArm_query .dl ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
      · exact smArm_ret_pair rfl rfl rfl
    · refine smArm_ite rfl (smArm_ret_pair rfl rfl rfl) ?_
      refine smArm_bind_ret rfl fun instIdx => ?_
      refine smArm_query .dl ⟨by decide, by decide⟩ rfl fun optRr => ?_
      exact smArm_ret_alice rfl rfl rfl rfl

private theorem smArm_ij {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (dTbl : (drvMirrorTblTy S ℓ).denote) (s_lst : (cliAdapterStateTy S ℓ).denote)
    (ijArgs : (Ty.prod .bool (B (ℓ := ℓ) 32)).denote)
    (s3 : (Ty.sum (.prod .bool (B (ℓ := ℓ) 32)) .bool).denote)
    (s2 : (Ty.sum (.prod .bool (B (ℓ := ℓ) 32)) (.sum (.prod .bool (B 32)) .bool)).denote)
    (s1 : (Ty.sum (.prod .bool (.prod (PlainT (ℓ := ℓ)) (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))).denote)
    (iSmQ : (Ty.prod .nat (smQT (ℓ := ℓ))).denote)
    (qv : (e2eBhAdapterCodec S ℓ).Q.denote) :
    SmArmCoupled P ki C K qep decT encT dTbl s_lst.2.2
      ((cliAdapterIjArmTbl S ℓ decT encT).eval
        (.cons ijArgs (.cons s3 (.cons s2 (.cons s1 (.cons iSmQ
          (.cons (replaceDrv dTbl s_lst) (.cons qv .nil))))))))
      ((cliAdapterIjArm S ℓ decT encT).eval
        (.cons ijArgs (.cons s3 (.cons s2 (.cons s1 (.cons iSmQ
          (.cons s_lst (.cons qv .nil)))))))) := by
  dsimp only [cliAdapterIjArmTbl, cliAdapterIjArm, cliQuery]
  refine smArm_ite rfl ?_ ?_
  · refine smArm_caseOpt rfl ?_ fun body => ?_
    · refine smArm_caseOpt rfl ?_ fun pk => ?_
      · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
      · refine smArm_ite rfl ?_ ?_
        · refine smArm_caseOpt rfl ?_ fun inst => ?_
          · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
          · refine smArm_ite rfl ?_ ?_
            · refine smArm_ite rfl ?_ ?_
              · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
              · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
            · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
        · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
    · refine smArm_ite rfl ?_ ?_
      · refine smArm_caseOpt rfl ?_ fun pkB => ?_
        · refine smArm_ite rfl ?_ ?_
          · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
          · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
        · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
      · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
  · refine smArm_caseOpt rfl (smArm_ret_pair rfl rfl rfl) fun body => ?_
    refine smArm_ite rfl ?_ (smArm_ret_pair rfl rfl rfl)
    refine smArm_caseOpt rfl ?_ fun pkB => ?_
    · refine smArm_ite rfl ?_ ?_
      · exact smArm_query .ij ⟨by decide, by decide⟩ rfl fun _ => smArm_ret_pair rfl rfl rfl
      · refine smArm_bind_ret rfl fun instIdx => ?_
        refine smArm_query .ij ⟨by decide, by decide⟩ rfl fun optRr => ?_
        exact smArm_ret_alice rfl rfl rfl rfl
    · refine smArm_bind_ret rfl fun instIdx => ?_
      refine smArm_query .ij ⟨by decide, by decide⟩ rfl fun optRr => ?_
      exact smArm_ret_alice rfl rfl rfl rfl

private theorem smArm_cr {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (dTbl : (drvMirrorTblTy S ℓ).denote) (s_lst : (cliAdapterStateTy S ℓ).denote)
    (crArgs : Bool)
    (s3 : (Ty.sum (.prod .bool (B (ℓ := ℓ) 32)) .bool).denote)
    (s2 : (Ty.sum (.prod .bool (B (ℓ := ℓ) 32)) (.sum (.prod .bool (B 32)) .bool)).denote)
    (s1 : (Ty.sum (.prod .bool (.prod (PlainT (ℓ := ℓ)) (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))).denote)
    (iSmQ : (Ty.prod .nat (smQT (ℓ := ℓ))).denote)
    (qv : (e2eBhAdapterCodec S ℓ).Q.denote) :
    SmArmCoupled P ki C K qep decT encT dTbl s_lst.2.2
      ((adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
          (drvMirrorTblTy S ℓ)).eval
        (.cons crArgs (.cons s3 (.cons s2 (.cons s1 (.cons iSmQ
          (.cons (replaceDrv dTbl s_lst) (.cons qv .nil))))))))
      ((adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
          (drvMirrorTy S ℓ)).eval
        (.cons crArgs (.cons s3 (.cons s2 (.cons s1 (.cons iSmQ
          (.cons s_lst (.cons qv .nil)))))))) := by
  dsimp only [adapterCrArm]
  refine smArm_caseOpt rfl (smArm_ret_pair rfl rfl rfl) fun inst => ?_
  refine smArm_query .cr ⟨by decide, by decide⟩ rfl fun optG => ?_
  exact smArm_caseOpt rfl (smArm_ret_pair rfl rfl rfl) fun g => smArm_ret_pair rfl rfl rfl

private theorem step_eq_unif_tbl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_lst : (cliAdapterStateTy S ℓ).denote} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : TblListCouplingInv s_lst σ_e2e) (n : ℕ) :
    TblStepCoupledEq
      (((cliHonestTblStepImplWith P ki C K qep decT encT (.inl n)).run
        (replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_e2e.toModelDriverBase) s_lst)).run (σ_e2e, log))
      (((cliHonestStepImplWith P ki C K qep decT encT (.inl n)).run s_lst).run (σ_e2e, log)) := by
  change TblStepCoupledEq
    ((do
      let x ← simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inl n))
      pure (x, replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_e2e.toModelDriverBase) s_lst)).run
      (σ_e2e, log))
    ((do
      let x ← simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inl n))
      pure (x, s_lst)).run (σ_e2e, log))
  simp only [StateT.run_bind, StateT.run_pure]
  have hq :
      (simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
        (query (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (.inl n))).run
        (σ_e2e, log) =
      ((query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>= fun r =>
        pure (r, (σ_e2e, log))) := by
    simp [cliE2EDrvImplWithLogState, StateT.run_monadLift, monadLift_self]
  rw [hq]
  refine ⟨?_, ?_⟩
  · simp only [bind_assoc, pure_bind, map_bind, map_pure]
  · simp only [bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    rintro _ ⟨a, -, rfl⟩
    exact hInv

private theorem step_eq_ki_tbl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives) (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_lst : (cliAdapterStateTy S ℓ).denote} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : TblListCouplingInv s_lst σ_e2e)
    (kq : SignalPqxdh.KeyIndQuery S) :
    TblStepCoupledEq
      (((cliHonestTblStepImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT
          (.inr (.inl (.inl kq)))).run
        (replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_e2e.toModelDriverBase) s_lst)).run (σ_e2e, log))
      (((cliHonestStepImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT
          (.inr (.inl (.inl kq)))).run s_lst).run (σ_e2e, log)) := by
  let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
  let s_tbl := replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_e2e.toModelDriverBase) s_lst
  change TblStepCoupledEq
    ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (((cliAdapterKiOrCtlArmTbl S ℓ decT encT).eval
        (.cons (.inl (keyIndQenc kq))
          (.cons s_tbl (.cons (.inl (.inl (keyIndQenc kq))) .nil)))) >>= fun p =>
        pure ((e2eBhAdapterCodec S ℓ).rdec (.inl (.inl kq)) p.1, p.2))).run (σ_e2e, log))
    ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (((cliAdapterKiOrCtlArm S ℓ decT encT).eval
        (.cons (.inl (keyIndQenc kq))
          (.cons s_lst (.cons (.inl (.inl (keyIndQenc kq))) .nil)))) >>= fun p =>
        pure ((e2eBhAdapterCodec S ℓ).rdec (.inl (.inl kq)) p.1, p.2))).run (σ_e2e, log))
  dsimp only [cliAdapterKiOrCtlArmTbl, cliAdapterKiOrCtlArm, cliQuery, Comp.eval, Expr.eval,
    env_get_zero_rfl, env_get_succ_rfl, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec]
  rw [keyIndQdec_keyIndQenc]
  simp only [bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_simulateQ_drv_ki]
  have hMirLst : ∀ kr : SignalPqxdh.KeyIndResponse,
      (stepBaseMirrorExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
        (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
          cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
        (.snd (.snd (.var (.succ (.succ (.succ .zero))))))
        (.var (.succ .zero)) (.var .zero)).eval
        (.cons (keyIndRenc kr) (.cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
          (.cons s_lst (.cons (.inl (.inl (keyIndQenc kq))) .nil))))) =
      drvMirrorToV (ℓ := ℓ) (bhBaseMirror σ_e2e.toModelDriverBase kq kr) := by
    intro kr
    rw [eval_stepBaseMirrorExpr _ _ _ σ_e2e.toModelDriverBase _
      (by dsimp only [Expr.eval, env_get_zero_rfl, env_get_succ_rfl]; exact hInv.drv_eq)]
    dsimp only [Expr.eval, env_get_zero_rfl, env_get_succ_rfl]
    rw [keyIndQdec_keyIndQenc, keyIndRdec_keyIndRenc]
  have hMirTbl : ∀ kr : SignalPqxdh.KeyIndResponse,
      (∀ u j b, kq = .genSPK u j → kr = .bundleResp b →
        b.spkB.length = 32 ∧ b.pqspkB.length = 1568) →
      (stepBaseMirrorTblExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
        (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
          cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
        (.snd (.snd (.var (.succ (.succ (.succ .zero))))))
        (.var (.succ .zero)) (.var .zero)).eval
        (.cons (keyIndRenc kr) (.cons (keyIndQenc kq) (.cons (.inl (keyIndQenc kq))
          (.cons s_tbl (.cons (.inl (.inl (keyIndQenc kq))) .nil))))) =
      drvMirrorTblToV (ℓ := ℓ) (bhBaseMirror σ_e2e.toModelDriverBase kq kr) := by
    intro kr hLen
    rw [eval_stepBaseMirrorTblExpr _ _ _ σ_e2e.toModelDriverBase _ rfl]
    · dsimp only [Expr.eval, env_get_zero_rfl, env_get_succ_rfl]
      rw [keyIndQdec_keyIndQenc, keyIndRdec_keyIndRenc]
    · intro u j b hq hr
      dsimp only [Expr.eval, env_get_zero_rfl, env_get_succ_rfl] at hq hr
      rw [keyIndQdec_keyIndQenc] at hq
      rw [keyIndRdec_keyIndRenc] at hr
      exact hLen u j b hq hr
  cases hok : !CryptoVerification.E2E.bhDrvKiQueryOk P σ_e2e.toModelDriverBase kq
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hprom : (match kq with
      | .corruptIK u => CryptoVerification.E2E.bhNoOpkRespPromoted σ_e2e.instMeta u
      | _ => false)
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      refine ⟨?_, ?_⟩
      · simp only [map_bind, map_pure]
        apply probComp_bind_congr_support
        rintro ⟨kr, st'⟩ hStep
        dsimp only
        rw [hMirTbl kr (fun u j b hq hr => by
          subst hq; subst hr
          exact pqxdhKeyIndImpl1KeyReal_genSPK_bundleResp_lengths P hP u j σ_e2e.st st' b hStep),
          hMirLst kr]
        rfl
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        rintro _ ⟨⟨kr, st'⟩, hStep, rfl⟩
        refine ⟨mirrorKiInv_bhBaseMirror (kiFreshKeys_pqxdhKeyIndImpl1KeyReal S P)
            hInv.mirror_ki kq kr hStep,
          bundlesValidLen_bhBaseMirror P hP hInv.bundles_sz kq kr hStep, ?_⟩
        dsimp only [CryptoVerification.E2E.bhE2EMirror]
        exact hMirLst kr
    · simp only [↓reduceIte, pure_bind]
      rw [hMirTbl .noneResp (fun _ _ _ _ hr => nomatch hr), hMirLst .noneResp,
        bhBaseMirror_noneResp]
      refine ⟨?_, ?_⟩
      · simp only [map_pure]; rfl
      · simp only [support_pure, Set.mem_singleton_iff]
        rintro out rfl
        exact ⟨hInv.mirror_ki, hInv.bundles_sz, rfl⟩
  · simp only [↓reduceIte, pure_bind]
    rw [hMirTbl .noneResp (fun _ _ _ _ hr => nomatch hr), hMirLst .noneResp,
      bhBaseMirror_noneResp]
    refine ⟨?_, ?_⟩
    · simp only [map_pure]; rfl
    · simp only [support_pure, Set.mem_singleton_iff]
      rintro out rfl
      exact ⟨hInv.mirror_ki, hInv.bundles_sz, rfl⟩

set_option linter.unusedSimpArgs false in
private theorem step_eq_ctl_tbl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    {ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp)}
    (hKi : KiFreshKeys S ki)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_lst : (cliAdapterStateTy S ℓ).denote} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : TblListCouplingInv s_lst σ_e2e)
    (sid : SignalPqxdh.SessionId S) :
    TblStepCoupledEq
      (((cliHonestTblStepImplWith P ki C K qep decT encT (.inr (.inl (.inr (.startDR sid))))).run
        (replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_e2e.toModelDriverBase) s_lst)).run (σ_e2e, log))
      (((cliHonestStepImplWith P ki C K qep decT encT (.inr (.inl (.inr (.startDR sid))))).run
        s_lst).run (σ_e2e, log)) := by
  let s_tbl := replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_e2e.toModelDriverBase) s_lst
  change TblStepCoupledEq
    ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (((cliAdapterKiOrCtlArmTbl S ℓ decT encT).eval
        (.cons (.inr (sidV sid))
          (.cons s_tbl (.cons (.inl (.inr (sidV sid))) .nil)))) >>= fun p =>
        pure ((e2eBhAdapterCodec S ℓ).rdec (.inl (.inr (.startDR sid))) p.1, p.2))).run
      (σ_e2e, log))
    ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (((cliAdapterKiOrCtlArm S ℓ decT encT).eval
        (.cons (.inr (sidV sid))
          (.cons s_lst (.cons (.inl (.inr (sidV sid))) .nil)))) >>= fun p =>
        pure ((e2eBhAdapterCodec S ℓ).rdec (.inl (.inr (.startDR sid))) p.1, p.2))).run
      (σ_e2e, log))
  dsimp only [cliAdapterKiOrCtlArmTbl, cliAdapterKiOrCtlArm, cliQuery, Comp.eval, Expr.eval,
    env_get_zero_rfl, env_get_succ_rfl, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec]
  rw [sidOfV_sidV]
  simp only [bind_assoc, bind_map_left, simulateQ_bind, StateT.run_bind]
  rw [run_simulateQ_drv_ctl]
  simp only [bind_assoc, pure_bind]
  have hGrdTbl : ∀ idx : ℕ,
      (guardPromoteTblExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
        (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
          cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
        (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
        (.var (.succ (.succ .zero)))).eval
        (.cons idx (.cons (some idx) (.cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons s_tbl (.cons (.inl (.inr (sidV sid))) .nil)))))) =
      ((bhShallowStepMirrorGuard (.inr (σ_e2e.toModelDriverBase, sid))).2).map
        (instMetaToV (ℓ := ℓ)) := by
    intro idx
    rw [eval_guardPromoteTblExpr _ _ σ_e2e.toModelDriverBase _ rfl
      hInv.mirror_ki.sends_init hInv.bundles_sz
      hInv.mirror_ki.prins_nodup hInv.mirror_ki.opks_nodup]
    dsimp only [Expr.eval, env_get_zero_rfl, env_get_succ_rfl]
    rw [sidOfV_sidV]
  have hGrdLst : ∀ idx : ℕ,
      (guardPromoteExpr (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
        (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
          cliAdapterStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
        (.snd (.snd (.var (.succ (.succ (.succ (.succ .zero)))))))
        (.var (.succ (.succ .zero)))).eval
        (.cons idx (.cons (some idx) (.cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons s_lst (.cons (.inl (.inr (sidV sid))) .nil)))))) =
      ((bhShallowStepMirrorGuard (.inr (σ_e2e.toModelDriverBase, sid))).2).map
        (instMetaToV (ℓ := ℓ)) := by
    intro idx
    rw [eval_guardPromoteExpr _ _ σ_e2e.toModelDriverBase _
      (by dsimp only [Expr.eval, env_get_zero_rfl, env_get_succ_rfl]; exact hInv.drv_eq)
      hInv.mirror_ki.prins_length_le hInv.mirror_ki.bundles_length_le
      hInv.mirror_ki.opks_length_le hInv.mirror_ki.sends_length_le]
    dsimp only [Expr.eval, env_get_zero_rfl, env_get_succ_rfl]
    rw [sidOfV_sidV]
  refine ⟨?_, ?_⟩
  · simp only [map_bind]
    apply probComp_bind_congr_support
    rintro ⟨optIdx, σ'⟩ hout
    obtain ⟨hBaseEq, _⟩ :=
      compositionLocalStart_base_mirror hKi C K (some σ_e2e.b) rfl hInv.mirror_ki sid hout
    cases optIdx with
    | none =>
      dsimp only [Comp.eval, Expr.eval, env_get_zero_rfl, env_get_succ_rfl, Expr.v3]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      dsimp only [s_tbl, replaceDrv]
      rw [hBaseEq]
    | some idx =>
      dsimp only [Comp.eval, Expr.eval, env_get_zero_rfl, env_get_succ_rfl, Expr.v0, Expr.v1,
        Expr.v4, Expr.v5]
      rw [hGrdTbl idx, hGrdLst idx]
      cases hG : (bhShallowStepMirrorGuard (.inr (σ_e2e.toModelDriverBase, sid))).2 with
      | none =>
        dsimp only [Option.map]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        dsimp only [s_tbl, replaceDrv]
        rw [hBaseEq]
      | some inst =>
        dsimp only [Option.map, Comp.eval, Expr.eval, env_get_zero_rfl, env_get_succ_rfl,
          Expr.v0, Expr.v1, Expr.v5]
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
        dsimp only [s_tbl, replaceDrv]
        rw [hBaseEq]
        rfl
  · simp only [mem_support_bind_iff]
    rintro out ⟨⟨optIdx, σ'⟩, hout, hout2⟩
    obtain ⟨hBaseEq, hMir'⟩ :=
      compositionLocalStart_base_mirror hKi C K (some σ_e2e.b) rfl hInv.mirror_ki sid hout
    have hInv' : TblListCouplingInv s_lst σ' := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← hBaseEq]; exact hMir'
      · rw [← hBaseEq]; exact hInv.bundles_sz
      · rw [← hBaseEq]; exact hInv.drv_eq
    cases optIdx with
    | none =>
      dsimp only [Comp.eval, Expr.eval, env_get_zero_rfl, env_get_succ_rfl, Expr.v3] at hout2
      simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, mem_support_bind_iff] at hout2
      rcases hout2 with ⟨_, rfl, rfl⟩
      exact hInv'
    | some idx =>
      dsimp only [Comp.eval, Expr.eval, env_get_zero_rfl, env_get_succ_rfl, Expr.v0, Expr.v1,
        Expr.v4, Expr.v5] at hout2
      rw [hGrdLst idx] at hout2
      cases hG : (bhShallowStepMirrorGuard (.inr (σ_e2e.toModelDriverBase, sid))).2 with
      | none =>
        rw [hG] at hout2
        dsimp only [Option.map] at hout2
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, mem_support_bind_iff] at hout2
        rcases hout2 with ⟨_, rfl, rfl⟩
        exact hInv'
      | some inst =>
        rw [hG] at hout2
        dsimp only [Option.map, Comp.eval, Expr.eval, env_get_zero_rfl, env_get_succ_rfl,
          Expr.v0, Expr.v1, Expr.v5] at hout2
        simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, mem_support_bind_iff] at hout2
        rcases hout2 with ⟨_, rfl, rfl⟩
        exact ⟨hInv'.mirror_ki, hInv'.bundles_sz, hInv'.drv_eq⟩

private theorem step_eq_sm_tbl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_lst : (cliAdapterStateTy S ℓ).denote} {σ_e2e : BHE2EDrvState S ℓ} {log : List (BitVec 512)}
    (hInv : TblListCouplingInv s_lst σ_e2e)
    (i : ℕ) (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    TblStepCoupledEq
      (((cliHonestTblStepImplWith P ki C K qep decT encT (.inr (.inr ⟨i, sq⟩))).run
        (replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_e2e.toModelDriverBase) s_lst)).run (σ_e2e, log))
      (((cliHonestStepImplWith P ki C K qep decT encT (.inr (.inr ⟨i, sq⟩))).run s_lst).run
        (σ_e2e, log)) := by
  let dTbl := drvMirrorTblToV (ℓ := ℓ) σ_e2e.toModelDriverBase
  let iSmQ : (Ty.prod .nat (smQT (ℓ := ℓ))).denote := (i, smQenc (ℓ := ℓ) sq)
  let qv : (e2eBhAdapterCodec S ℓ).Q.denote := (e2eBhAdapterCodec S ℓ).qenc (.inr ⟨i, sq⟩)
  have h_qenc : qv = .inr iSmQ := by
    rcases sq with ((((tr | ch) | dl) | ij) | cr) <;> rfl
  let cTbl := (cliAdapterHandleTbl decT encT S ℓ).eval
    (.cons (replaceDrv dTbl s_lst) (.cons qv .nil))
  let cLst := (cliAdapterHandle decT encT S ℓ).eval (.cons s_lst (.cons qv .nil))
  have hArm : SmArmCoupled P ki C K qep decT encT dTbl s_lst.2.2 cTbl cLst := by
    dsimp only [cTbl, cLst, cliAdapterHandleTbl, cliAdapterHandle]
    refine smArm_caseSum_inr h_qenc h_qenc ?_
    refine smArm_caseSum rfl (fun trArgs => smArm_tr P ki C K qep decT encT dTbl s_lst trArgs iSmQ qv)
      fun s1 => ?_
    refine smArm_caseSum rfl
      (fun chArgs => smArm_ch P ki C K qep decT encT dTbl s_lst chArgs s1 iSmQ qv) fun s2 => ?_
    refine smArm_caseSum rfl
      (fun dlArgs => smArm_dl P ki C K qep decT encT dTbl s_lst dlArgs s2 s1 iSmQ qv) fun s3 => ?_
    exact smArm_caseSum rfl
      (fun ijArgs => smArm_ij P ki C K qep decT encT dTbl s_lst ijArgs s3 s2 s1 iSmQ qv)
      (fun crArgs => smArm_cr P ki C K qep decT encT dTbl s_lst crArgs s3 s2 s1 iSmQ qv)
  change TblStepCoupledEq
    ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (cTbl >>= fun p => pure ((e2eBhAdapterCodec S ℓ).rdec (.inr ⟨i, sq⟩) p.1, p.2))).run
      (σ_e2e, log))
    ((simulateQ (cliE2EDrvImplWithLogState P ki C K qep decT encT)
      (cLst >>= fun p => pure ((e2eBhAdapterCodec S ℓ).rdec (.inr ⟨i, sq⟩) p.1, p.2))).run
      (σ_e2e, log))
  refine ⟨?_, ?_⟩
  · have hBindMap :
        (cTbl >>= fun p => pure ((e2eBhAdapterCodec S ℓ).rdec (.inr ⟨i, sq⟩) p.1, p.2)) =
        (fun q => (q.1, replaceDrv dTbl q.2)) <$>
          (cLst >>= fun p => pure ((e2eBhAdapterCodec S ℓ).rdec (.inr ⟨i, sq⟩) p.1, p.2)) := by
      rw [hArm.1, bind_map_left, map_bind]
      simp only [map_pure]
    rw [hBindMap, run_simulateQ_map]
    apply probComp_map_congr_support
    intro out hout
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨p, σ_log'⟩, hMem, rfl⟩
    obtain ⟨_, hBaseEq, _⟩ := hArm.2 σ_e2e log (p, σ_log') hMem
    dsimp only [dTbl]
    rw [hBaseEq]
  · intro out hout
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    rcases hout with ⟨⟨p, σ_log'⟩, hMem, rfl⟩
    obtain ⟨hdEq, hBaseEq, hStEq⟩ := hArm.2 σ_e2e log (p, σ_log') hMem
    refine ⟨?_, ?_, ?_⟩
    · rw [hBaseEq, hStEq]; exact hInv.mirror_ki
    · rw [hBaseEq]; exact hInv.bundles_sz
    · rw [hdEq, hBaseEq]; exact hInv.drv_eq

private theorem cliHonestTblStepImplWith_coupled {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives) (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {s_lst : (cliAdapterStateTy S ℓ).denote} {σ_log : DrvLogState S ℓ}
    (hInv : TblListCouplingInv s_lst σ_log.1)
    (q : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain) :
    TblStepCoupledEq
      (((cliHonestTblStepImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT q).run
        (replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_log.1.toModelDriverBase) s_lst)).run σ_log)
      (((cliHonestStepImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT q).run
        s_lst).run σ_log) := by
  rcases σ_log with ⟨σ_e2e, log⟩
  rcases q with n | ((kq | cq) | ⟨i, sq⟩)
  · exact step_eq_unif_tbl P _ C K qep decT encT hInv n
  · exact step_eq_ki_tbl P hP C K qep decT encT hInv kq
  · cases cq with
    | startDR sid =>
      exact step_eq_ctl_tbl P (kiFreshKeys_pqxdhKeyIndImpl1KeyReal S P) C K qep decT encT hInv sid
  · exact step_eq_sm_tbl P _ C K qep decT encT hInv i sq

private theorem simulateQ_cliHonestTblStepImplWith_eq_map
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α : Type}
    (P : SignalPqxdh.Primitives) (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (oa : OracleComp (unifSpec + bhGameSpec S ℓ (BitVec 512)) α)
    {s_lst : (cliAdapterStateTy S ℓ).denote} {σ_log : DrvLogState S ℓ}
    (hInv : TblListCouplingInv s_lst σ_log.1) :
    (((simulateQ (cliHonestTblStepImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep
        decT encT) oa).run
      (replaceDrv (drvMirrorTblToV (ℓ := ℓ) σ_log.1.toModelDriverBase) s_lst)).run σ_log) =
    (fun p =>
      ((p.1.1, replaceDrv (drvMirrorTblToV (ℓ := ℓ) p.2.1.toModelDriverBase) p.1.2), p.2)) <$>
      (((simulateQ (cliHonestStepImplWith P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K qep
          decT encT) oa).run s_lst).run σ_log) := by
  induction oa using OracleComp.inductionOn generalizing s_lst σ_log with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q mx ih =>
    rw [run_simulateQ_query_bind, StateT.run_bind, run_simulateQ_query_bind, StateT.run_bind]
    obtain ⟨hStepEq, hStepInv⟩ := cliHonestTblStepImplWith_coupled P hP C K qep decT encT hInv q
    rw [hStepEq, bind_map_left]
    exact probComp_bind_eq_map_bind _ _ fun ⟨⟨u, s_lst'⟩, σ_log'⟩ hout =>
      ih u (hStepInv _ hout)

theorem cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTbl_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    cliE2EExpWithKiCoinLogged true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) =
      cliE2EExpWithKiCoinLogged true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) := by
  let B := cliGameAdversaryReassoc A
  let ki := SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P
  have hTblEval :
      (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) () =
      Prod.fst <$>
        ((simulateQ (handlerImpl (C := e2eBhAdapterCodec S ℓ)
          (I := e2eBhAdapterIface S ℓ)
          (cliAdapterHandleTbl decT encT S ℓ)) B).run
          (replaceDrv (drvMirrorTblToV (ℓ := ℓ) ({} : ModelDriverBase S))
            (cliAdapterStateToV (ℓ := ℓ) (cliAdapterInitState S)))) := by
    dsimp [CostedReduction.eval, CostedReduction.impl, cliToModelAdapterProgTbl, Comp.eval,
      Expr.eval, Env.get, replaceDrv, cliAdapterInitState, cliAdapterStateToV, drvMirrorTblToV,
      prinsTblOfList, bundlesTblOfList, opksTblOfList, sendsOpkTblOfList, sendsNoOpkTblOfList]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    rfl
  have hHonEval :
      (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) () =
      Prod.fst <$>
        ((simulateQ (handlerImpl (C := e2eBhAdapterCodec S ℓ)
          (I := e2eBhAdapterIface S ℓ)
          (cliAdapterHandle decT encT S ℓ)) B).run
          (cliAdapterStateToV (ℓ := ℓ) (cliAdapterInitState S))) := by
    dsimp [CostedReduction.eval, CostedReduction.impl, cliToModelAdapterProg, Comp.eval,
      Expr.eval, Env.get, cliAdapterInitState, cliAdapterStateToV, drvMirrorToV]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    rfl
  have hEqHon :
      cliE2EExpWithKiCoinLogged true S P ki C K ℓ qep decT encT
        ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ()) =
      cliE2EExpWithKiCoinLogged true S P ki C K ℓ qep decT encT
        ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ()) := by
    have hSimEq : ∀ b : Bool,
        ((simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
          ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ())).run
          { b := b, st := SignalPqxdh.KeyIndState.empty S true }) =
        ((simulateQ (cliE2EDrvImplWithCoinLogged P ki C K qep decT encT)
          ((cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval (fun _ => B) ())).run
          { b := b, st := SignalPqxdh.KeyIndState.empty S true }) := fun b => by
      apply WriterT.ext
      rw [run_simulateQ_cliE2EDrvImplWithCoinLogged_nil,
        run_simulateQ_cliE2EDrvImplWithCoinLogged_nil]
      congr 1
      rw [hTblEval, hHonEval]
      simp only [map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure]
      dsimp only [ki]
      have hInitDrv : ({} : ModelDriverBase S) =
          (({ b := b, st := SignalPqxdh.KeyIndState.empty S true }, ([] : List (BitVec 512))) :
            DrvLogState S ℓ).1.toModelDriverBase := rfl
      rw [simulateQ_cliE2EDrvImplWith_honestTbl_run, simulateQ_cliE2EDrvImplWith_honest_run,
        hInitDrv,
        simulateQ_cliHonestTblStepImplWith_eq_map P hP C K qep decT encT B
          (tblListCouplingInv_init b true)]
      simp only [bind_map_left]
    unfold cliE2EExpWithKiCoinLogged
    simp only [hSimEq]
  exact hEqHon.trans (cliE2EExpWithKiCoinLogged_cliToModelAdapterProg_eq_L_bh S P C K ℓ qep
    decT encT A)

theorem cliE2EExpWithKi_cliToModelAdapterProgTbl_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) =
      cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) := by
  rw [← cliE2EExpWithKiCoinLogged_fst, ← cliE2EExpWithKiCoinLogged_fst,
    cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTbl_eq_L_bh S P hP C K ℓ qep decT encT A]

theorem evalDist_cliE2EExpWithKi_cliToModelAdapterProgTbl_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ())) =
      evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ())) :=
  congrArg evalDist
    (cliE2EExpWithKi_cliToModelAdapterProgTbl_eq_L_bh S P hP C K ℓ qep decT encT A)

/-- Exact `boolBias` equivalence between `cliToModelAdapterProgTbl` and `L_bh` inside
`cliE2EExpWithKi` under `WellFormedPrimitivesδ P`. -/
theorem boolBias_cliE2EExpWithKi_cliToModelAdapterProgTbl_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    (evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()))).boolBias =
      (evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()))).boolBias := by
  rw [evalDist_cliE2EExpWithKi_cliToModelAdapterProgTbl_eq_L_bh S P hP C K ℓ qep decT encT A]

end TightTblAdapter

end Computational.Proofs.E2E.Dsl.CliAdapterCosted

