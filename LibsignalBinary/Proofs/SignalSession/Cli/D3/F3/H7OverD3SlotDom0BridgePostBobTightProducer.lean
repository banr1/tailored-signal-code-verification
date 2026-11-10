/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `verNeEnv`-Parametric and Fixed-Budget `OverD3` Poll Producers

Specializes the Stage-P2 and Stage-P4 `OverD3` contracts to a single `RunBudgets` parameter,
generalizes the Stage-P3 `VerNe` obligation from `VerNeTopEnv` to an arbitrary `verNeEnv`, and
provides closed `VerNeTightTopRawEnv` poll producers extracting `SessionGhostValid` from memory.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobTightProducer

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  LibsignalFullPlacement LibsignalPlacement lsMemcpySym lsRustAllocSym lsRustDeallocSym
  lsRustNoAllocShimSym ls_hook_ok_ultra_of_mem lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (LsTokenInitM3)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (OverPrevEncOK)
open CryptoVerification.CliHandshake.RespClosurePlaced (instIsLsBlockProg_518 lsProg_518)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (LsTokenInit dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (cliGhostExterns_sat_of_cliExternsPlaced)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  pollTryDecryptM3PlacedSpecP pollTryDecryptM3PlacedSpecTPTight
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody stageP3Gen_prev1_vregs_at_full_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux (VerNeTopEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (VerNeTightTopRawEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollAuxPlacedBudget (
  StageP4Prev1VRegsAtPlacedStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget (
  CliDpPollOkOverV4StateFrozenPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget (
  StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget (
  StageP3Prev1D3FrozenPlacedStmt cliGrowOneSpe_518_placed_ok cliSetSessionState_518_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.StageP3RawBodyPlacedBudget (
  cliVerNe1e04_full_placed_ok_raw
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob (
  DecPkD3ValidOverOfEnv' DecPkD3ValidOverTightOfEnv'
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobProducerAux (
  H7pbDecPkD3ValidOverOfEnv'
  H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt
  H7pbStageP3Prev1D3OfVerNeAtFrozenPlacedStmt
  H7pbStageP3Prev1D3OfVerNeFrozenPlacedStmt
  H7pbStageP4Prev1VRegsAtBPlacedStmt
  h7pb_decPk_d3_validOver_poll_ofVerNe_at_b_at_full_placedBudget'
  h7pb_decPk_d3_validOver_poll_ofVerNe_at_b_full_placedBudget'
  h7pb_stageP2OverQpanCliD3FrozenAtB_of_forall
  h7pb_stageP3Prev1D3OfVerNe_top_iff
  h7pb_stageP4Prev1VRegsAtB_of_forall
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  CliStageP4Prev1Envs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudget (
  overPollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  pollTryDecryptPlacedSpecP pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_shim_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Fixed-`B` and `verNeEnv`-Parametric Stage Statements + Sanity Bridges -/

theorem h7pbt_decPkD3ValidOverOfEnv'_eq :
    @H7pbDecPkD3ValidOverOfEnv' = @DecPkD3ValidOverOfEnv' :=
  rfl

/-- `StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt` specialized to a single `(B : RunBudgets)`. -/
abbrev StageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt :=
  @H7pbStageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt

theorem stageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt_of_forall [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : UnreachedPqxdhPrimitives} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} (B : RunBudgets)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (h : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W P2OverErrEnv P2OverOkEnv) :
    StageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv :=
  h7pb_stageP2OverQpanCliD3FrozenAtB_of_forall B h

/-- `StageP3Prev1D3FrozenPlacedStmt` with `VerNeTopEnv` generalized to `verNeEnv`. -/
abbrev StageP3Prev1D3OfVerNeFrozenPlacedStmt :=
  @H7pbStageP3Prev1D3OfVerNeFrozenPlacedStmt

theorem stageP3Prev1D3OfVerNeFrozenPlacedStmt_top_iff [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop} :
    StageP3Prev1D3OfVerNeFrozenPlacedStmt A lim tdEnv VerNeTopEnv ↔
      StageP3Prev1D3FrozenPlacedStmt A lim tdEnv :=
  h7pb_stageP3Prev1D3OfVerNe_top_iff

/-- `StageP4Prev1VRegsAtPlacedStmt` specialized to a single `(B : RunBudgets)`. -/
abbrev StageP4Prev1VRegsAtBPlacedStmt :=
  @H7pbStageP4Prev1VRegsAtBPlacedStmt

theorem stageP4Prev1VRegsAtBPlacedStmt_of_forall [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (B : RunBudgets)
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (h : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs) :
    StageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs :=
  h7pb_stageP4Prev1VRegsAtB_of_forall B h

/-! ## 2. `[LibsignalFullPlacement]` Stage-P3 Discharger Over `stageP3Gen_prev1_vregs_at_full_placed_ok` -/

private theorem h7pbt_pollTryDecryptM3PlacedSpecTPTight_eq_over [LibsignalPlacement]
    {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidParse S tdEnv =
      overPollTryDecryptPlacedSpecTPTight C A lim ctl uuidParse S tdEnv := by
  dsimp only [pollTryDecryptM3PlacedSpecTPTight, overPollTryDecryptPlacedSpecTPTight,
    pollTryDecryptPlacedSpecTPTight, pollTryDecryptM3PlacedSpecP, pollTryDecryptPlacedSpecP,
    LsTokenInitM3, LsTokenInit]
  rfl

private theorem h7pbt_stageP3Prev1D3_ofVerNe_at_full_placed_of_verNeAt [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hVerNeAt :
      CliGhostAllocHooks M A lim gh →
      AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
      OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK verNeEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    H7pbStageP3Prev1D3OfVerNeAtFrozenPlacedStmt A lim tdEnv verNeEnv mmpl gh W := by
  intro st_b hG hAllocX hcc hscc hroot hDropSS3 s0 s coroPtr ctxPtr outPtr initErrsPtr
    prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest recG st rem loc
    msgG msg F_frame Q hfits hinit hcap hprev hv4 hns hsd hrc hpq hfr hpc hrun hsp hroot_sp hfp
    htr hvregs hOk hErr hVerNe
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hshim : subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym)
      sessionShimBudgetSpec :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
        cliExternsPlaced_shim_budget_sat mmpl gh W hG.shim_eq)
      (by decide)
  have halloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false) :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
        cliExternsPlaced_alloc_budget_sat mmpl gh W hG)
      (by decide)
  have hdealloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem
      ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
        cliExternsPlaced_dealloc_budget_sat mmpl gh W hG)
      (by decide)
  have hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym)
      sessionMemcpyRegionBudgetSpec :=
    ls_hook_ok_ultra_of_mem
      ((show ("memcpy" : String) = lsMemcpySym by decide) ▸
        cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hG)
      (by decide)
  have hrootM3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))) := by
    rw [h7pbt_pollTryDecryptM3PlacedSpecTPTight_eq_over]
    exact hroot
  exact stageP3Gen_prev1_vregs_at_full_placed_ok ext W.C 0#64 W.Q.K
    hshim halloc hdealloc hmemcpy
    (cliGrowOneSpe_518_placed_ok mmpl gh W hG)
    (cliSetSessionState_518_placed_ok mmpl gh W hG)
    hDropSS3 hcc hscc hrootM3 (hVerNeAt hG hAllocX hDropSS3)
    st_b s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer b_2c0 enc rest recG st rem loc msgG msg F_frame Q
    hfits hinit hcap hprev hv4 hns hsd hrc hpq hfr hpc hrun hsp hroot_sp hfp htr hvregs
    (fun G₁ G' pt ptCap ptPtr evs_ok s' P_s' => hOk G₁ G' evs_ok pt ptCap ptPtr s' P_s')
    (fun G₁ G' e evs_err sf P_f => hErr G₁ G' evs_err e sf P_f)
    (fun evs_vn sf P_f hver hevs hPf => hVerNe evs_vn sf P_f hver hevs
      (Entails.trans hPf (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
          (sepConj_mono_right (entails_anyHeap emp)))))))))

/-- Discharges `StageP3Prev1D3OfVerNeFrozenPlacedStmt` via `stageP3Gen_prev1_vregs_at_full_placed_ok`. -/
theorem stageP3Prev1D3_ofVerNe_full_placed_of_verNeAt [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hVerNeAt : ∀ (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks),
      CliGhostAllocHooks M A lim gh →
      AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
      OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK verNeEnv
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP3Prev1D3OfVerNeFrozenPlacedStmt A lim tdEnv verNeEnv :=
  fun mmpl gh W =>
    h7pbt_stageP3Prev1D3_ofVerNe_at_full_placed_of_verNeAt mmpl gh W (hVerNeAt mmpl gh W)

/-! ## 3. `verNeEnv`-Parametric Poll Producers -/

/-- Fixed-`B`, `verNeEnv`-parametric poll producer extracting `SessionGhostValid` on `ses0` and
`ses'` from memory, with `hEnv` stated over `DecPkD3ValidOverOfEnv'`. -/
theorem decPk_d3_validOver_poll_ofVerNe_at_b_full_placedBudget' [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2O : StageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv)
    (hP3O : StageP3Prev1D3OfVerNeFrozenPlacedStmt A lim tdEnv verNeEnv)
    (hP4O : StageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      DecPkD3ValidOverOfEnv' A.repAlloc verNeEnv W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  h7pb_decPk_d3_validOver_poll_ofVerNe_at_b_full_placedBudget'
    hDropNz mmpl gh W X B S Scope hP2O hP3O hP4O hTry hEnv

/-- Fixed-`B` `[LibsignalFullPlacement]` poll producer discharging the Stage-P3 continuation
internally from `hVerNeAt`. -/
theorem decPk_d3_validOver_ofVerNe_at_b_poll_at_full_placedBudget' [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2O : StageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv)
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK verNeEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hP4O : StageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      DecPkD3ValidOverOfEnv' A.repAlloc verNeEnv W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  h7pb_decPk_d3_validOver_poll_ofVerNe_at_b_at_full_placedBudget'
    hDropNz mmpl gh W X B S Scope hP2O
    (h7pbt_stageP3Prev1D3_ofVerNe_at_full_placed_of_verNeAt mmpl gh W fun _ _ _ => hVerNeAt)
    hP4O hTry hEnv

/-- `∀ B` `[LibsignalFullPlacement]` poll producer parameterized by `verNeEnv` and `hVerNeAt`. -/
theorem decPk_d3_validOver_ofVerNe_poll_at_full_placedBudget' [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hP2O : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv)
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK verNeEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hP4O : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      DecPkD3ValidOverOfEnv' A.repAlloc verNeEnv W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  decPk_d3_validOver_ofVerNe_at_b_poll_at_full_placedBudget'
    hDropNz mmpl gh W X B S Scope
    (stageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt_of_forall B hP2O)
    hVerNeAt
    (stageP4Prev1VRegsAtBPlacedStmt_of_forall B hP4O)
    hTry hEnv

/-! ## 4. Closed `VerNeTightTopRawEnv` Poll Producers -/

/-- Closed `VerNeTightTopRawEnv` instance of `StageP3Prev1D3OfVerNeFrozenPlacedStmt` via `cliVerNe1e04_full_placed_ok_raw`. -/
theorem stageP3Prev1D3_tightRaw_full_placed_ok [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop) :
    StageP3Prev1D3OfVerNeFrozenPlacedStmt A lim tdEnv VerNeTightTopRawEnv :=
  fun mmpl gh W =>
    h7pbt_stageP3Prev1D3_ofVerNe_at_full_placed_of_verNeAt mmpl gh W
      fun hG _ _ => cliVerNe1e04_full_placed_ok_raw mmpl gh W hG

/-- Fixed-`B` `[LibsignalFullPlacement]` poll producer specialized to `VerNeTightTopRawEnv` and `DecPkD3ValidOverTightOfEnv'`. -/
theorem decPk_d3_validOver_tightRaw_at_b_poll_at_full_placedBudget' [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hP2O : StageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt A lim X mmpl gh W B
      P2OverErrEnv P2OverOkEnv)
    (hP4O : StageP4Prev1VRegsAtBPlacedStmt A lim mmpl gh W B p4Envs)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      DecPkD3ValidOverTightOfEnv' A.repAlloc W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  decPk_d3_validOver_poll_ofVerNe_at_b_full_placedBudget'
    hDropNz mmpl gh W X B S Scope hP2O
    (stageP3Prev1D3_tightRaw_full_placed_ok A lim tdEnv)
    hP4O hTry hEnv

/-- `∀ B` `[LibsignalFullPlacement]` poll producer specialized to `VerNeTightTopRawEnv` and `DecPkD3ValidOverTightOfEnv'`. -/
theorem decPk_d3_validOver_tightRaw_poll_at_full_placedBudget' [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A.repAlloc) B F0 peer pid kpkId spkId kbk}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hP2O : StageP2OverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W
      P2OverErrEnv P2OverOkEnv)
    (hP4O : StageP4Prev1VRegsAtPlacedStmt A lim mmpl gh W p4Envs)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hTry : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (overPollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) (tdEnv W))))
    (hEnv : ∀ g evs,
      DecPkD3ValidOverTightOfEnv' A.repAlloc W X B ReadEnv DeserEnv
        P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs →
      DecPkEnv g evs) :
    CliDpPollOkOverV4StateFrozenPlacedAt A lim ReadEnv DeserEnv DecPkEnv mmpl gh W X B S Scope :=
  decPk_d3_validOver_tightRaw_at_b_poll_at_full_placedBudget'
    hDropNz mmpl gh W X B S Scope
    (stageP2OverQpanCliD3FrozenAtBPlacedBudgetStmt_of_forall B hP2O)
    (stageP4Prev1VRegsAtBPlacedStmt_of_forall B hP4O)
    hTry hEnv

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBobTightProducer
