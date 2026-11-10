/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAtFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3BudgetFitsAux
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3InitAux
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3VerifySigAux

/-!
# Spine-C Slot `521` (`initiate`) Closure at `h2k_ghFixedK` (`ElfSlicesPqOomH2KSlot521`)

**Checked by Lean.**

Discharges `ElfSlicesPqOomH2KIfaces.h2ki_W3InitSlot521OkK` (`signal_session_handshake::initiate`,
Block `521`) via `AllocWithFds.withFds`, `CliInitSlotOkPlacedAtFd`, `AllocWithFdsStrClone`, and
`Hole3W3BudgetFitsAux.w3m_cliInitiate_placed_ok_of_local`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot521

open Arm64 (GhostName HookFsTraced HookSat SepProp State subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoVerification (LibsignalFullPlacement LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym
   lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced initProgPlaced transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk (cliFormatInner_budget_sat)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (CliInitSlotOkPlacedAt ExternNoAllocFailed Stage3OkEventsFit Stage3OkEventsOut
   lsProg_not_allocFailedIn_cliGhost stage3PlacedOk_okEvents w3Local_placed_ok_of_seams)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAtFd
  (cliInitSlotOkPlacedAt_preFd_of_withFds w3Exist_withFds_placed_ok_of_hooks_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (withLsRetAddr624AndFds)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (ReadFileRuleEnvFixed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (cliGhostSpqrAllocHooks_withFds withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFdsStrClone
  (hookSat_stringCloneBudget_withFds_of_enforced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
  (cliExistingStoreCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced spqrInitialStateInnerSpec verifySignatureInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
  (subroutine_ok_semInitSlot_of_noAllocFail)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliSpqrInitialState_initProg)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (InitialStateParamsEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
  (h2kb_hole2_hGSpqr h2kb_stringCloneBudget_hookSat)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_ghFixedK h2k_hole2_hFsK h2k_hole2_hghNoAllocK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (CliInitSlotOkPlacedPreFd h2ki_W3InitSlot521OkK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA
  (h2k_hole2_readFile_hookSat_lsRetAddr624AndFds)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
  (h2kb_stringCloneBudget_withFdsGe3Closed_hookSat)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3BudgetFitsAux
  (W3CliInitiateBudgetFits w3m_cliInitiate_placed_ok_of_local w3m_initiate_budgetFits)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3InitAux
  (w3m_libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3VerifySigAux
  (w3m_verifySignature_vm_ok)

/-! ## `W3CliInitiateBudgetFits`-Backed `CliInitSlotOkPlacedPreFd` Producer -/

/-- Produces `CliInitSlotOkPlacedPreFd` at `(withFds A)` from `W3CliInitiateBudgetFits`,
`withLsRetAddr624AndFds` `readFile` `HookSat`, and `withFdsGe3Closed` `stringClone` `HookSat`. -/
theorem w3m_cliInitSlotOkPlacedPreFd_of_hooks_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hGSpqr : CliGhostSpqrAllocHooks M A lim gh')
    (hStrFsT : ∀ f, gh'.stringClone = some f → HookFsTraced IsFsC f)
    (hStrClone0 : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hStrCloneFd : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsStringCloneSym
      (withFdsGe3Closed (stringCloneBudgetSpec M A lim)))
    (hReadSatFd : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsReadFileSym
      (withLsRetAddr624AndFds
        (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)))
    (hSpqrInit' : subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec (withFds A) lim InitStateEnv W.C.F)))
    (hVerifySig : ∀ (Y : UnreachedPqxdhPrimitives),
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 203)
        (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          W3CliInitiateBudgetFits M lim (cliExistingStoreCalleesEnvs ReadEnv) InitStateEnv InitEnv
            (Stage3OkEventsFit lim InitEnv W X) (Stage3OkEventsOut W X) W X x s0 st0) :
    CliInitSlotOkPlacedPreFd mmpl gh' A lim InitEnv X W := by
  let hAlloc' := cliGhostSpqrAllocHooks_withFds hGSpqr
  let hStrClone' := hookSat_stringCloneBudget_withFds_of_enforced henf hStrCloneFd
  let hFmt0 := cliFormatInner_budget_sat (A := A) (lim := lim) mmpl gh' W
  let hFmt' := cliFormatInner_budget_sat (A := withFds A) (lim := lim) mmpl gh' W
  let hh0 :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced.of_hooks
      mmpl gh' W hGSpqr hStrFsT hStrClone0 hFmt0
  let hh' :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced.of_hooks
      mmpl gh' W hAlloc' hStrFsT hStrClone' hFmt'
  let hh3' :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced.of_hooks
      mmpl gh' W hAlloc' hStrFsT hStrClone' hFmt'
  have hExist' :=
    w3Exist_withFds_placed_ok_of_hooks_fd mmpl gh' W A lim henf ReadEnv hh0 hh' hh3' hReadSatFd
  have hLocal' : ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
      InitLocalCalleesPlaced (withFds A) lim InitStateEnv mmpl gh' W stk :=
    fun hstk hstk64 =>
      w3Local_placed_ok_of_seams mmpl gh' W (withFds A) lim InitStateEnv cliRunBudgets
        hh3' hSpqrInit' hVerifySig hstk hstk64
  have hSlot' : CliInitSlotOkPlacedAt (cliGhostExterns gh' (cliExternsPlaced mmpl W))
      (withFds A) lim InitEnv X W := by
    intro S sEnvs needs henv hfiles hS hinitOk hneed stk h1 h2
    dsimp only [slotsOfPlaced, mkSlot] at h1 ⊢
    have hstk : cliInitiateNeed cliRunBudgets ≤ stk := hneed ▸ h1
    rw [henv]
    have h521 := w3m_cliInitiate_placed_ok_of_local mmpl gh' W X cliRunBudgets S
      hh3' hExist' hLocal'
      (stage3PlacedOk_okEvents (withFds A) lim InitStateEnv InitEnv mmpl gh' W X cliRunBudgets S)
      hS (fun _ _ _ _ hio => hinitOk ▸ hio)
      stk hstk h2 (hFits S hfiles hS hinitOk hstk h2)
    have h579 := transfer_withLsCodeRoLoaded
      (callerProg := lsProg_579 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
      (hi := (by decide : 579 < 619)) h521
    exact subroutine_ok_semInitSlot_of_noAllocFail h579
      (lsProg_not_allocFailedIn_cliGhost mmpl gh' W hghNoAlloc)
  intro S sEnvs needs henv hfiles hS hinitOk hneed stk h1 h2
  exact cliInitSlotOkPlacedAt_preFd_of_withFds henf hSlot'
    S sEnvs needs henv hfiles hS hinitOk hneed stk h1 h2

/-! ## Concrete `h2k_ghFixedK` and Witness-Packaged `h2ki_W3InitSlot521OkK` Entrypoints -/

/-- Concrete `h2k_ghFixedK mpl mmpl` Spine-C Slot-`521` (`initiate`) closure on `cliElfBytes`. -/
theorem h2k_ghost_w3InitSlot521Ok_cliElfK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    mpl.base 547 ≠ 0#64 →
    ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      CliInitSlotOkPlacedPreFd mmpl (h2k_ghFixedK mpl mmpl)
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (realCliInitBinarySlotEnvFixed W) X W := by
  letI : LibsignalFullPlacement :=
    w3m_libsignalFullPlacementOf mpl hLs (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro _h547 X W γ tp
  have hGSpqr := h2kb_hole2_hGSpqr mpl mmpl hLs hMm γ tp
  have hFs := h2k_hole2_hFsK mpl mmpl hLs hMm
  exact w3m_cliInitSlotOkPlacedPreFd_of_hooks_fd (rfl : cliBudgetLimits.enforced = true)
    (InitStateEnv := InitialStateParamsEnv W.C.F)
    mmpl (h2k_ghFixedK mpl mmpl) W X
    hGSpqr
    hFs.stringClone_fsT
    (h2kb_stringCloneBudget_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp)
    (h2kb_stringCloneBudget_withFdsGe3Closed_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp)
    (h2k_hole2_readFile_hookSat_lsRetAddr624AndFds mpl mmpl hLs hMm W γ tp)
    (cliSpqrInitialState_initProg mmpl (h2k_ghFixedK mpl mmpl) W
      (cliGhostSpqrAllocHooks_withFds hGSpqr))
    (w3m_verifySignature_vm_ok (h2k_ghFixedK mpl mmpl) W hGSpqr.toCliGhostAllocHooks)
    (h2k_hole2_hghNoAllocK mpl mmpl hLs hMm)
    (w3m_initiate_budgetFits W X)

/-- Witness-packaged `readFile` (`withLsRetAddr624AndFds`) and `stringClone`
(`withFdsGe3Closed`) hook companion predicate for `w : F3CliElfGhostWitnessK mpl mmpl`. -/
structure F3WitnessW3HooksFd {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop where
  strClone0 :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)) lsStringCloneSym
        (stringCloneBudgetSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)
  strCloneFd :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)) lsStringCloneSym
        (withFdsGe3Closed
          (stringCloneBudgetSpec fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits))
  readFileFd :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (withLsRetAddr624AndFds
          (readFileSpecPlaced cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))

theorem f3WitnessW3HooksFd_mkF3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    F3WitnessW3HooksFd (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) where
  strClone0 W γ tp :=
    h2kb_stringCloneBudget_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp
  strCloneFd W γ tp :=
    h2kb_stringCloneBudget_withFdsGe3Closed_hookSat mpl mmpl hLs hMm (cliExternsPlaced mmpl W) γ tp
  readFileFd W γ tp :=
    h2k_hole2_readFile_hookSat_lsRetAddr624AndFds mpl mmpl hLs hMm W γ tp

/-- Witness-parametric `h2ki_W3InitSlot521OkK w` discharge from `F3WitnessW3HooksFd w`. -/
theorem h2k_w3InitSlot521Ok_of_witnessK
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hW3Fd : F3WitnessW3HooksFd w) :
    h2ki_W3InitSlot521OkK w := by
  letI : LibsignalFullPlacement :=
    w3m_libsignalFullPlacementOf mpl hLs w.hblk w.hext_nodup
  intro _h547 X W γ tp
  have hGSpqr :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA.F3CliElfGhostWitnessK.hGSpqr
      w hLs γ tp
  exact w3m_cliInitSlotOkPlacedPreFd_of_hooks_fd (rfl : cliBudgetLimits.enforced = true)
    (InitStateEnv := InitialStateParamsEnv W.C.F)
    mmpl w.ghFixed W X
    hGSpqr
    w.hFs.stringClone_fsT
    (hW3Fd.strClone0 W γ tp)
    (hW3Fd.strCloneFd W γ tp)
    (hW3Fd.readFileFd W γ tp)
    (cliSpqrInitialState_initProg mmpl w.ghFixed W (cliGhostSpqrAllocHooks_withFds hGSpqr))
    (w3m_verifySignature_vm_ok w.ghFixed W hGSpqr.toCliGhostAllocHooks)
    w.hghNoAlloc
    (w3m_initiate_budgetFits W X)

/-- Unconditional `h2ki_W3InitSlot521OkK` discharge at
`mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2`. -/
theorem h2k_w3InitSlot521Ok_mkWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2ki_W3InitSlot521OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k_w3InitSlot521Ok_of_witnessK
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)
    hLs
    (f3WitnessW3HooksFd_mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot521
