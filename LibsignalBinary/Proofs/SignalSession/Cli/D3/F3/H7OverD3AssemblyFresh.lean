/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueOverF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget

/-!
# Parametric `MainOkOverD3F3` Assembly over `LibsignalFrozen`

Parametric bridges from `Block617TransferFixedHyp`, `MainIoOfPlaced`,
`MainEntryBudgetFitsCapOf`, and the four `slotsOfSigPkFrozenPlaced` slot contracts to
`MainOkOverD3F3` over `LibsignalFrozen mpl`, keeping `ReadEnv`, `sEnvsOf` / `DecPkSlotEnv`,
and `PksmEnv` abstract.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3AssemblyFresh

open Arm64 (GhostName HookOk Memory subroutine_ok)
open Arm64.Obj (MultiPlacement)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns lsProg_51 lsmpl lsρ withLsCl)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives aesDecHookMallocng)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced libsignalSessionLib lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliMainStk cliResStack cliRunBudgets cliRunNeeds cliWrOk
   instLsCodeInvFrozen mProgPlaced mainFrameSize)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost Init2Data InitGhost PksmGhost addrValOf runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
  (PromoteOverEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
  (DecPkD3ValidOverEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
  (cliRunSemOverV4 decPkValidOverSlotOk_at_full_of_readEnv_ofEnv_placedBudget pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverStage2PlacedBudget
  (StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
  (Block617TransferFixedHyp mainSubroutineD3F3_of_domScopedRunTight)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueOverF3
  (mainOkOverD3F3_of_mainSubroutine)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (MainOkOverD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
  (runNeed_cli_le_resStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
  (PksmSlotOkPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliInitSlotOkPlaced CliPubCalleesFrozenPlaced CliRunHooksBundle cliPubCallees_d2c_frozen_ok
   cliRunArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunEnv run_ok_frozen_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
  (cliPollStageP4Prev1Envs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmLoopEnv PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
  (subsetA4PksmTryFromPlaced_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (cliPksmTryFrom_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
  (hc_kemDeserialize_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. `[LibsignalFullPlacement]` Instances Aligned with `libsignalPlacementOf` -/

/-- Builds `[LibsignalFullPlacement]` whose `toLibsignalPlacement` is definitionally
`libsignalPlacementOf mpl hblk hext_nodup` from `hPl : libsignalSessionLib.Placeable mpl`. -/
@[instance_reducible]
def h7f_libsignalFullPlacementOfPlaceable
    (mpl : MultiPlacement)
    (hPl : libsignalSessionLib.Placeable mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalFullPlacement where
  toLibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  placeable := hPl

/-- Builds `[LibsignalFullPlacement]` whose `toLibsignalPlacement` is definitionally
`libsignalPlacementOf mpl hblk hext_nodup` from any `hLs : libsignalSessionLib.LinkedAt imgBytes mpl`. -/
@[instance_reducible]
def h7f_libsignalFullPlacementOfLinkedAt
    {imgBytes : List (BitVec 8)}
    (mpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt imgBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalFullPlacement :=
  h7f_libsignalFullPlacementOfPlaceable mpl hLs.choose_spec.2.1 hblk hext_nodup

/-! ## 2. Block-`111` `PksmTryFrom` & `CliPubCalleesFrozenPlaced` Helpers -/

/-- Byte-extensionality of `PksmTryFromEnv`. -/
theorem h7f_pksmTryFromEnv_congr (x y : PksmGhost) (hb : x.bytes = y.bytes) :
    PksmTryFromEnv x = PksmTryFromEnv y := by
  have hloop : PksmLoopEnv x = PksmLoopEnv y := by
    funext evs; dsimp [PksmLoopEnv]; rw [hb]
  funext evs; apply propext; constructor
  · intro h
    cases h with
    | nil => exact .nil
    | loopOnly hcons hge hle hl =>
      exact .loopOnly (hb.symm.trans hcons) hge hle (hloop ▸ hl)
    | loopAfter hcons hge hle hl ha =>
      exact .loopAfter (hb.symm.trans hcons) hge hle (hloop ▸ hl) (hb ▸ ha)
  · intro h
    cases h with
    | nil => exact .nil
    | loopOnly hcons hge hle hl =>
      exact .loopOnly (hb.trans hcons) hge hle (hloop.symm ▸ hl)
    | loopAfter hcons hge hle hl ha =>
      exact .loopAfter (hb.trans hcons) hge hle (hloop.symm ▸ hl) (hb.symm ▸ ha)

/-- Discharges `PksmSlotOkPlacedAt` (Block `111`) at `PksmTryFromEnv` from `CliGhostAllocHooks`. -/
theorem h7f_pksmSlotOk_pksmTryFromEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    PksmSlotOkPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) A lim PksmTryFromEnv := by
  intro S hS
  exact cliPksmTryFrom_placed_at_block
    (callerProg := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
    (subsetA4PksmTryFromPlaced_cli mmpl gh W hG)
    (fun b => congrFun hS b)

/-- Parametric `CliPubCalleesFrozenPlaced` constructor for arbitrary `ReadEnv`, `sEnvs`, and `PksmEnv`. -/
theorem h7f_cliPubCallees_of_pksm_frozen_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmEnv : PksmGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl gh W A lim ReadEnv)
    (hinit_addr : ∀ gc d2 fsp,
      sEnvs.initiate (r1cInitGhost gc d2 fsp) = sEnvs.initiate (r1cInitGhost gc d2 0#64))
    (henc_addr : ∀ gc peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost gc peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ gc fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 gc peerV meG m))
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmEnv x = PksmEnv y)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y) :
    CliPubCalleesFrozenPlaced mmpl gh A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmEnv) W :=
  cliPubCallees_d2c_frozen_ok mmpl gh W hHooks
    hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost

/-- Specialization of `h7f_cliPubCallees_of_pksm_frozen_placed` to `PksmTryFromEnv`. -/
theorem h7f_cliPubCallees_frozen_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl gh W A lim ReadEnv)
    (hinit_addr : ∀ gc d2 fsp,
      sEnvs.initiate (r1cInitGhost gc d2 fsp) = sEnvs.initiate (r1cInitGhost gc d2 0#64))
    (henc_addr : ∀ gc peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost gc peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ gc fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 gc peerV meG m))
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y) :
    CliPubCalleesFrozenPlaced mmpl gh A lim (cliRunCalleesEnvs ReadEnv) sEnvs
      (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv) W :=
  h7f_cliPubCallees_of_pksm_frozen_placed mmpl gh W hHooks
    hinit_addr henc_addr hdec_ghost h7f_pksmTryFromEnv_congr hdp_ghost

/-! ## 3. Block-`579` `runSpecTightPlaced (LibsignalFrozen lsmpl)` over `cliRunSemOverV4` -/

/-- Parametric Block-`579` `signal_session::run` (`runSpecTightPlaced (LibsignalFrozen lsmpl)`)
assembly over `cliRunSemOverV4 X W` for arbitrary `ReadEnv`, `sEnvs`, and `PksmEnv`. -/
theorem h7f_hrun_overV4_sEnvs_pksm_frozen_placed [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {PksmEnv : PksmGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl gh W A lim ReadEnv)
    (hinit_addr : ∀ gc d2 fsp,
      sEnvs.initiate (r1cInitGhost gc d2 fsp) = sEnvs.initiate (r1cInitGhost gc d2 0#64))
    (henc_addr : ∀ gc peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost gc peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ gc fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 gc peerV meG m))
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmEnv x = PksmEnv y)
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y)
    (hpksm : PksmSlotOkPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) A lim PksmEnv)
    (hEnc :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hDecSig :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hInit :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).initiate.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 521))
    (hDecPk :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmEnv (cliRunSemOverV4 X W)))
        uuidTryParse
        (runRel (cliRunSemOverV4 X W))
        cliWrOk cliResStack) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let S := cliRunSemOverV4 X W
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hh := hHooks.runHooks
  have hpub := h7f_cliPubCallees_of_pksm_frozen_placed mmpl gh W hHooks
    hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost
  have hcallees : RunCalleesPlaced A lim (cliRunCalleesEnvs ReadEnv)
      H cliRunBudgets (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) :=
    { readFile := hHooks.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt := hEnc
      decryptSignal := hDecSig
      initiate := hInit
      decryptPrekey := hDecPk
      kemDeserialize :=
        hc_kemDeserialize_placed (callerProg := lsProg_579 H) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }
  exact
    run_ok_frozen_placed_at_block
      (callerProg := mProgPlaced H) (i := 617)
      (hpub.arms S (cliDecryptPrekeyNeed cliRunBudgets))
      hh
      hcallees
      (hpksm S rfl)
      (runNeed_cli_le_resStack_placed A lim sEnvs
        (S := S) (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets) (by decide))
      (by decide)
      (by decide)

/-- Specialization of `h7f_hrun_overV4_sEnvs_pksm_frozen_placed` to `PksmTryFromEnv`, discharging
Block `111` internally from `CliGhostAllocHooks`. -/
theorem h7f_hrun_overV4_sEnvs_frozen_placed [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs}
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim ReadEnv)
    (hinit_addr : ∀ gc d2 fsp,
      sEnvs.initiate (r1cInitGhost gc d2 fsp) = sEnvs.initiate (r1cInitGhost gc d2 0#64))
    (henc_addr : ∀ gc peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost gc peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ gc fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 gc peerV meG m))
    (hdp_ghost : ∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y)
    (hEnc :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hDecSig :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hInit :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).initiate.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 521))
    (hDecPk :
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) sEnvs PksmTryFromEnv
          (cliRunSemOverV4 X W)))
        uuidTryParse
        (runRel (cliRunSemOverV4 X W))
        cliWrOk cliResStack) :=
  h7f_hrun_overV4_sEnvs_pksm_frozen_placed mmpl gh X W hHooks
    hinit_addr henc_addr hdec_ghost h7f_pksmTryFromEnv_congr hdp_ghost
    (h7f_pksmSlotOk_pksmTryFromEnv mmpl gh W hG)
    hEnc hDecSig hInit hDecPk

/-! ## 4. Block-`520` `validOver` Slot Wrapper from `SpqrV1PlacedSeamsOfEnv` -/

/-- Specializes `decPkValidOverSlotOk_at_full_of_readEnv_ofEnv_placedBudget` to
`S := cliRunSemOverV4 X W` and `needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)`. -/
theorem h7f_decPkValidOverSlotOk_of_spqr [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {InitSpqrEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (sEnvs : RunSlotEnvs)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim ReadEnv)
    (hRead : ∀ (B' : RunBudgets),
      subroutine_ok
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
          (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B'.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hPathC : StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt A lim X mmpl gh W PromoteOverEnv
      P2OverErrEnv P2OverOkEnv)
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W InitSpqrEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hsEnv : ∀ g evs,
      DecPkD3ValidOverEnv A.repAlloc W X cliRunBudgets ReadEnv SessDeserializeCancelEnv
        P2OverErrEnv P2OverOkEnv tdEnv
        (fun B' F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1Envs A.repAlloc B' F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      sEnvs.decryptPrekey g evs) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemOverV4 X W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  decPkValidOverSlotOk_at_full_of_readEnv_ofEnv_placedBudget mmpl gh W X h547 hG hHooks.runHooks
    hRead hDeser hPathC hRaw hGrow hAesDec hSpqr hRecv_ne htd (cliRunSemOverV4 X W) sEnvs
    (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)) hsEnv rfl rfl (fun _ _ _ _ h => h) rfl

/-! ## 5. Parametric `MainOkOverD3F3` Bridges -/

/-- Parametric `MainOkOverD3F3` bridge over arbitrary `ReadEnv`, `sEnvsOf`, `PksmEnv`,
`MainEntryBudgetFitsCapOf`, and the four `slotsOfSigPkFrozenPlaced` slot contracts. -/
theorem h7f_overD3_assembly_of_sEnvs_pksm_fitsCap
    {mpl mmpl : MultiPlacement} {imgBytes : List (BitVec 8)}
    (hLs : libsignalSessionLib.LinkedAt imgBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (sEnvsOf : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (PksmEnv : PksmGhost → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv)
    (hinit_addr : ∀ X W γ tp gc d2 fsp,
      (sEnvsOf X W γ tp).initiate (r1cInitGhost gc d2 fsp) =
        (sEnvsOf X W γ tp).initiate (r1cInitGhost gc d2 0#64))
    (henc_addr : ∀ X W γ tp gc peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      (sEnvsOf X W γ tp).encrypt (r2EncGhost gc peerG meG fsp) =
        (sEnvsOf X W γ tp).encrypt (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ X W γ tp gc fsp w peerV meG msgG m,
      (sEnvsOf X W γ tp).decryptSignal (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        (sEnvsOf X W γ tp).decryptSignal (r3aDecSigGhost0 gc peerV meG m))
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmEnv x = PksmEnv y)
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      (sEnvsOf X W γ tp).decryptPrekey x = (sEnvsOf X W γ tp).decryptPrekey y)
    (hpksm : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        PksmSlotOkPlacedAt (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits PksmEnv)
    (hEnc : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf X W γ tp) (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hDecSig : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf X W γ tp) (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hInit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf X W γ tp) (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).initiate.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hDecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf X W γ tp) (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) (sEnvsOf X W γ tp) PksmEnv
            (cliRunSemOverV4 X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :
    MainOkOverD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk := by
  refine mainOkOverD3F3_of_mainSubroutine fun h547 X W => ?_
  letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
  exact mainSubroutineD3F3_of_domScopedRunTight hblk hext_nodup ghFixed
    (@instLsCodeInvFrozen (libsignalPlacementOf mpl hblk hext_nodup))
    (CliPqOrD3RecvDom ⟨W.C, W.Q⟩) (cliRunSemOverV4 X W)
    hlibc hTr hG (hioOf W) hstk
    (hfitCap h547 X W)
    (fun γ tp =>
      h7f_hrun_overV4_sEnvs_pksm_frozen_placed mmpl ghFixed X W
        (hHooks W γ tp)
        (hinit_addr X W γ tp)
        (henc_addr X W γ tp)
        (hdec_ghost X W γ tp)
        hpksm_addr
        (hdp_ghost X W γ tp)
        (hpksm h547 W γ tp)
        (hEnc h547 X W γ tp)
        (hDecSig h547 X W γ tp)
        (hInit h547 X W γ tp)
        (hDecPk h547 X W γ tp))

/-- Specialization of `h7f_overD3_assembly_of_sEnvs_pksm_fitsCap` to `PksmTryFromEnv`, discharging
`hpksm_addr` and Block-`111` `PksmSlotOkPlacedAt` internally from `hG`. -/
theorem h7f_overD3_assembly_of_sEnvs_fitsCap
    {mpl mmpl : MultiPlacement} {imgBytes : List (BitVec 8)}
    (hLs : libsignalSessionLib.LinkedAt imgBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (sEnvsOf : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 → RunSlotEnvs)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv)
    (hinit_addr : ∀ X W γ tp gc d2 fsp,
      (sEnvsOf X W γ tp).initiate (r1cInitGhost gc d2 fsp) =
        (sEnvsOf X W γ tp).initiate (r1cInitGhost gc d2 0#64))
    (henc_addr : ∀ X W γ tp gc peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      (sEnvsOf X W γ tp).encrypt (r2EncGhost gc peerG meG fsp) =
        (sEnvsOf X W γ tp).encrypt (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ X W γ tp gc fsp w peerV meG msgG m,
      (sEnvsOf X W γ tp).decryptSignal (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        (sEnvsOf X W γ tp).decryptSignal (r3aDecSigGhost0 gc peerV meG m))
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      (sEnvsOf X W γ tp).decryptPrekey x = (sEnvsOf X W γ tp).decryptPrekey y)
    (hEnc : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf X W γ tp) (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hDecSig : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf X W γ tp) (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hInit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf X W γ tp) (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).initiate.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hDecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (sEnvsOf X W γ tp) (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv) (sEnvsOf X W γ tp) PksmTryFromEnv
            (cliRunSemOverV4 X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :
    MainOkOverD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h7f_overD3_assembly_of_sEnvs_pksm_fitsCap hLs hblk hext_nodup ghFixed sEnvsOf PksmTryFromEnv
    hlibc hTr hG hioOf hstk hHooks hinit_addr henc_addr hdec_ghost h7f_pksmTryFromEnv_congr
    hdp_ghost
    (fun _ W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact h7f_pksmSlotOk_pksmTryFromEnv mmpl ghFixed W (hG γ tp))
    hEnc hDecSig hInit hDecPk hfitCap

/-- Per-slot `DecPkSlotEnv`-parametric `MainOkOverD3F3` bridge from `CliInitSlotOkPlaced`,
`PksmSlotOkPlacedAt`, W1/W2/W4 `.OkPlaced` contracts, and `MainEntryBudgetFitsCapOf`. -/
theorem h7f_overD3_assembly_of_fitsCap
    {mpl mmpl : MultiPlacement} {imgBytes : List (BitVec 8)}
    (hLs : libsignalSessionLib.LinkedAt imgBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (EncSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      EncGhost → List AllocEvent → Prop)
    (DecSigSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecSigGhost → List AllocEvent → Prop)
    (InitSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      InitGhost → List AllocEvent → Prop)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (PksmEnv : PksmGhost → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv)
    (hinit_addr : ∀ X W γ tp gc (d2 : Init2Data) fsp,
      InitSlotEnv X W γ tp (r1cInitGhost gc d2 fsp) =
        InitSlotEnv X W γ tp (r1cInitGhost gc d2 0#64))
    (henc_addr : ∀ X W γ tp gc (peerV : AddrV) (peerG meG : AddrGhost) fsp,
      peerG.val = addrValOf peerV →
      EncSlotEnv X W γ tp (r2EncGhost gc peerG meG fsp) =
        EncSlotEnv X W γ tp (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ X W γ tp gc fsp w (peerV : AddrV) (meG : AddrGhost) msgG m,
      DecSigSlotEnv X W γ tp (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        DecSigSlotEnv X W γ tp (r3aDecSigGhost0 gc peerV meG m))
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmEnv x = PksmEnv y)
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      DecPkSlotEnv X W γ tp x = DecPkSlotEnv X W γ tp y)
    (hpksm : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        PksmSlotOkPlacedAt (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits PksmEnv)
    (hEnc : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          { encrypt := EncSlotEnv X W γ tp
            decryptSignal := DecSigSlotEnv X W γ tp
            initiate := InitSlotEnv X W γ tp
            decryptPrekey := DecPkSlotEnv X W γ tp }
          (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hDecSig : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          { encrypt := EncSlotEnv X W γ tp
            decryptSignal := DecSigSlotEnv X W γ tp
            initiate := InitSlotEnv X W γ tp
            decryptPrekey := DecPkSlotEnv X W γ tp }
          (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hInit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliInitSlotOkPlaced mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitSlotEnv X W γ tp) X W)
    (hDecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          { encrypt := EncSlotEnv X W γ tp
            decryptSignal := DecSigSlotEnv X W γ tp
            initiate := InitSlotEnv X W γ tp
            decryptPrekey := DecPkSlotEnv X W γ tp }
          (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
            { encrypt := EncSlotEnv X W γ tp
              decryptSignal := DecSigSlotEnv X W γ tp
              initiate := InitSlotEnv X W γ tp
              decryptPrekey := DecPkSlotEnv X W γ tp }
            PksmEnv
            (cliRunSemOverV4 X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :
    MainOkOverD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h7f_overD3_assembly_of_sEnvs_pksm_fitsCap hLs hblk hext_nodup ghFixed
    (fun X W γ tp =>
      { encrypt := EncSlotEnv X W γ tp
        decryptSignal := DecSigSlotEnv X W γ tp
        initiate := InitSlotEnv X W γ tp
        decryptPrekey := DecPkSlotEnv X W γ tp })
    PksmEnv hlibc hTr hG hioOf hstk hHooks
    hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost hpksm
    hEnc hDecSig
    (fun h547 X W γ tp => by
      letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
      exact hInit h547 X W γ tp (cliRunSemOverV4 X W)
        { encrypt := EncSlotEnv X W γ tp
          decryptSignal := DecSigSlotEnv X W γ tp
          initiate := InitSlotEnv X W γ tp
          decryptPrekey := DecPkSlotEnv X W γ tp }
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))
        rfl rfl rfl rfl rfl)
    hDecPk hfitCap

/-- End-to-end `MainOkOverD3F3` bridge composing `h7f_decPkValidOverSlotOk_of_spqr` with
`h7f_overD3_assembly_of_fitsCap`. -/
theorem h7f_overD3_assembly_of_spqr_and_fitsCap
    {mpl mmpl : MultiPlacement} {imgBytes : List (BitVec 8)}
    (hLs : libsignalSessionLib.LinkedAt imgBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {InitSpqrEnv : CliHooks → InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : CliHooks → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : CliHooks → SendCall → List AllocEvent → Prop}
    {tdEnv : GhostName → BitVec 64 → CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    (EncSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      EncGhost → List AllocEvent → Prop)
    (DecSigSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecSigGhost → List AllocEvent → Prop)
    (InitSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      InitGhost → List AllocEvent → Prop)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (PksmEnv : PksmGhost → List AllocEvent → Prop)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv ReadEnv)
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits ReadEnv)
    (hinit_addr : ∀ X W γ tp gc (d2 : Init2Data) fsp,
      InitSlotEnv X W γ tp (r1cInitGhost gc d2 fsp) =
        InitSlotEnv X W γ tp (r1cInitGhost gc d2 0#64))
    (henc_addr : ∀ X W γ tp gc (peerV : AddrV) (peerG meG : AddrGhost) fsp,
      peerG.val = addrValOf peerV →
      EncSlotEnv X W γ tp (r2EncGhost gc peerG meG fsp) =
        EncSlotEnv X W γ tp (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ X W γ tp gc fsp w (peerV : AddrV) (meG : AddrGhost) msgG m,
      DecSigSlotEnv X W γ tp (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
        DecSigSlotEnv X W γ tp (r3aDecSigGhost0 gc peerV meG m))
    (hpksm_addr : ∀ x y : PksmGhost, x.bytes = y.bytes → PksmEnv x = PksmEnv y)
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      DecPkSlotEnv X W γ tp x = DecPkSlotEnv X W γ tp y)
    (hpksm : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        PksmSlotOkPlacedAt (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits PksmEnv)
    (hEnc : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          { encrypt := EncSlotEnv X W γ tp
            decryptSignal := DecSigSlotEnv X W γ tp
            initiate := InitSlotEnv X W γ tp
            decryptPrekey := DecPkSlotEnv X W γ tp }
          (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).encrypt.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hDecSig : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          { encrypt := EncSlotEnv X W γ tp
            decryptSignal := DecSigSlotEnv X W γ tp
            initiate := InitSlotEnv X W γ tp
            decryptPrekey := DecPkSlotEnv X W γ tp }
          (cliRunSemOverV4 X W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptSignal.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hInit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliInitSlotOkPlaced mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (InitSlotEnv X W γ tp) X W)
    (hRead : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64) (B' : RunBudgets),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok
          (CryptoVerification.SignalSession.Cli.RunProofs.Poll.dpPollProgPlaced
            (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (lsρ lsReadFileSym)
          (readFileSpecPlaced cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits B'.readFile ReadEnv))
    (hDeser : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (mpl.base 46)
          (sessDeserializeSpecPlaced scopeKit
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            SessDeserializeCancelEnv))
    (hPathC : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
        StageP2PathCOverQpanCliD3FrozenAtPlacedBudgetStmt
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits X mmpl ghFixed W
          PromoteOverEnv (P2OverErrEnv X W γ tp) (P2OverOkEnv X W γ tp))
    (hRaw : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        EncodeRawPreallocPlacedOkX
          (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hGrow : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        subroutine_ok (lsProg_51 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
          (mpl.base 621)
          (withLsCl mpl
            (growOneVecU8BudgetSpec fineCostModel
              (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits)))
    (hAesDec : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookOk (aesDecHookMallocng mmpl W.C.D)
          (aesDecBudgetSpec W.C.D fineCostModel
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits))
    (hSpqr : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        SpqrV1PlacedSeamsOfEnv fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          mmpl ghFixed W
          (InitSpqrEnv W)
          (fun st msg => RecvBytesEnv W st.bytes msg.bytes)
          (SendEnv W))
    (hRecv_ne : ∀ (W : CliHooks) stBs msgBs, ∃ evs, RecvBytesEnv W stBs msgBs evs)
    (htd : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64) a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv (RecvBytesEnv W) FormatInnerEnv a evs →
      tdEnv γ tp W a evs)
    (hsEnv : ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) g evs,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      DecPkD3ValidOverEnv (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc W X
        cliRunBudgets ReadEnv SessDeserializeCancelEnv
        (P2OverErrEnv X W γ tp) (P2OverOkEnv X W γ tp) (tdEnv γ tp)
        (fun B' F0 peer pid kpkId spkId kbk =>
          cliPollStageP4Prev1Envs (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc
            B' F0 peer pid kpkId spkId kbk ReadEnv)
        g evs →
      DecPkSlotEnv X W γ tp g evs)
    (hfitCap : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo ReadEnv
          uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs ReadEnv)
            { encrypt := EncSlotEnv X W γ tp
              decryptSignal := DecSigSlotEnv X W γ tp
              initiate := InitSlotEnv X W γ tp
              decryptPrekey := DecPkSlotEnv X W γ tp }
            PksmEnv
            (cliRunSemOverV4 X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) :
    MainOkOverD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h7f_overD3_assembly_of_fitsCap hLs hblk hext_nodup ghFixed
    EncSlotEnv DecSigSlotEnv InitSlotEnv DecPkSlotEnv PksmEnv
    hlibc hTr hG hioOf hstk hHooks
    hinit_addr henc_addr hdec_ghost hpksm_addr hdp_ghost hpksm
    hEnc hDecSig hInit
    (fun h547 X W γ tp => by
      letI : LibsignalFullPlacement := h7f_libsignalFullPlacementOfLinkedAt mpl hLs hblk hext_nodup
      exact h7f_decPkValidOverSlotOk_of_spqr mmpl ghFixed W X
        { encrypt := EncSlotEnv X W γ tp
          decryptSignal := DecSigSlotEnv X W γ tp
          initiate := InitSlotEnv X W γ tp
          decryptPrekey := DecPkSlotEnv X W γ tp }
        h547 (hG γ tp) (hHooks W γ tp) (hRead h547 W γ tp) (hDeser h547 W γ tp)
        (hPathC h547 X W γ tp) (hRaw h547 W γ tp) (hGrow h547 W γ tp) (hAesDec h547 W γ tp)
        (hSpqr h547 W γ tp) (hRecv_ne W) (htd W γ tp) (hsEnv X W γ tp))
    hfitCap

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3AssemblyFresh
