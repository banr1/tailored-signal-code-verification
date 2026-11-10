/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget
public import LibsignalBinary.Proofs.Common.StringClonePlacedBudget
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.PeakBudget.CliF3MainOkBridge
public import LibsignalBinary.Proofs.PeakBudget.CliKitEnvFits
public import LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv
public import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueOverF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bCut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bPub
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import ProofLib.FsTrace
public import LibsignalBinary.Heap.IfaceBudgetBase
import LibsignalBinary.Heap.IfaceBudgetBaseBridges
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostAcp
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst
import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic
import LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfHole3W2IntAux
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
import LibsignalBinary.Proofs.SignalSession.CliIo.Sym
import ProofLib.Process
import ProofLib.Process.FastParse
import ProofLib.Process.FsLemmas
import ProofLib.SepLogic.WP.StepsProcess
import VerifiedLibraries.Musl.Proofs.MemOps
import VerifiedLibraries.Musl.Proofs.SyscallProof
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinG5A
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinKit
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinOverD3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinPathB
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinVm
meta import ProofLib
meta import ProofLib.ProgramReflection

/-!
# Concrete `cliElfBytes` Relocatable V2-OOM Assembly

**Checked by Lean.**

Instantiates `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` by assembling ELF parsing,
startup/static assumptions, `LibsignalFrozen` preservation (`hole_gap3_f3CodeOk_to_libsignalFrozen`),
the `hole2_ghFixed` ghost-hook witness (`F3CliElfGhostWitness`, `mallocngLib`, 9-block
`musl` syscalls, `signalSessionIoMultiLib`, and `<String as Clone>::clone`), SPQR seam
bridges, and the six `main`-level arm assemblies.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst

open Arm64 (GhostName HookSat Memory subroutine_ok)
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (bytesOfString)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalSpqrV1 (Message MlKem States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (VecArg extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliElfBytes cliElfImage cliElf_parse cliExternsPlaced
   cliProcessInputs libsignalSessionLib lsReadFileSym stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliMainStk cliResStack cliRunBudgets cliRunBudgets_placed cliRunNeeds cliWrOk
   inputOf instLsCodeInvFrozen mProgPlaced mainFrameSize parseArgs)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost PksmGhost RunSem runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget (SpqrSendCoinsExactEnv)
open LibsignalBinary.Proofs.PeakBudget.CliF3MainOkBridge
  (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFits
  (realCliMainBinaryKitEnvOfFixed_fitsEnv_cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliNoOomOfFitsEnv
  (mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed
  (mainEntryBudgetFitsCapOf_initD3ScopedRun_fixed mainEntryBudgetFitsCapOf_pqD3Recv_fixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (cliDecPkCanonSlotEnvExact')
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
  (hmx_runEnvExact_sub_runBinaryKitEnvOfSlot mkBinaryKitRealCalleeEnvsSlotOf
   realCliMainBinaryKitEnvOfSlot realCliRunBinaryKitEnvOfSlot)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (binaryKitRunSlotEnvsFixed mkBinaryKitRealCalleeEnvsFixed realCliDecPkBinaryWideSlotEnvFixed
   realCliInitBinarySlotEnvFixed realCliRunBinaryKitEnvOfFixed
   runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonSlice
   runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_canonOrFallback)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec (SpqrSendTightCapEnv)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RealTdEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnv DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
  (cliRunSemD3ValidMatch runSlotEnvsF3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
  (MainOkPathBD3F3 cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
  (MainOkOverD3F3 MainOkValidMatchD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
  (MainOkUntypedD3F3 cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MainOkCliF3PqB2NeedLocksPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (Block617TransferFixedHyp mainOkCliF3Pq_of_block617TransferFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.M24L4BEquiv
  (mainOkCliExtPqB2NeedLocksPlacedAt_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (MainInitSemF3 initD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (CliSpqrRecvTightLinkedEnv SpqrSendCoinsTightLinkedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeOk cliElf_f3B2NeedLocksAssumptions)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact
   cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinCanonPrime
  (canonOrFallbackRunEnvExact' hole3_gap2_hrun_canonSlice')
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_mkBinaryKitRealCalleeEnvsDecPk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main)

/-! ## `LibsignalFrozen` Bridge and Ghost-Hook Witness Carrier -/

set_option maxRecDepth 400000 in
private theorem hole1_f3CodeOk_to_libsignalFrozen
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {m : Memory}
    (hCO : F3CodeOk mpl mmpl m) :
    LibsignalFrozen mpl m := by
  obtain ⟨inputs, sLoad, hload, hkf_load⟩ := hCO.1.fromLoad
  have htok :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics.cliElf_tokenCellsPlacedAt_of_linkedAt
      hLs
  have hmap :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced.loadState_patchElfTokensPlacedAt
      CryptoVerification.SignalSession.cliElf_staticOk htok inputs
  rw [hmap] at hload
  cases hraw : cliElfImage.loadState inputs with
  | error _ =>
    rw [hraw] at hload
    cases hload
  | ok sRaw =>
    rw [hraw] at hload
    simp only [Except.map, Except.ok.injEq] at hload
    have hkf0 : sRaw.mem.KeepsFrozen sLoad.mem := by
      rw [← hload]
      exact
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics.keepsFrozen_cliTokenPatchPlacedAt
          CryptoVerification.SignalSession.cliElf_staticOk htok hraw
    exact CryptoVerification.libsignalFrozen_of_keepsFrozen
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics.cliElf_frozen_of_linkedAt
        hLs hraw)
      (hkf0.trans hkf_load)

/-- Proves `F3CodeOk mpl mmpl m → LibsignalFrozen mpl m` under `LinkedAt cliElfBytes mpl`. -/
theorem hole_gap3_f3CodeOk_to_libsignalFrozen
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {m : Memory}
    (hCO : F3CodeOk mpl mmpl m) :
    LibsignalFrozen mpl m := by
  exact hole1_f3CodeOk_to_libsignalFrozen hLs hCO

/-- `ghFixed`-parametric ghost-hook witness bundle on `cliElfBytes`. -/
structure F3CliElfGhostWitness (mpl mmpl : MultiPlacement) where
  ghFixed : CliGhostHooks
  hookStack : Nat
  hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
    (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i)
  hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup
  hPl_mng : mallocngLib.Placeable mmpl
  hMainStk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk
  hTrFrozen : Block617TransferFixedHyp mpl mmpl ghFixed
    (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk
  hGSpqr :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed
  hFs : CliGhostHooksFs ghFixed
  hReadSat : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))
  hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none))
  hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
      ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd)
  hHooksBundle : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd)

theorem F3CliElfGhostWitness.hG {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitness mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits w.ghFixed :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  fun γ tp => (w.hGSpqr γ tp).toCliGhostAllocHooks

abbrev hole2_hookStack : Nat := extHookStack

def hole2_keepSub (a : BitVec 64) : Bool :=
  decide (0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000)

theorem hole2_keepSub_eq_wp4Gen (a : BitVec 64) :
    hole2_keepSub a = Wp4LayoutGen.hole2_keepSub a := by
  unfold hole2_keepSub Wp4LayoutGen.hole2_keepSub
  simp only [decide_eq_decide]
  omega

def hole2_keep (a : BitVec 64) : Bool :=
  decide ((0x4686a0 ≤ a.toNat ∧ a.toNat < 0x468724) ∨ (0x469000 ≤ a.toNat ∧ a.toNat < 0x46f000))

def hole2_emptyProg : Arm64.Program :=
  Arm64.Program.ofSvc Arm64.Syscall.standard

noncomputable def hole2_str1Prog (mpl : MultiPlacement) : Arm64.Program where
  base := mpl.base 623
  code := (libsignalSessionLib.blockProgram mpl 623).code
  svc := Arm64.Syscall.standard

set_option linter.unusedVariables false in
noncomputable def hole2_strCloneProg (mpl : MultiPlacement) : Arm64.Program where
  base := 0#64
  code := []
  externs sym :=
    if sym == "memcpy" then some ProofLib.hookMemcpy
    else if sym == "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" then
      some Arm64.Rust.panicked
    else none
  stubs := []
  svc := Arm64.Syscall.standard

def hole2_ActiveStrCloneRun (mpl : MultiPlacement) (s0 : Arm64.State) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ExecFrozen s0.mem ∧
  hole2_keep (s0.readReg64 .lr) = false ∧
  (hole2_str1Prog mpl).CodeLoaded (ProofLib.stripExecOutside hole2_keep s0.mem) ∧
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg.CodeLoaded
    (ProofLib.stripExecOutside hole2_keep s0.mem) ∧
  ∃ sf : Arm64.State,
    Arm64.StepsUntil (hole2_strCloneProg mpl) (Arm64.SubroutineStop s0)
      (s0.setPC (mpl.base 623)) sf ∧
    Arm64.SubroutineStop s0 sf ∧
    sf.fs = s0.fs ∧
    Arm64.FsTraced CryptoVerification.SignalSession.Cli.RunGlue.IsFsC s0 sf ∧
    LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ExecFrozen sf.mem

open Classical in
noncomputable def hole2_strCloneGhostHook [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (s0 : Arm64.State) : Arm64.State :=
  if _ : LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.ActiveF3CallPre
      (fun γ tp => LibsignalBinary.Heap.RustStdAllocBudgetBridge.stringCloneNoOomSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) s0 then
    if hReal : hole2_ActiveStrCloneRun mpl s0 then
      Classical.choose hReal.2.2.2.2
    else
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.keepFsTrace
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3StringCloneFallback mmpl) s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

def hole2_targets (mpl : MultiPlacement) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.F3GhostEntryTargets where
  alloc := LibsignalBinary.Heap.Fine.f3RdlAddrs.alloc
  dealloc := LibsignalBinary.Heap.Fine.f3RdlAddrs.dealloc
  realloc := LibsignalBinary.Heap.Fine.f3RdlAddrs.realloc
  allocZeroed := LibsignalBinary.Heap.Fine.f3RdlAzAddr
  stringClone := mpl.base 623
  readFile := 0x4691b4#64
  readStdin := 0x469000#64

noncomputable def hole2_ghFixed [LibsignalPlacement] (mpl mmpl : MultiPlacement) : CliGhostHooks :=
  { (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3CliGhostHooksFixed
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      (hole2_targets mpl) mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack
      (some (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow mmpl))
      (some (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow mmpl)))
    with stringClone := some (hole2_strCloneGhostHook mpl mmpl) }

theorem hole2_hblk (mpl : MultiPlacement) (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i) := by
  obtain ⟨_, _, hpl, _⟩ := hLs
  intro _ hi _
  exact libsignalSessionLib.placeable_blockLib hi hpl

theorem hole2_hext_nodup (mpl : MultiPlacement) (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    (libsignalSessionExterns.map mpl.ρ).Nodup := by
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_externs_nodup_of_linkedAt hLs

/-- Proof-side allocator and IO hook-transfer premise stating that `main` satisfies
`b2MainSpecTightNeedLocksFineAt` when the five Rust global-allocator entry points,
`read_file`, and `read_stdin` execute their real ELF code rather than `hole2_ghFixed`. -/
def CliElfHole2Assumption : Prop :=
  ∀ (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
    mallocngLib.LinkedAt cliElfBytes mmpl →
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    Block617TransferFixedHyp mpl mmpl (hole2_ghFixed mpl mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk

theorem hole2_hPl_mng (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.Placeable mmpl := by
  obtain ⟨_, _, hpl, _⟩ := hMm
  exact hpl

theorem hole2_hMainStk :
    mainFrameSize + max (max extHookStack hole2_hookStack) cliResStack ≤ cliMainStk := by
  decide

theorem hole2_hTrFrozen
    (hA : CliElfHole2Assumption)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    Block617TransferFixedHyp mpl mmpl (hole2_ghFixed mpl mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  have _ := hF3Frozen
  exact hA mpl mmpl hLs hMm

private theorem hole2_mng_placeable (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.Placeable mmpl := by
  obtain ⟨_, _, hPl, _⟩ := hMm
  exact hPl

private theorem hole2_mng_inElf (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngLib.InElf LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3TrialElf mmpl := by
  obtain ⟨img, hparse, _, hIn⟩ := hMm
  cases LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3TrialElf_parse.symm.trans hparse
  exact hIn

private theorem hole2_toNat_add_ofNat_of_lt {b : BitVec 64} {k : Nat}
    (hlt : b.toNat + k < 18446744073709551616) :
    (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hk : k < 2 ^ 64 := by omega
  have hlt' : b.toNat + k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt']

private theorem hole2_keepSub_mallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ a : BitVec 64, (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keepSub a = true := by
  intro a hsome
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp [hf] at hsome
  | some k =>
    have hk : k < mallocngLib.blocks.length := ProofLib.findCodeBlock_lt hf
    have hin : Arm64.InRegion (mmpl.base k) (mallocngLib.blockPatched mmpl k).length a :=
      ProofLib.findCodeBlock_inRegion hf
    have hlen : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      unfold Arm64.Obj.MultiPlacedLib.blockPatched
      rw [mallocngLib.blockLib_text hk]
      exact Arm64.Obj.CodeBlock.length_patched_of_aligned _
        ((hole2_mng_placeable mmpl hMm).blocks_ok k hk).len_aligned
    rw [hlen] at hin
    obtain ⟨_, hhi64, hm_lo, hm_hi⟩ :=
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3CliElf_mallocng_code_bounds_of_inElf
        (hole2_mng_placeable mmpl hMm) (hole2_mng_inElf mmpl hMm) k hk
    have hk_off : (a - mmpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    have heq_a : mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hlo : 0x469000 ≤ LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3MngCodeLo := by
      decide
    have hhi : LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3MngCodeHi ≤ 0x46f000 := by
      decide
    have ht : (mmpl.base k + BitVec.ofNat 64 (a - mmpl.base k).toNat).toNat =
        (mmpl.base k).toNat + (a - mmpl.base k).toNat :=
      hole2_toNat_add_ofNat_of_lt (by omega)
    rw [heq_a] at ht
    unfold hole2_keepSub
    exact decide_eq_true ⟨by omega, by omega⟩

private theorem hole2_mng_fnAddr_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (name : String) :
    mallocngLib.fnAddr mmpl name =
      mallocngLib.fnAddr LibsignalBinary.Heap.Fine.f3MallocngMpl name := by
  unfold Arm64.Obj.MultiPlacedLib.fnAddr
  cases hlk : Arm64.Obj.lookupBlockSym name mallocngLib.blocks with
  | none =>
    exact (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3CliElf_mallocng_linkedAt_unique hMm).1
      0 (Nat.zero_lt_succ 23)
  | some p =>
    rcases p with ⟨i, off⟩
    dsimp only
    rw [(LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3CliElf_mallocng_linkedAt_unique hMm).1
      i (ProofLib.lookupBlockSym_lt hlk)]

private theorem hole2_mng_cAddrs_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    VerifiedLibraries.RustStd.mallocngPlacedCAddrs mmpl =
      VerifiedLibraries.RustStd.mallocngPlacedCAddrs LibsignalBinary.Heap.Fine.f3MallocngMpl := by
  unfold VerifiedLibraries.RustStd.mallocngPlacedCAddrs
  simp only [hole2_mng_fnAddr_eq mmpl hMm]

private theorem hole2_mng_progContainsMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg mmpl := by
  have hPl1 := hole2_mng_placeable mmpl hMm
  have hIn1 := hole2_mng_inElf mmpl hMm
  have hPl2 := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.mallocngLib_in_f3TrialElf.1
  have hIn2 := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.mallocngLib_in_f3TrialElf.2.1
  have hF3 := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3Trial_progContainsMallocng
  refine VerifiedLibraries.Mallocng.Proofs.ProgContainsMultiLib.of_noExterns hPl1
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
    (fun m hPm i hi => ?_)
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
  have hcl_f3 := hF3.codeLoaded m hPm i hi
  have hbase_i : mmpl.base i = LibsignalBinary.Heap.Fine.f3MallocngMpl.base i :=
    (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced.f3CliElf_mallocng_linkedAt_unique hMm).1 i hi
  have hbase_prog : (mallocngLib.blockProgram mmpl i).base =
      (mallocngLib.blockProgram LibsignalBinary.Heap.Fine.f3MallocngMpl i).base := hbase_i
  have hcode_mmpl : (mallocngLib.blockProgram mmpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mmpl i) := by
    simp [Arm64.Obj.MultiPlacedLib.blockProgram, Arm64.Obj.PlacedLib.program, mallocngLib.blockLib_text hi]
  have hcode_f3 : (mallocngLib.blockProgram LibsignalBinary.Heap.Fine.f3MallocngMpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement LibsignalBinary.Heap.Fine.f3MallocngMpl i) := by
    simp [Arm64.Obj.MultiPlacedLib.blockProgram, Arm64.Obj.PlacedLib.program, mallocngLib.blockLib_text hi]
  have hlen1 : (mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mmpl i)).length =
      mallocngLib.blocks[i].code.length :=
    Arm64.Obj.CodeBlock.length_patched_of_aligned _ (hPl1.blocks_ok i hi).len_aligned
  have hlen2 : (mallocngLib.blocks[i].patched
      (mallocngLib.blockPlacement LibsignalBinary.Heap.Fine.f3MallocngMpl i)).length =
      mallocngLib.blocks[i].code.length :=
    Arm64.Obj.CodeBlock.length_patched_of_aligned _ (hPl2.blocks_ok i hi).len_aligned
  have hcode_prog : (mallocngLib.blockProgram mmpl i).code =
      (mallocngLib.blockProgram LibsignalBinary.Heap.Fine.f3MallocngMpl i).code := by
    rw [hcode_mmpl, hcode_f3]
    refine List.ext_getElem (hlen1.trans hlen2.symm) (fun k hk1 hk2 => ?_)
    obtain ⟨p1, hc1, _⟩ := hIn1.blocks i hi k hk1
    obtain ⟨p2, hc2, _⟩ := hIn2.blocks i hi k hk2
    rw [hbase_i] at hc1
    have hsome := hc1.symm.trans hc2
    exact (Prod.mk.inj (Option.some.inj hsome)).2
  rw [Arm64.Program.codeLoaded_iff] at hcl_f3 ⊢
  rwa [hbase_prog, hcode_prog]

private theorem hole2_rdlEntries (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    LibsignalBinary.Heap.RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAddrs := by
  have hShims := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3Trial_seg5ShimBundle.rdlShims
  rw [← hole2_mng_cAddrs_eq mmpl hMm] at hShims
  exact LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget.fineHookRustCliAllocBudgetEntries
    (hole2_mng_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart hShims
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3Trial_allocMemcpyVm_ok

private theorem hole2_rustStdThunks_chk :
    VerifiedLibraries.RustStd.checkRustStdThunkCode
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3RxSegBase
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxWordTree
      LibsignalBinary.Heap.Fine.f3StubAddrs.toRustStd
      LibsignalBinary.Heap.Fine.f3RdlAddrs.toRustStd = true := by
  decide +kernel

private theorem hole2_rustStdThunks :
    VerifiedLibraries.RustStd.RustStdThunkCode
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3StubAddrs.toRustStd
      LibsignalBinary.Heap.Fine.f3RdlAddrs.toRustStd :=
  VerifiedLibraries.RustStd.rustStdThunkCode_of_wordTree
    LibsignalBinary.Heap.Fine.f3RxWordCount
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxWordTree_eq
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxWordTree_size
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_externs_none
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_overrides_none
    (by rw [LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_base]
        exact hole2_rustStdThunks_chk)

private theorem hole2_stubEntries (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    LibsignalBinary.Heap.RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3StubAddrs := by
  have hShims := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3Trial_seg5ShimBundle.rdlShims
  rw [← hole2_mng_cAddrs_eq mmpl hMm] at hShims
  exact LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget.fineHookRustCliAllocBudgetEntries_thunks
    (hole2_mng_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart
    hole2_rustStdThunks hShims
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3Trial_allocMemcpyVm_ok

private theorem hole2_rdlAllocZeroed_ok (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAzAddr
      (LibsignalBinary.Heap.rustCliAllocBudgetSpecBase fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits true) := by
  have hZero := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3Trial_seg5ShimBundle.allocZeroedInstrs
  rw [← hole2_mng_fnAddr_eq mmpl hMm "calloc", ← hole2_mng_cAddrs_eq mmpl hMm] at hZero
  exact LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget.fineHookRdlAllocZeroed_budget_placed_ok
    (hole2_mng_progContainsMallocng mmpl hMm) γ tp cliElfImage.brkStart
    LibsignalBinary.Heap.Fine.f3RdlAzAddr
    LibsignalBinary.Heap.Fine.f3StdLayout.memsetAddr cliBudgetLimits
    hZero LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3Trial_allocMemsetVm_ok

private theorem hole2_emptyProg_externAt (pc : BitVec 64) :
    hole2_emptyProg.externAt? pc = none := rfl

private theorem hole2_spqrAllocHooks [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostSpqrAllocHooks
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      cliBudgetLimits (hole2_ghFixed mpl mmpl) where
  alloc :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3AllocGhostHookFine_ok
      rfl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      (fun pc _ => hole2_emptyProg_externAt pc)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      (hole2_mng_placeable mmpl hMm) (hole2_keepSub_mallocng mmpl hMm) γ tp
      ((hole2_rdlEntries mmpl hMm γ tp).toPlaced.alloc cliBudgetLimits)
  dealloc :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3DeallocGhostHookFine_ok
      rfl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      (fun pc _ => hole2_emptyProg_externAt pc)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      (hole2_mng_placeable mmpl hMm) (hole2_keepSub_mallocng mmpl hMm) γ tp
      ((hole2_rdlEntries mmpl hMm γ tp).toPlaced.dealloc cliBudgetLimits)
  realloc :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReallocGhostHookFine_ok
      rfl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      (fun pc _ => hole2_emptyProg_externAt pc)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      (hole2_mng_placeable mmpl hMm) (hole2_keepSub_mallocng mmpl hMm) γ tp
      ((hole2_rdlEntries mmpl hMm γ tp).toPlaced.realloc cliBudgetLimits)
  alloc_fs :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3AllocGhostHookFine_fs
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAddrs.alloc mmpl cliElfImage.brkStart cliBudgetLimits
  dealloc_fs :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3DeallocGhostHookFine_fs
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAddrs.dealloc mmpl cliElfImage.brkStart cliBudgetLimits
  realloc_fs :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReallocGhostHookFine_fs
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAddrs.realloc mmpl cliElfImage.brkStart cliBudgetLimits
  alloc_fsT :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3AllocGhostHookFine_fsT
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAddrs.alloc mmpl cliElfImage.brkStart cliBudgetLimits
  dealloc_fsT :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3DeallocGhostHookFine_fsT
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAddrs.dealloc mmpl cliElfImage.brkStart cliBudgetLimits
  realloc_fsT :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReallocGhostHookFine_fsT
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAddrs.realloc mmpl cliElfImage.brkStart cliBudgetLimits
  shim_eq := rfl
  memset :=
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow_r1_allocWitness
      mmpl rfl
  memcpy :=
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow_r1_allocWitness
      mmpl rfl
  memcpy_exact := fun _ hf => by
    cases hf
    exact LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow_exact mmpl
  memset_acp := fun _ hf s => by
    cases hf
    exact LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostAcp.f3EmptyMemsetGhostHookNarrow_acp mmpl s
  allocZeroed :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3AllocZeroedGhostHookFine_ok
      rfl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      (fun pc _ => hole2_emptyProg_externAt pc)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      (hole2_mng_placeable mmpl hMm) (hole2_keepSub_mallocng mmpl hMm) γ tp
      (LibsignalBinary.Heap.subroutine_ok_rustCliAllocBudget_of_base
        (hole2_rdlAllocZeroed_ok mmpl hMm γ tp))
  allocZeroed_fs :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3AllocZeroedGhostHookFine_fs
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAzAddr mmpl cliElfImage.brkStart cliBudgetLimits
  allocZeroed_fsT :=
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3AllocZeroedGhostHookFine_fsT
      hole2_keepSub hole2_emptyProg
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
      LibsignalBinary.Heap.Fine.f3RdlAzAddr mmpl cliElfImage.brkStart cliBudgetLimits

theorem hole2_hGSpqr
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (hole2_ghFixed mpl mmpl) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun γ tp => hole2_spqrAllocHooks mpl mmpl hMm γ tp

theorem hole2_hG
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (γ : GhostName) (tp : BitVec 64),
      CliGhostAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (hole2_ghFixed mpl mmpl) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun γ tp => (hole2_hGSpqr mpl mmpl hLs hMm γ tp).toCliGhostAllocHooks

private theorem hfsr_strCloneGhostHook_fsT [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    Arm64.HookFsTraced CryptoVerification.SignalSession.Cli.RunGlue.IsFsC
      (hole2_strCloneGhostHook mpl mmpl) := by
  classical
  intro s0
  unfold hole2_strCloneGhostHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.1
    · exact LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.keepFsTrace_fsT _ s0
  · exact Arm64.FsTraced.of_eq rfl rfl

theorem hole2_hFs
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    CliGhostHooksFs (hole2_ghFixed mpl mmpl) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have _ := hMm
  refine
    { alloc_fsT :=
        LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3AllocGhostHookFine_fsT
          hole2_keepSub hole2_emptyProg
          LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
          LibsignalBinary.Heap.Fine.f3RdlAddrs.alloc mmpl cliElfImage.brkStart cliBudgetLimits
      dealloc_fsT :=
        LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3DeallocGhostHookFine_fsT
          hole2_keepSub hole2_emptyProg
          LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
          LibsignalBinary.Heap.Fine.f3RdlAddrs.dealloc mmpl cliElfImage.brkStart cliBudgetLimits
      realloc_fsT :=
        LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReallocGhostHookFine_fsT
          hole2_keepSub hole2_emptyProg
          LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
          LibsignalBinary.Heap.Fine.f3RdlAddrs.realloc mmpl cliElfImage.brkStart cliBudgetLimits
      allocZeroed_fsT :=
        LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3AllocZeroedGhostHookFine_fsT
          hole2_keepSub hole2_emptyProg
          LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
          LibsignalBinary.Heap.Fine.f3RdlAzAddr mmpl cliElfImage.brkStart cliBudgetLimits
      shim_fsT := CryptoVerification.SignalSession.Cli.RunGlue.hookNoop_fsT
      stringClone_fsT := ?_
      memset_fsT := ?_
      memcpy_fsT := ?_ }
  · intro f hf
    dsimp only [hole2_ghFixed] at hf
    injection hf with hfeq
    subst hfeq
    exact hfsr_strCloneGhostHook_fsT mpl mmpl
  · intro f hf
    dsimp only [hole2_ghFixed,
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3CliGhostHooksFixed] at hf
    injection hf with hfeq
    subst hfeq
    exact
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow_fsT mmpl
  · intro f hf
    dsimp only [hole2_ghFixed,
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3CliGhostHooksFixed] at hf
    injection hf with hfeq
    subst hfeq
    exact
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow_fsT mmpl

section Hole2Gap1BReadFile

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup SepProp
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMultiLib memcpySymWords)
open VerifiedLibraries.Musl (
  MuslSysPlacement ValidCPath
  muslBlk00_errno_location muslBlk01_syscall_ret muslBlk02_sccp
  muslBlk03_syscall_cp muslBlk04_aio_close muslBlk05_close
  muslBlk06_read muslBlk07_write muslBlk08_open
  muslBlk09_fstat muslBlk10_fstatat
  muslErrnoLocationSpec
  muslSysPC00 muslSysPC01 muslSysPC02 muslSysPC03 muslSysPC04
  muslSysPC05 muslSysPC06 muslSysPC08
  muslSysPl00 muslSysPl01 muslSysPl02 muslSysPl03 muslSysPl04
  muslSysPl05 muslSysPl06 muslSysPl08
  muslSysPC02_svc muslSysPC08_svc muslSysPlacedLib
  ofNat64_le_maxSyscallOk placed_program_rebase_self
  stdMemcpy_ok_of_hasWords sxtw64_truncate32
)
open CryptoVerification (signalSessionIoMultiLib)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession (PathOk blockingAncestor? lsReadFileSym pathComps)
open LibsignalBinary.Heap.Fine (f3NoShimV2Addr f3RdlAddrs f3RxWordCount f3StubAddrs)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec rustAllocShimVm_ret_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.AgreesOutsideReadHooks
  (hookSat_readFileSpecPlaced_mono_stk)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (f3ReadFileFixedGhostHookFine f3ReadFileFixedGhostHookFine_ok_placed readFileAnyBudgetCondSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (hookSat_readFile_of_hookOk)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst
  (cliIoReadFileAnyBudgetCond_ok_of_entries cliIoReadFileAnyBudgetCond_ok_of_entries_of_readsCodeLoaded
   fineHookPoolErrnoSplit)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
  (codeLoaded_of_checkProgSliceInWordTree progContainsMultiLib_of_wordTree)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  OpenatLocalExecSpec OpenatLocalOutcome
  dirReadErrno32 dirReadErrno32_cases dirReadErrno32_ne_eintr
  dirReadErrnoNat dirReadErrnoNat_bounds
  execOpenat_rdonly_cloexec_dir
  muslClose48LocalSpec muslOpenNoCreatCloexecLocalExecSpec muslReadDir32Spec
  step_svc_close_fd_local step_svc_read_dir
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (
  ancestorWalkErrno?_eq_of_pathOk classifyOpenRdonly
  classifyOpenRdonly_err_cases classifyOpenRdonly_ok_spec
  isEmpty_false_of_pathOk muslOpenRdonlyDetSpec
  normalizePath_ne_nil_of_pathOk trailingDir_false_of_pathOk
  validRelCPath_of_pathOk
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (muslReadFileOrStdio32Spec)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (ExternPreservesOracleSymtab)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoBlockNoExtern cliIoCloseSym cliIoErrnoLocationSym cliIoMemcpySym
  cliIoOpenSym cliIoReadFileSym cliIoReadSym cliIoResolve_eq_base
  cliIoRustAllocSym cliIoRustDeallocSym cliIoRustNoAllocShimSym cliIoRustReallocSym
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (
  f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_stubs
  f3TrialRxProg_svc f3TrialRxProg_symbols f3TrialRxWordTree_eq f3TrialRxWordTree_size
  f3Trial_seg5ShimBundle
)

private def hole2_rf_muslPadMpl : MultiPlacement :=
  Wp4LayoutGen.hole2_rf_muslPadMpl

private theorem hole2_rf_muslPad_placeable :
    muslSysPlacedLib.Placeable hole2_rf_muslPadMpl :=
  MultiPlacedLib.placeable_of_checkPlaceable (by rfl_kernel)

private local instance hole2_rf_instMuslSysPlacement : MuslSysPlacement where
  mpl := hole2_rf_muslPadMpl
  placeable := hole2_rf_muslPad_placeable

private def hole2_rf_muslSys9Lib : MultiPlacedLib where
  name := "musl_sys"
  blocks := [
    muslBlk00_errno_location, muslBlk01_syscall_ret, muslBlk02_sccp,
    muslBlk03_syscall_cp, muslBlk04_aio_close, muslBlk05_close,
    muslBlk06_read, muslBlk07_write, muslBlk08_open
  ]
  data := []
  exports := [
    "___errno_location", "__errno_location", "__syscall_ret", "__syscall_cp",
    "__aio_close", "close", "read", "write", "open"
  ]

set_option maxRecDepth 400000 in
private theorem hole2_rf_musl9_placeable :
    hole2_rf_muslSys9Lib.Placeable hole2_rf_muslPadMpl :=
  MultiPlacedLib.placeable_of_checkPlaceable (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem hole2_rf_musl9_contains :
    ProgContainsMultiLib hole2_rf_muslSys9Lib f3TrialRxProg hole2_rf_muslPadMpl :=
  progContainsMultiLib_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    hole2_rf_musl9_placeable f3TrialRxProg_svc f3TrialRxProg_no_ext
    (by rw [f3TrialRxProg_base]; rfl_kernel)

private theorem hole2_rf_subroutine_ok_of_noExt {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {j : Nat} {entry : BitVec 64} {spec : Spec α}
    (hj : j < lib.blocks.length)
    (hcall : subroutine_ok (lib.blockProgram mpl j) entry (lib.withCodeLoaded mpl spec))
    (hcl : ∀ m, P.CodeLoaded m → lib.CodeLoaded mpl m)
    (hext : ∀ pc, P.externAt? pc = none)
    (hsvc : P.svc = Syscall.standard) :
    subroutine_ok P entry spec := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hcode
  have hpre_cl : s0.mem ⊨ (lib.withCodeLoaded mpl spec).pre x s0 ∗ R := by
    show s0.mem ⊨ (spec.pre x s0 ∗ ⌜lib.CodeLoaded mpl s0.mem⌝) ∗ R
    rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true (hcl s0.mem hcode)]
    exact hpre
  exact (lib.subroutine_ok_of_block hj hcall hext hsvc).mono_outcome
    x R s0 hpc hrun hpre_cl hsp (fun _ h => h)

private theorem hole2_rf_lookupAux_append {sym : String} :
    ∀ (idx : Nat) (xs ys : List CodeBlock),
      lookupBlockSymAux sym idx (xs ++ ys) =
        match lookupBlockSymAux sym idx xs with
        | some r => some r
        | none => lookupBlockSymAux sym (idx + xs.length) ys
  | _, [], _ => rfl
  | idx, b :: xs, ys => by
    simp only [List.cons_append, lookupBlockSymAux, List.length_cons]
    cases lookup sym b.symbols with
    | some _ => rfl
    | none =>
      rw [hole2_rf_lookupAux_append (idx + 1) xs ys]
      have h : idx + 1 + xs.length = idx + (xs.length + 1) := by omega
      rw [h]

private theorem hole2_rf_musl9_resolve_eq :
    hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl =
      muslSysPlacedLib.resolve MuslSysPlacement.mpl := by
  funext sym
  change (match lookupBlockSymAux sym 0 hole2_rf_muslSys9Lib.blocks with
          | some (i, off) => hole2_rf_muslPadMpl.base i + BitVec.ofNat 64 off
          | none => hole2_rf_muslPadMpl.ρ sym) =
         (match lookupBlockSymAux sym 0 (hole2_rf_muslSys9Lib.blocks ++ [muslBlk09_fstat, muslBlk10_fstatat]) with
          | some (i, off) => hole2_rf_muslPadMpl.base i + BitVec.ofNat 64 off
          | none => hole2_rf_muslPadMpl.ρ sym)
  rw [hole2_rf_lookupAux_append]
  cases lookupBlockSymAux sym 0 hole2_rf_muslSys9Lib.blocks with
  | some _ => rfl
  | none =>
    by_cases h1 : sym = "fstat"
    · subst h1; rfl_kernel
    · by_cases h2 : sym = "fstatat"
      · subst h2; rfl_kernel
      · change hole2_rf_muslPadMpl.ρ sym =
          match lookupBlockSymAux sym 9 [muslBlk09_fstat, muslBlk10_fstatat] with
          | some (i, off) => hole2_rf_muslPadMpl.base i + BitVec.ofNat 64 off
          | none => hole2_rf_muslPadMpl.ρ sym
        simp only [lookupBlockSymAux, muslBlk09_fstat, muslBlk10_fstatat, lookup,
          List.find?, Option.map, beq_false_of_ne (Ne.symm h1), beq_false_of_ne (Ne.symm h2)]

private theorem hole2_rf_placed_program_eq_of_text_pl {l1 l2 : PlacedLib} {p1 p2 : Placement}
    (ht : l1.text = l2.text) (hp : p1 = p2) :
    l1.program p1 = (l2.program p2).rebase p2.base (fun _ => none) := by
  rw [placed_program_rebase_self]
  unfold PlacedLib.program
  rw [ht, hp]

private theorem hole2_rf_musl9_pl_eq (i : Nat) :
    hole2_rf_muslSys9Lib.blockPlacement hole2_rf_muslPadMpl i =
      muslSysPlacedLib.blockPlacement MuslSysPlacement.mpl i := by
  show ({ base := hole2_rf_muslPadMpl.base i, ρ := hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl,
          relax := hole2_rf_muslPadMpl.relax i, b2b := hole2_rf_muslPadMpl.b2b i,
          undefWeak := hole2_rf_muslPadMpl.undefWeak } : Placement) =
       { base := hole2_rf_muslPadMpl.base i, ρ := muslSysPlacedLib.resolve MuslSysPlacement.mpl,
         relax := hole2_rf_muslPadMpl.relax i, b2b := hole2_rf_muslPadMpl.b2b i,
         undefWeak := hole2_rf_muslPadMpl.undefWeak }
  rw [hole2_rf_musl9_resolve_eq]

private theorem hole2_rf_musl9_prog_eq_0 :
    hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 0 =
      muslSysPC00.rebase muslSysPl00.base (fun _ => none) :=
  hole2_rf_placed_program_eq_of_text_pl rfl (hole2_rf_musl9_pl_eq 0)

private theorem hole2_rf_musl9_prog_eq_1 :
    hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 1 =
      muslSysPC01.rebase muslSysPl01.base (fun _ => none) :=
  hole2_rf_placed_program_eq_of_text_pl rfl (hole2_rf_musl9_pl_eq 1)

private theorem hole2_rf_musl9_prog_eq_2 :
    hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 2 =
      muslSysPC02.rebase muslSysPl02.base (fun _ => none) :=
  hole2_rf_placed_program_eq_of_text_pl rfl (hole2_rf_musl9_pl_eq 2)

private theorem hole2_rf_musl9_prog_eq_3 :
    hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 3 =
      muslSysPC03.rebase muslSysPl03.base (fun _ => none) :=
  hole2_rf_placed_program_eq_of_text_pl rfl (hole2_rf_musl9_pl_eq 3)

private theorem hole2_rf_musl9_prog_eq_4 :
    hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 4 =
      muslSysPC04.rebase muslSysPl04.base (fun _ => none) :=
  hole2_rf_placed_program_eq_of_text_pl rfl (hole2_rf_musl9_pl_eq 4)

private theorem hole2_rf_musl9_prog_eq_5 :
    hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 5 =
      muslSysPC05.rebase muslSysPl05.base (fun _ => none) :=
  hole2_rf_placed_program_eq_of_text_pl rfl (hole2_rf_musl9_pl_eq 5)

private theorem hole2_rf_musl9_prog_eq_6 :
    hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 6 =
      muslSysPC06.rebase muslSysPl06.base (fun _ => none) :=
  hole2_rf_placed_program_eq_of_text_pl rfl (hole2_rf_musl9_pl_eq 6)

private theorem hole2_rf_musl9_prog_eq_8 :
    hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 8 =
      muslSysPC08.rebase muslSysPl08.base (fun _ => none) :=
  hole2_rf_placed_program_eq_of_text_pl rfl (hole2_rf_musl9_pl_eq 8)

@[local simp] private theorem hole2_rf_muslSysPlacement_mpl_eq :
    MuslSysPlacement.mpl = hole2_rf_muslPadMpl := rfl
@[local simp] private theorem hole2_rf_lookup_musl_errno :
    lookupBlockSymAux "___errno_location" 0 muslSysPlacedLib.blocks = some (0, 0) := by decide
@[local simp] private theorem hole2_rf_lookup_musl_syscall_ret :
    lookupBlockSymAux "__syscall_ret" 0 muslSysPlacedLib.blocks = some (1, 0) := by decide
@[local simp] private theorem hole2_rf_lookup_musl_syscall_cp :
    lookupBlockSymAux "__syscall_cp" 0 muslSysPlacedLib.blocks = some (3, 0) := by decide
@[local simp] private theorem hole2_rf_lookup_musl_aio_close :
    lookupBlockSymAux "__aio_close" 0 muslSysPlacedLib.blocks = some (4, 0) := by decide

@[local simp] private theorem hole2_rf_muslErrnoAddr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    muslErrnoAddr (s.writeReg64 r v) = muslErrnoAddr s := rfl
@[local simp] private theorem hole2_rf_muslErrnoAddr_setPC (s : State) (pc : BitVec 64) :
    muslErrnoAddr (s.setPC pc) = muslErrnoAddr s := rfl
@[local simp] private theorem hole2_rf_muslErrnoAddr_setMem (s : State) (m : Memory) :
    muslErrnoAddr (s.setMem m) = muslErrnoAddr s := rfl
@[local simp] private theorem hole2_rf_muslErrnoAddr_setPState (s : State) (ps : PState) :
    muslErrnoAddr (s.setPState ps) = muslErrnoAddr s := rfl

private theorem hole2_rf_muslErrnoLocation_block_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 0)
      (hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "___errno_location")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl muslErrnoLocationSpec) := by
  rw [hole2_rf_musl9_prog_eq_0]
  have hentry : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "___errno_location" = muslSysPl00.base := by
    decide
  rw [hentry]; wp_entry; wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp [wp_norm, arm64_norm, muslErrnoAddr], rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩

private theorem hole2_rf_muslErrnoLocation2_ok :
    subroutine_ok f3TrialRxProg 0x46ba94#64 muslErrnoLocationSpec := by
  have haddr : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "___errno_location" = 0x46ba94#64 := by
    decide
  rw [← haddr]
  exact hole2_rf_subroutine_ok_of_noExt (j := 0) (by decide) hole2_rf_muslErrnoLocation_block_ok
    hole2_rf_musl9_contains.codeLoaded f3TrialRxProg_no_ext f3TrialRxProg_svc

private theorem hole2_rf_condHI_adds_4096_false {a : BitVec 64} (ha : a.toNat ≤ 2 ^ 64 - 4096) :
    ConditionHolds .HI (addsPState64 a 4096#64) = false := by
  rw [conditionHolds_hi_addsPState64]
  by_cases heq : a = -4096#64
  · subst heq; decide
  · have hlt_strict : a.toNat < 2 ^ 64 - 4096 := by
      refine Nat.lt_of_le_of_ne ha fun h => heq (BitVec.eq_of_toNat_eq ?_)
      have : (-4096#64 : BitVec 64).toNat = 2 ^ 64 - 4096 := by decide
      omega
    have hadd : (a + 4096#64).toNat = a.toNat + 4096 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : 4096 % 2 ^ 64 = 4096 := by decide
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have hult : BitVec.ult (a + 4096#64) a = false := by
      simp only [BitVec.ult, hadd, decide_eq_false_iff_not]; omega
    rw [hult, Bool.false_and]

private theorem hole2_rf_condHI_adds_4096_true {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ConditionHolds .HI (addsPState64 (-BitVec.ofNat 64 err) 4096#64) = true := by
  rw [conditionHolds_hi_addsPState64]
  have herr_mod : err % 2 ^ 64 = err := Nat.mod_eq_of_lt (by omega)
  have h4096_mod : 4096 % 2 ^ 64 = 4096 := by decide
  have hneg : (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, herr_mod, Nat.mod_eq_of_lt (by omega)]
  have hsum : (-BitVec.ofNat 64 err + 4096#64).toNat = 4096 - err := by
    rw [BitVec.toNat_add, hneg, BitVec.toNat_ofNat, h4096_mod]
    have : 2 ^ 64 - err + 4096 = 2 ^ 64 + (4096 - err) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hult : BitVec.ult (-BitVec.ofNat 64 err + 4096#64) (-BitVec.ofNat 64 err) = true := by
    simp only [BitVec.ult, hneg, hsum, decide_eq_true_eq]; omega
  have hne : (-BitVec.ofNat 64 err + 4096#64 != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [hsum, BitVec.toNat_ofNat] at this
    omega
  rw [hult, hne]; rfl

private theorem hole2_rf_neg_truncate32_neg_ofNat (err : Nat) :
    0#32 - (-BitVec.ofNat 64 err).truncate 32 = BitVec.ofNat 32 err := by bv_omega

private def hole2_rf_muslSyscallRetOkSpec : Spec (BitVec 64) where
  pre := fun r s0 =>
    ⌜s0.readReg64 .x0 = r ∧ r.toNat ≤ 2 ^ 64 - 4096⌝ ∗ stackAt s0.sp 32
  post := fun r s0 sf =>
    ⌜sf.readReg64 .x0 = r ∧ StdStatePreserved s0 sf⌝ ∗ stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_rf_muslSyscallRetOk_block_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 1)
      (hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "__syscall_ret")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl hole2_rf_muslSyscallRetOkSpec) := by
  rw [hole2_rf_musl9_prog_eq_1]
  have hentry : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "__syscall_ret" = muslSysPl01.base := by
    decide
  rw [hentry]; wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepConj_assoc]; repeat (apply SepWP.exists_left; intro)
  wp_stp64_perm hm1; wp_sym_steps 2; wp_str64_perm hm2; wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = false := hole2_rf_condHI_adds_4096_false ‹_›
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp_all [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm, hm2, hm1]⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [wp_norm, arm64_norm]

private def hole2_rf_muslSyscallRetErrSpec : Spec (Nat × BitVec 32) where
  pre := fun (err, e0) s0 =>
    ⌜s0.readReg64 .x0 = -BitVec.ofNat 64 err ∧ 1 ≤ err ∧ err ≤ 4095⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (err, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -1#64 ∧ StdStatePreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 err))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_rf_muslSyscallRetErr_block_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 1)
      (hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "__syscall_ret")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl hole2_rf_muslSyscallRetErrSpec) := by
  rw [hole2_rf_musl9_prog_eq_1]
  have hentry : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "__syscall_ret" = muslSysPl01.base := by
    decide
  rw [hentry]; wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps 2; wp_str64_perm hm2; wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = true := hole2_rf_condHI_adds_4096_true ‹_› ‹_›
  simp only [hcond, ↓reduceIte]; wp_sym_steps
  wp_call_block hole2_rf_muslErrnoLocation_block_ok ()
  rcases ‹StdStatePreserved _ sf› with ⟨hbrk_sf, hfs_sf, htpidr_sf, htr_sf, hoidx_sf, horacle_sf, hphys_sf, _⟩
  simp only [wp_norm, arm64_norm] at hbrk_sf hfs_sf htpidr_sf htr_sf hoidx_sf horacle_sf hphys_sf
  simp only [muslErrnoAddr] at *; wp_sym_steps 3; wp_str32_perm hm3; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, ‹sf.status = .Running›])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, hbrk_sf.symm],
      by simp [wp_norm, arm64_norm, hfs_sf.symm], by simp [wp_norm, arm64_norm, htpidr_sf.symm],
      by simp [wp_norm, arm64_norm, htr_sf.symm], by simp [wp_norm, arm64_norm, hoidx_sf.symm],
      by simp [wp_norm, arm64_norm, horacle_sf.symm], by simp [wp_norm, arm64_norm, hphys_sf.symm],
      fun _ => by simp [wp_norm, arm64_norm, hm3, ‹sf.mem = _›, hm2, hm1]⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm, htpidr_sf.symm, hole2_rf_neg_truncate32_neg_ofNat]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem hole2_rf_muslSyscallCp_step {s0 : State} {target_pc : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s0.pc = muslSysPl03.base) (hrun : s0.status = .Running)
    (hcl : hole2_rf_muslSys9Lib.CodeLoaded hole2_rf_muslPadMpl s0.mem)
    (hnext : SepWP (muslSysPC02.rebase muslSysPl02.base (fun _ => none)) target_pc
      ((((((((s0.writeReg64 .x8 (s0.readReg64 .x0)).writeReg64 .x0 (s0.readReg64 .x1)).writeReg64
        .x1 (s0.readReg64 .x2)).writeReg64 .x2 (s0.readReg64 .x3)).writeReg64
        .x3 (s0.readReg64 .x4)).writeReg64 .x4 (s0.readReg64 .x5)).writeReg64
        .x5 (s0.readReg64 .x6)).setPC (muslSysPl02.base + 28#64)) P post) :
    SepWP (muslSysPC03.rebase muslSysPl03.base (fun _ => none)) target_pc s0 P post := by
  wp_sym_steps
  have hsccp : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl02.base := by
    decide
  rw [hsccp]
  have hcl2 : (muslSysPC02.rebase muslSysPl02.base (fun _ => none)).CodeLoaded s0.mem := by
    simpa [hole2_rf_musl9_prog_eq_2] using hcl 2 (by decide)
  refine SepWP.of_sameHooks (P := muslSysPC03.rebase muslSysPl03.base (fun _ => none))
    (Q := muslSysPC02.rebase muslSysPl02.base (fun _ => none))
    (by intro pc
        change ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 2).rebase muslSysPl02.base (fun _ => none)).externAt? pc =
          ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3).rebase muslSysPl03.base (fun _ => none)).externAt? pc
        simp)
    rfl hcl2 ?_
  wp_sym_steps
  simpa [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8] using hnext

private theorem hole2_rf_resolve_syscall_cp :
    hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl "__syscall_cp" = muslSysPl03.base := by
  decide

private def hole2_rf_muslAioCloseSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = s0.readReg64 .x0 ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_rf_muslAioClose_blk_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 4)
      (hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl "__aio_close")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl hole2_rf_muslAioCloseSpec) := by
  rw [hole2_rf_musl9_prog_eq_4]
  have hentry : hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl "__aio_close" = muslSysPl04.base := by
    decide
  rw [hentry]; wp_entry; wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    by simpa using hmem⟩

private def hole2_rf_muslSccpCloseLocalSpec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜s0.readReg64 .x0 = 57#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind = .localFile ∨ desc.kind = .localDir)⌝
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs.setFd fd none ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_rf_muslSccpCloseLocal_blk_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 3)
      (hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl "__syscall_cp")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl hole2_rf_muslSccpCloseLocalSpec) := by
  rw [hole2_rf_musl9_prog_eq_3, hole2_rf_resolve_syscall_cp]; wp_entry
  refine hole2_rf_muslSyscallCp_step hpc hrun h ?_
  refine step_svc_close_fd_local (fd := a_1) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem hole2_rf_muslClose48Local_block_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 5)
      (hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "close")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl muslClose48LocalSpec) := by
  rw [hole2_rf_musl9_prog_eq_5]
  have hentry : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "close" = muslSysPl05.base := by decide
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 32 2 (by decide)]
  cells_unfold; simp only [sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep hole2_rf_muslAioClose_blk_ok ()
  rcases ‹StdStatePreserved _ _› with ⟨hfs1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at hfs1 htr1 htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block_keep hole2_rf_muslSccpCloseLocal_blk_ok (a_1, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at htp2 hsig2 hb2 hbs2 hp2 hmp2
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block hole2_rf_muslSyscallRetOk_block_ok 0#64
  rcases ‹StdStatePreserved _ _› with ⟨hfs3, htr3, htp3, hsig3, hb3, hbs3, hp3, hmp3⟩
  simp only [wp_norm, arm64_norm, htp2, hsig2, hb2, hbs2, hp2, hmp2] at hfs3 htr3 htp3 hsig3 hb3 hbs3 hp3 hmp3
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
      by simp [wp_norm, arm64_norm, *], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
        stackAt_split_cells s0.sp 32 2 (by decide)]
      cells_unfold; simp only [wp_norm, arm64_norm, *]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem hole2_rf_muslClose48Local_ok :
    subroutine_ok f3TrialRxProg 0x46e1fc#64 muslClose48LocalSpec := by
  have haddr : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "close" = 0x46e1fc#64 := by decide
  rw [← haddr]
  exact hole2_rf_subroutine_ok_of_noExt (j := 5) (by decide) hole2_rf_muslClose48Local_block_ok
    hole2_rf_musl9_contains.codeLoaded f3TrialRxProg_no_ext f3TrialRxProg_svc

private def hole2_rf_muslSccpReadDirSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry) where
  pre := fun (fd, buf, count, desc) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      s0.fs.fds fd = some desc ∧
      desc.kind = .localDir ∧
      desc.accMode.canRead = true⌝
  post := fun (_, buf, count, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 (dirReadErrnoNat buf count) ∧
      sf.fs = s0.fs ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_rf_muslSccpReadDir_blk_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 3)
      (hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl "__syscall_cp")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl hole2_rf_muslSccpReadDirSpec) := by
  rw [hole2_rf_musl9_prog_eq_3, hole2_rf_resolve_syscall_cp]; wp_entry
  refine hole2_rf_muslSyscallCp_step hpc hrun h ?_
  refine step_svc_read_dir (fd := a_1) (buf := a) (count := a_2) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4
    (by simp [wp_norm, arm64_norm, h_5]) (by simp [wp_norm, arm64_norm, h_6])
    h_7 h_8 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem hole2_rf_muslReadDir32_block_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 6)
      (hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "read")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl muslReadDir32Spec) := by
  rw [hole2_rf_musl9_prog_eq_6]
  have hentry : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "read" = muslSysPl06.base := by decide
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep hole2_rf_muslSccpReadDir_blk_ok (a_1, a, a_2, a_3)
  rcases ‹SyscallPreserved _ sf› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
  wp_conv_pre => rw [htp_e]
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ a_rest_1))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have ⟨h1_err, h2_err⟩ := dirReadErrnoNat_bounds a a_2
  wp_call_block hole2_rf_muslSyscallRetErr_block_ok (dirReadErrnoNat a a_2, a_rest_1)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], dirReadErrno32_cases a a_2,
      dirReadErrno32_ne_eintr a a_2, by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [dirReadErrno32, muslErrnoAddr, wp_norm, arm64_norm, *] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem hole2_rf_muslReadDir32_ok :
    subroutine_ok f3TrialRxProg 0x46e240#64 muslReadDir32Spec := by
  have haddr : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "read" = 0x46e240#64 := by decide
  rw [← haddr]
  exact hole2_rf_subroutine_ok_of_noExt (j := 6) (by decide) hole2_rf_muslReadDir32_block_ok
    hole2_rf_musl9_contains.codeLoaded f3TrialRxProg_no_ext f3TrialRxProg_svc

private def hole2_rf_muslSccpReadFileOrStdioSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      (desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE) ∧
      oldBuf.length = count.toNat ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind == .localFile || desc.kind == .stdio) = true ∧
      desc.accMode.canRead = true⌝ ∗
    (buf ↦ₛ oldBuf)
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_rf_muslSccpReadFileOrStdio_blk_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 3)
      (hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl "__syscall_cp")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl hole2_rf_muslSccpReadFileOrStdioSpec) := by
  rw [hole2_rf_musl9_prog_eq_3, hole2_rf_resolve_syscall_cp]; wp_entry
  refine hole2_rf_muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine SepWP.step_svc_read (fd := a_1) (buf := a) (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x0 = 63#64›])
    (by simpa [wp_norm, arm64_norm] using ‹(s0.readReg32 .x1).zeroExtend 64 = a_1›)
    ‹a_1.toNat < 2 ^ 31›
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x2 = a›])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x3 = a_2›])
    ‹a_rest_1.length = a_2.toNat›
    ‹s0.fs.fds a_1 = some a_3›
    ‹(a_3.kind == .localFile || a_3.kind == .stdio) = true›
    ‹a_3.accMode.canRead = true› ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, ‹s0.readReg64 .x0 = 63#64›])
    ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    ‹a.toNat + a_2.toNat ≤ Arm64.USER_VA_LIMIT›
    ‹a_3.kind = .localFile → a_3.offset + a_2.toNat ≤ Arm64.MAX_LFS_FILESIZE›
  dsimp only; rw [sepConj_emp]
  (conv => arg 3; simp only [wp_norm, arm64_norm])
  (conv => arg 4; simp only [wp_norm, arm64_norm, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8])
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by cases a_3; simp_all [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm]⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem hole2_rf_muslReadFileOrStdio32_block_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 6)
      (hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "read")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl muslReadFileOrStdio32Spec) := by
  rw [hole2_rf_musl9_prog_eq_6]
  have hentry : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "read" = muslSysPl06.base := by decide
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded; wp_stp64_perm hm1; wp_sym_steps
  wp_call_block_keep hole2_rf_muslSccpReadFileOrStdio_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗
    (a ↦ₛ (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat ++
      a_rest_1.drop (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt : (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length < 2 ^ 63 := by
    simp only [List.length_take]
    have := ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    simp only [Arm64.MAX_RW_COUNT] at this
    omega
  have hchunk_ok := ofNat64_le_maxSyscallOk hchunk_lt
  wp_call_block hole2_rf_muslSyscallRetOk_block_ok
    (BitVec.ofNat 64 (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
    at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_, by simp [wp_norm, arm64_norm, *], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem hole2_rf_muslReadFileOrStdio32_ok :
    subroutine_ok f3TrialRxProg 0x46e240#64 muslReadFileOrStdio32Spec := by
  have haddr : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "read" = 0x46e240#64 := by decide
  rw [← haddr]
  exact hole2_rf_subroutine_ok_of_noExt (j := 6) (by decide) hole2_rf_muslReadFileOrStdio32_block_ok
    hole2_rf_musl9_contains.codeLoaded f3TrialRxProg_no_ext f3TrialRxProg_svc

private def hole2_rf_muslSccpOpenatLocalExecSpec :
    Spec (BitVec 64 × String × BitVec 32 × FsState × List TraceEvent × OpenatLocalOutcome) where
  pre := fun (cstr, path, flags, fs0, tr0, out) s0 =>
    ⌜s0.readReg64 .x0 = 56#64 ∧
      s0.readReg32 .x1 = AT_FDCWD_W32 ∧
      s0.readReg64 .x2 = cstr ∧
      s0.readReg32 .x3 = flags ||| O_LARGEFILE_W32 ∧
      s0.fs = fs0 ∧
      s0.trace = tr0 ∧
      ValidCPath path ∧
      OpenatLocalExecSpec fs0 tr0 path flags out⌝ ∗
    (cstr ↦ₛ cstrBytes path)
  post := fun (cstr, path, _, fs0, tr0, out) s0 sf =>
    match out with
    | .ok fd desc fs' traceExtra =>
      ⌜sf.readReg64 .x0 = fd ∧
        fd.toNat < 2 ^ 31 ∧
        fs'.fds fd = some desc ∧
        (desc.kind = .localFile ∨ desc.kind = .localDir) ∧
        desc.cloexec = true ∧
        sf.fs = fs' ∧
        sf.mem = s0.mem ∧
        sf.trace = tr0 ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (cstr ↦ₛ cstrBytes path)
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 errno ∧
          1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.fs = fs0 ∧
          sf.mem = s0.mem ∧
          sf.trace = tr0 ∧
          SyscallPreserved s0 sf⌝ ∗
        (cstr ↦ₛ cstrBytes path)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_rf_muslSccpOpenatLocalExec_blk_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 3)
      (hole2_rf_muslSys9Lib.resolve hole2_rf_muslPadMpl "__syscall_cp")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl hole2_rf_muslSccpOpenatLocalExecSpec) := by
  rw [hole2_rf_musl9_prog_eq_3, hole2_rf_resolve_syscall_cp]; wp_entry
  obtain ⟨hlen_p, hval_p⟩ := h_8
  refine hole2_rf_muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_openat_rw (path := a) (fname := a_1) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simp [wp_norm, arm64_norm, h_4])
    hlen_p hval_p (fun hcs => ?_)
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  rw [sepConj_emp]
  have hexec := h_1 hcs (by simp [wp_norm, arm64_norm, h_6]) (by simp [wp_norm, arm64_norm, h_7])
    (by simpa [wp_norm, arm64_norm] using h_3) (by simpa [wp_norm, arm64_norm] using h_5)
  cases a_rest with
  | ok fd desc fs' traceExtra =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨hfd_lt, hfds, hkind, hclo, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [hole2_rf_muslSccpOpenatLocalExecSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], hfd_lt, hfds, hkind, hclo,
        by simp [wp_norm, arm64_norm, State.appendTrace], rfl,
        by simp [wp_norm, arm64_norm, State.appendTrace, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [wp_norm, arm64_norm, State.appendTrace, calleeSavedVRegs]
  | err errPred =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨errno, h1, h2, hpred, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [hole2_rf_muslSccpOpenatLocalExecSpec]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], h1, h2, hpred,
        by simp [wp_norm, arm64_norm, h_6], rfl,
        by simp [wp_norm, arm64_norm, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem hole2_rf_truncate32_and64 (x y : BitVec 64) :
    (x &&& y).truncate 32 = x.truncate 32 &&& y.truncate 32 := by ext i hi; simp

private theorem hole2_rf_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    fd.getLsbD 31 = false := by
  rw [BitVec.getLsbD]; exact Nat.testBit_lt_two_pow hfd

private theorem hole2_rf_truncate32_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hole2_rf_getLsbD_31_false_of_lt hfd]; decide

private theorem hole2_rf_mask32_or_zero_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := by
  simp only [BitVec.ushiftRight_zero, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem hole2_rf_setWidth64_setWidth32_and_mask_of_lt31 {fd : BitVec 64}
    (hfd : fd.toNat < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
  rw [h1]
  simpa [BitVec.ushiftRight_zero, BitVec.or_zero] using hole2_rf_mask32_or_zero_of_lt31 hfd

private theorem hole2_rf_sxtw64_eq_self_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 |||
      (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = fd := by
  rw [hole2_rf_getLsbD_31_false_of_lt hfd]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem hole2_rf_neg_ofNat_toNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem hole2_rf_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).getLsbD 31 = true := by
  rw [BitVec.getLsbD, hole2_rf_neg_ofNat_toNat h1 h2, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 ^ 64 - err) / 2 ^ 31 = 2 ^ 33 - 1 := by omega
  rw [hdiv]; decide

private theorem hole2_rf_truncate32_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err).truncate 32).getLsbD 31 = true := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hole2_rf_getLsbD_31_neg_ofNat h1 h2]; decide

private theorem hole2_rf_sxtw_neg_of_hi_ones {v : BitVec 64} (h : v >>> 32 = 0xffffffff#64) :
    (v >>> 0 &&& 4294967295#64 ||| 0xffffffffffffffff#64 &&& 0xffffffff00000000#64) = v := by
  bv_robdd

private theorem hole2_rf_sxtw64_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err) >>> 0 &&& 4294967295#64 |||
      (if (-BitVec.ofNat 64 err).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = -BitVec.ofNat 64 err := by
  rw [hole2_rf_getLsbD_31_neg_ofNat h1 h2]
  simp only [↓reduceIte]
  refine hole2_rf_sxtw_neg_of_hi_ones (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ushiftRight, hole2_rf_neg_ofNat_toNat h1 h2, Nat.shiftRight_eq_div_pow]
  have hmax : (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  rw [hmax]; omega

private theorem hole2_rf_zeroExtend64_getLsbD_6 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 6 = flags.getLsbD 6 := by simp

private theorem hole2_rf_zeroExtend64_getLsbD_19 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 19 = flags.getLsbD 19 := by simp

private theorem hole2_rf_tmpfile_mask_eq_zero {flags : BitVec 32} (h : flags &&& 0x00404000#32 = 0#32) :
    (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = 0#32 := by
  have heq : (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = flags &&& 0x00404000#32 := by bv_bits
  rw [heq, h]

private theorem hole2_rf_or_largefile_sxtw_truncate32 (flags : BitVec 32) :
    (((flags.zeroExtend 64 ||| 131072#64) >>> 0 &&& 4294967295#64 |||
      (if (flags.zeroExtend 64 ||| 131072#64).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64).truncate 32) = flags ||| O_LARGEFILE_W32 := by
  rw [sxtw64_truncate32]
  change (flags.zeroExtend 64 ||| 131072#64).truncate 32 = flags ||| 0x00020000#32
  bv_bits

private theorem hole2_rf_FsState_setFd_eq_self {fs : FsState} {fd : BitVec 64} {d : Option FdEntry}
    (h : fs.fds fd = d) :
    fs.setFd fd d = fs := by
  cases fs with
  | mk entries stdin fds =>
    dsimp only at h
    simp only [FsState.setFd, FsState.mk.injEq, true_and]
    funext k
    by_cases hk : (k == fd) = true
    · rw [eq_of_beq hk]; simp [h]
    · simp [hk]

set_option maxHeartbeats 400000 in
private theorem hole2_rf_muslOpenNoCreatCloexecLocalExec_block_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 8)
      (hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "open")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl muslOpenNoCreatCloexecLocalExecSpec) := by
  rw [hole2_rf_musl9_prog_eq_8]
  have hentry : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "open" = muslSysPl08.base := by decide
  rw [hentry]; wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 112 = stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
      stackAt_split_cells s0.sp 32 10 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  wp_stp64_perm hm1; wp_sym_steps 1; wp_str64_perm hm2; wp_sym_steps 1; wp_str64_perm hm3
  (conv => arg 3; simp only [wp_norm, arm64_norm, h_3, hole2_rf_zeroExtend64_getLsbD_6, h_4])
  wp_sym_steps 3
  have htmp := hole2_rf_tmpfile_mask_eq_zero h_5
  (conv => arg 3; simp only [wp_norm, arm64_norm, hole2_rf_truncate32_and64, h_3, htmp])
  wp_sym_steps
  have hcwd : (-100#32 : BitVec 32) = AT_FDCWD_W32 := by decide
  have hflg := hole2_rf_or_largefile_sxtw_truncate32 a_2
  have ⟨_, _⟩ := ‹ValidCPath a›
  wp_call_block_keep hole2_rf_muslSccpOpenatLocalExec_blk_ok (a_1, a, a_2, s0.fs, s0.trace, a_rest_1)
  cases a_rest_1 with
  | ok fd desc fs' traceExtra =>
    wp_conv_pre => try dsimp only [hole2_rf_muslSccpOpenatLocalExecSpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0, hfd_lt, hfds, hkind, hclo, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsvc08 : muslSysPC08.svc = Syscall.standard := rfl
    have hsxtw : (fd >>> 0 &&& 4294967295#64 |||
        (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64) = fd := hole2_rf_sxtw64_eq_self_of_lt31 hfd_lt
    have hmask0 : (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := hole2_rf_mask32_or_zero_of_lt31 hfd_lt
    have hfd_ze_mask : BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd :=
      hole2_rf_setWidth64_setWidth32_and_mask_of_lt31 hfd_lt
    have hfd_ze : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
    have htbnz : fd.getLsbD 31 = false := hole2_rf_getLsbD_31_false_of_lt hfd_lt
    have htbnz32 : (fd.truncate 32).getLsbD 31 = false := hole2_rf_truncate32_getLsbD_31_false_of_lt hfd_lt
    wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32])
    wp_sym_steps 2
    simp only [wp_norm, arm64_norm, hole2_rf_zeroExtend64_getLsbD_19, h_6]
    have hdesc_eq : ({ desc with cloexec := true } : FdEntry) = desc := by
      cases desc; simp at hclo; subst hclo; rfl
    have hsetfd_eq : fs'.setFd fd (some { desc with cloexec := true }) = fs' := by
      rw [hdesc_eq]; exact hole2_rf_FsState_setFd_eq_self hfds
    have h1_clo : (1#64 &&& 1#64 != 0#64) = true := by decide
    wp_sym_steps
    refine step_svc_fcntl_setfd_local (fd := fd) (arg := 1#64) rfl
      (by simp [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hfd_ze]) hfd_lt
      (by simp [wp_norm, arm64_norm, F_SETFD_W32]) (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm, hfs1] using hfds) hkind ?_
      (by simp [wp_norm, arm64_norm, *])
    dsimp only
    (conv => arg 3; simp only [wp_norm, arm64_norm, hfs1, h1_clo, hsetfd_eq])
    wp_sym_steps
    have hfd_ok : fd.toNat ≤ 2 ^ 64 - 4096 := by omega
    wp_cut_codeLoaded
    wp_call_block hole2_rf_muslSyscallRetOk_block_ok fd
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp_all [wp_norm, arm64_norm],
        by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]
  | err errPred =>
    wp_conv_pre => try dsimp only [hole2_rf_muslSccpOpenatLocalExecSpec]; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro errno
    apply SepWP.pure_elim
    rintro ⟨hx0, h1, h2, hpred, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsxtw : ((-BitVec.ofNat 64 errno) >>> 0 &&& 4294967295#64 |||
        (if (-BitVec.ofNat 64 errno).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64) = -BitVec.ofNat 64 errno := hole2_rf_sxtw64_neg_ofNat h1 h2
    have htbnz : (-BitVec.ofNat 64 errno).getLsbD 31 = true := hole2_rf_getLsbD_31_neg_ofNat h1 h2
    have htbnz32 : ((-BitVec.ofNat 64 errno).truncate 32).getLsbD 31 = true :=
      hole2_rf_truncate32_getLsbD_31_neg_ofNat h1 h2
    have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
    wp_conv_pre => rw [htp_e]
    wp_cut_codeLoaded; wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, htbnz, htbnz32])
    wp_sym_steps
    wp_call_block hole2_rf_muslSyscallRetErr_block_ok (errno, a_3)
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨h1, h2, hpred, by simp [wp_norm, arm64_norm, *],
        by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *], ?_⟩,
        ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem hole2_rf_classifyOpenRdonly_err_of_none_some (fs : FsState) (path : String)
    (e : FsEntry) {errno : Nat}
    (hb : blockingAncestor? fs path = none)
    (hf : fs.files path = some e)
    (hcl : classifyOpenRdonly fs path = .err errno) :
    fs.allocFd = none ∧ errno = 24 := by
  unfold classifyOpenRdonly at hcl
  rw [hb, hf] at hcl
  cases e <;> (
    cases ha : fs.allocFd with
    | none => rw [ha] at hcl; injection hcl with he; exact ⟨rfl, he.symm⟩
    | some _ => rw [ha] at hcl; cases hcl)

private theorem hole2_rf_execOpenat_rdonly_cloexec_err_anc {s : State} {path : String}
    {err : BitVec 64}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = some err) :
    execOpenat s = (s.writeReg64 .x0 (-err)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  rw [ProofLib.ancestorWalkErrno_eq_strict] at hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_cr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres]
  cases hsanc : strictAncestorWalkErrno? s.fs path with
  | some e =>
    rw [hsanc] at hanc
    injection hanc with he; subst he; rfl
  | none =>
    rw [hsanc] at hanc
    cases hlast : ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
    | true =>
      rw [hlast] at hanc
      simp only [↓reduceIte, Option.some.injEq] at hanc
      subst hanc; rfl
    | false =>
      rw [hlast] at hanc; cases hanc

private theorem hole2_rf_execOpenat_rdonly_cloexec_missing {s : State} {path : String}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hnone : s.fs.files path = none) :
    execOpenat s = (s.writeReg64 .x0 (-ENOENT)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = none := hnone
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_cr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only; rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge]; simp

private theorem hole2_rf_execOpenat_rdonly_cloexec_emfile_dir {s : State} {path : String}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hdir : s.fs.files path = some .dir)
    (halloc : s.fs.allocFd = none) :
    execOpenat s = (s.writeReg64 .x0 (-EMFILE)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hrd_ne : (FdAccessMode.rdonly != FdAccessMode.rdonly) = false := rfl
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some .dir := hdir
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_tr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only; rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, hrd_ne, halloc]; simp

private theorem hole2_rf_execOpenat_rdonly_cloexec_file_or_emfile {s : State} {path : String}
    {bs : List (BitVec 8)}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (htd : trailingDir path = false)
    (hnorm_ne : normalizePath path ≠ [])
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hfile : s.fs.files path = some (.file bs)) :
    execOpenat s =
      match s.fs.allocFd with
      | none => (s.writeReg64 .x0 (-EMFILE)).advancePC
      | some fd =>
        ((s.setFs (s.fs.setFd fd (some
            { path := path, accMode := .rdonly, append := false, cloexec := true,
              offset := 0, kind := .localFile }))).writeReg64 .x0 fd).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hf_ap : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_APPEND_W32 != 0#32) = false := by decide
  have hf_dr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_DIRECTORY_W32 != 0#32) = false := by decide
  have hf_cl : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CLOEXEC_W32 != 0#32) = true := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some (.file bs) := hfile
  have hself : s.fs.setEntry (normalizePath path) (some (.file bs)) = s.fs :=
    FsState.setEntry_self_of_nonEmpty hnorm_ne hge
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_tr, hf_ap, hf_dr, hf_cl, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, Bool.and_false, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only; rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, htd]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  cases ha : s.fs.allocFd with
  | none => simp
  | some fd => simp [hself]

private theorem hole2_rf_setFs_appendTrace_nil (s : State) (fs' : FsState) :
    (s.setFs fs').appendTrace [] = s.setFs fs' := by
  cases s; simp [State.setFs, State.appendTrace]

private theorem hole2_rf_blockingAncestor?_ne_some_dir (fs : FsState) (path : String) :
    blockingAncestor? fs path ≠ some (some FsEntry.dir) :=
  LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic.blockingAncestor?_ne_some_dir fs path

private theorem hole2_rf_execOpenat_of_classifyOpenRdonly_err {s : State} {path : String}
    {errno : Nat}
    (hpok : PathOk path = true)
    (hmax : ((pathComps path).all fun c => decide (c.length ≤ NAME_MAX)) = true)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (htd : trailingDir path = false)
    (hnorm_ne : normalizePath path ≠ [])
    (hcl : classifyOpenRdonly s.fs path = .err errno)
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path) :
    execOpenat s = (s.writeReg64 .x0 (-BitVec.ofNat 64 errno)).advancePC := by
  have hanc_eq := ancestorWalkErrno?_eq_of_pathOk s.fs hpok hmax
  have hcl0 := hcl
  unfold classifyOpenRdonly at hcl
  cases hb : blockingAncestor? s.fs path with
  | some a =>
    rw [hb] at hcl hanc_eq
    cases a with
    | none =>
      have he : errno = 2 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
      subst he
      exact hole2_rf_execOpenat_rdonly_cloexec_err_anc hdfd hflags hcs hne hlead hdot hanc_eq
    | some e =>
      cases e with
      | dir => exact absurd hb (hole2_rf_blockingAncestor?_ne_some_dir s.fs path)
      | file _ =>
        have he : errno = 20 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
        subst he
        exact hole2_rf_execOpenat_rdonly_cloexec_err_anc hdfd hflags hcs hne hlead hdot hanc_eq
  | none =>
    rw [hb] at hcl hanc_eq
    cases hf : s.fs.files path with
    | none =>
      rw [hf] at hcl
      have he : errno = 2 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
      subst he
      exact hole2_rf_execOpenat_rdonly_cloexec_missing hdfd hflags hcs hne hlead hdot hanc_eq hf
    | some e =>
      obtain ⟨ha, rfl⟩ := hole2_rf_classifyOpenRdonly_err_of_none_some s.fs path e hb hf hcl0
      cases e with
      | dir =>
        exact hole2_rf_execOpenat_rdonly_cloexec_emfile_dir hdfd hflags hcs hne hlead hdot hanc_eq hf ha
      | file bs =>
        have hexec := hole2_rf_execOpenat_rdonly_cloexec_file_or_emfile hdfd hflags hcs hne hlead hdot
          htd hnorm_ne hanc_eq hf
        rw [ha] at hexec
        exact hexec

private theorem hole2_rf_muslOpenRdonlyDet_block_ok :
    subroutine_ok (hole2_rf_muslSys9Lib.blockProgram hole2_rf_muslPadMpl 8)
      (hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "open")
      (hole2_rf_muslSys9Lib.withCodeLoaded hole2_rf_muslPadMpl muslOpenRdonlyDetSpec) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨cstr, path, e0⟩ R s0 hpc hrun hpre hsp _hL
  simp only [MultiPlacedLib.withCodeLoaded, muslOpenRdonlyDetSpec, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpok, hmax, hlen, hlat⟩, hm⟩
  obtain ⟨hcp, hlead, hdot⟩ := validRelCPath_of_pathOk hpok hlen hlat
  have hne := isEmpty_false_of_pathOk hpok
  have htd := trailingDir_false_of_pathOk hpok
  have hnorm_ne := normalizePath_ne_nil_of_pathOk hpok
  have hb6 : O_CLOEXEC_W32.getLsbD 6 = false := by decide
  have htmp : O_CLOEXEC_W32 &&& 0x00404000#32 = 0#32 := by decide
  have hb19 : O_CLOEXEC_W32.getLsbD 19 = true := by decide
  have hfl_eq : O_CLOEXEC_W32 ||| O_LARGEFILE_W32 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  cases hcl : classifyOpenRdonly s0.fs path with
  | ok fd kind =>
    obtain ⟨hb_none, halloc, _, hfd_max, _, hkind_cases⟩ := classifyOpenRdonly_ok_spec hcl
    have hfd_lt : fd.toNat < 2 ^ 31 := by
      have hmmax : FsState.maxOpenFds = 1024 := rfl
      rw [hmmax] at hfd_max
      have h1024_lt : (1024 : Nat) < 2 ^ 31 := by decide
      exact Nat.lt_trans hfd_max h1024_lt
    have hanc_none : ancestorWalkErrno? s0.fs path = none := by
      rw [ancestorWalkErrno?_eq_of_pathOk s0.fs hpok hmax, hb_none]
    let desc : FdEntry :=
      { path := path, accMode := .rdonly, append := false, cloexec := true,
        offset := 0, kind := kind }
    let fs' : FsState := s0.fs.setFd fd (some desc)
    refine hole2_rf_muslOpenNoCreatCloexecLocalExec_block_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .ok fd desc fs' []) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      rcases hkind_cases with ⟨rfl, hdir⟩ | ⟨rfl, bs, hfile⟩
      · have hexec := execOpenat_rdonly_cloexec_dir hs_x0 (hfl_eq ▸ hs_x2) hcs hne hlead hdot
          (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hdir) (hs_fs.symm ▸ halloc)
        rw [hs_fs] at hexec
        refine ⟨hfd_lt, by simp [fs', FsState.setFd], Or.inr rfl, rfl, ?_⟩
        rw [hole2_rf_setFs_appendTrace_nil]; exact hexec
      · have hexec := hole2_rf_execOpenat_rdonly_cloexec_file_or_emfile hs_x0 (hfl_eq ▸ hs_x2) hcs hne
          hlead hdot htd hnorm_ne (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hfile)
        rw [hs_fs, halloc] at hexec
        refine ⟨hfd_lt, by simp [fs', FsState.setFd], Or.inl rfl, rfl, ?_⟩
        rw [hole2_rf_setFs_appendTrace_nil]; exact hexec
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simpa only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec,
          muslOpenRdonlyDetSpec, hcl, List.append_nil] using hq
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))
  | err errno =>
    have herr_cases := classifyOpenRdonly_err_cases hcl
    have herr_bounds : 1 ≤ errno ∧ errno ≤ 4095 := by
      rcases herr_cases with rfl | rfl | rfl <;> decide
    refine hole2_rf_muslOpenNoCreatCloexecLocalExec_block_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .err (· = errno)) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      refine ⟨errno, herr_bounds.1, herr_bounds.2, rfl, ?_⟩
      exact hole2_rf_execOpenat_of_classifyOpenRdonly_err hpok hmax hne hlead hdot htd hnorm_ne
        (hs_fs.symm ▸ hcl) hs_x0 (hfl_eq ▸ hs_x2) hcs
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simp only [MultiPlacedLib.withCodeLoaded, muslOpenNoCreatCloexecLocalExecSpec,
          muslOpenRdonlyDetSpec, hcl, sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
          satisfies_pure_sepConj] at hq ⊢
        rcases hq with ⟨errno', ⟨_, _, rfl, hx0', hfs', htr', hpres'⟩, hm_cells⟩
        exact ⟨⟨hx0', hfs', htr', hpres'⟩, hm_cells⟩
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))

private theorem hole2_rf_muslOpenRdonlyDet_ok :
    subroutine_ok f3TrialRxProg 0x46bb24#64 muslOpenRdonlyDetSpec := by
  have haddr : hole2_rf_muslSys9Lib.fnAddr hole2_rf_muslPadMpl "open" = 0x46bb24#64 := by decide
  rw [← haddr]
  exact hole2_rf_subroutine_ok_of_noExt (j := 8) (by decide) hole2_rf_muslOpenRdonlyDet_block_ok
    hole2_rf_musl9_contains.codeLoaded f3TrialRxProg_no_ext f3TrialRxProg_svc

private abbrev hole2_rf_ioMpl : MultiPlacement :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen.h2fsreads_ioMpl

set_option maxRecDepth 400000 in
private theorem hole2_rf_io_placeable :
    signalSessionIoMultiLib.Placeable hole2_rf_ioMpl :=
  MultiPlacedLib.placeable_of_checkPlaceable (by decide +kernel)

set_option maxRecDepth 400000 in
private theorem hole2_rf_io_readsCodeLoaded :
    ∀ m : Memory, f3TrialRxProg.CodeLoaded m →
      LibsignalBinary.Proofs.SignalSession.CliIo.Sym.CliIoReadsCodeLoaded hole2_rf_ioMpl m :=
  fun _ hCL =>
    LibsignalBinary.Proofs.SignalSession.CliIo.Sym.cliIoReadsCodeLoaded_of_blocks
      (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
        (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)
      (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
        (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)
      (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
        (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)

set_option maxRecDepth 400000 in
private theorem hole2_rf_memcpy_ok :
    subroutine_ok f3TrialRxProg 0x469650#64 stdMemcpySpec :=
  stdMemcpy_ok_of_hasWords f3TrialRxProg 0x469650#64 f3TrialRxProg_no_ext
    (hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
      (by rw [f3TrialRxProg_base]) (by decide)
      f3TrialRxProg_stubs f3TrialRxProg_symbols (by rfl_kernel))

private theorem hole2_rf_shim_ok :
    subroutine_ok f3TrialRxProg 0x469640#64 rustAllocShimVmSpec := by
  have heq : f3NoShimV2Addr = 0x469640#64 := by rfl_kernel
  rw [← heq]
  exact rustAllocShimVm_ret_ok f3Trial_seg5ShimBundle.noAllocShimV2

private theorem hole2_rf_readFile_cond_ok (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg 0x4691b4#64
      (readFileAnyBudgetCondSpec
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) := by
  have hentry : signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoReadFileSym = 0x4691b4#64 := by
    rw [cliIoResolve_eq_base hole2_rf_io_placeable 3 cliIoReadFileSym (by decide) (by rfl_kernel)]
    rfl
  have hopen_a : signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoOpenSym = 0x46bb24#64 := by
    decide
  have herrno_a : signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoErrnoLocationSym = 0x46ba94#64 := by
    decide
  have hread_a : signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoReadSym = 0x46e240#64 := by
    decide
  have hclose_a : signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoCloseSym = 0x46e1fc#64 := by
    decide
  have hmemcpy_a : signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoMemcpySym = 0x469650#64 := by
    decide
  have hshim_a : signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoRustNoAllocShimSym = 0x469640#64 := by
    decide
  have halloc_a :
      ({ alloc := signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoRustAllocSym
         dealloc := signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoRustDeallocSym
         realloc := signalSessionIoMultiLib.resolve hole2_rf_ioMpl cliIoRustReallocSym } :
        LibsignalBinary.Heap.RustAllocAddrs) = f3StubAddrs := by
    rfl_kernel
  rw [← hentry]
  exact cliIoReadFileAnyBudgetCond_ok_of_entries_of_readsCodeLoaded (stk := extHookStack)
    (fineHookPoolErrnoSplit γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    hole2_rf_io_placeable hole2_rf_io_readsCodeLoaded (by decide)
    f3TrialRxProg_svc
    (ExternPreservesOracleSymtab.of_no_extern f3TrialRxProg_no_ext)
    (CliIoBlockNoExtern.of_no_extern f3TrialRxProg_no_ext 3)
    (CliIoBlockNoExtern.of_no_extern f3TrialRxProg_no_ext 4)
    (hopen_a ▸ hole2_rf_muslOpenRdonlyDet_ok)
    (herrno_a ▸ hole2_rf_muslErrnoLocation2_ok)
    (hread_a ▸ hole2_rf_muslReadDir32_ok)
    (hread_a ▸ hole2_rf_muslReadFileOrStdio32_ok)
    (hclose_a ▸ hole2_rf_muslClose48Local_ok)
    (hmemcpy_a ▸ hole2_rf_memcpy_ok)
    (hshim_a ▸ hole2_rf_shim_ok)
    (halloc_a ▸ hole2_stubEntries mmpl hMm γ tp)

private theorem hole2_rf_readFile_hookOk (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk
      (f3ReadFileFixedGhostHookFine hole2_keepSub hole2_emptyProg f3TrialRxProg 0x4691b4#64
        mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack)
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) :=
  f3ReadFileFixedGhostHookFine_ok_placed rfl f3TrialRxProg_svc
    (fun pc _ => hole2_emptyProg_externAt pc) f3TrialRxProg_no_ext
    (hole2_mng_placeable mmpl hMm) (hole2_keepSub_mallocng mmpl hMm)
    (Nat.le_refl extHookStack) (hole2_rf_readFile_cond_ok mmpl hMm) γ tp

private theorem hole2_rf_cliGhostExterns_readFile [LibsignalPlacement]
    (mpl mmpl : MultiPlacement) (W : CliHooks) :
    cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) lsReadFileSym =
      some (f3ReadFileFixedGhostHookFine hole2_keepSub hole2_emptyProg f3TrialRxProg 0x4691b4#64
        mmpl cliElfImage.brkStart cliBudgetLimits hole2_hookStack) :=
  CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readFile_some
    (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) rfl

private theorem hole2_rf_readFile_hookSat_stk [LibsignalPlacement] (mpl mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {stk : Nat} (hstk : hole2_hookStack ≤ stk)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    HookSat (cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits stk (ReadFileRuleEnvFixed cliIo.rd)) :=
  hookSat_readFileSpecPlaced_mono_stk (by decide : 0 < hole2_hookStack) hstk
    (hookSat_readFile_of_hookOk (hole2_rf_cliGhostExterns_readFile mpl mmpl W)
      (hole2_rf_readFile_hookOk mmpl hMm γ tp))

private theorem hole2_rf_hReadSat_ext (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W)) lsReadFileSym
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  fun W γ tp =>
    hole2_rf_readFile_hookSat_stk mpl mmpl hMm (Nat.le_refl hole2_hookStack) W γ tp

end Hole2Gap1BReadFile

theorem hole2_readFileFineSub_cond_ok
    (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
        0x4691b4#64
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.readFileAnyBudgetCondSpec
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits extHookStack) := by
  exact hole2_rf_readFile_cond_ok mmpl hMm

theorem hole2_hReadSat
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W)) lsReadFileSym
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  exact fun W γ tp => hole2_rf_readFile_hookSat_stk mpl mmpl hMm (by decide) W γ tp

private theorem hfsr_hookMemcpy_trace (s : Arm64.State) :
    (ProofLib.hookMemcpy s).trace = s.trace := by
  unfold ProofLib.hookMemcpy ProofLib.retHook
  dsimp (config := { zeta := true, zetaHave := true }) only [Arm64.State.setMem, Arm64.State.setPC]

private theorem hfsr_emptyProg_steps_noAllocFailed {s0 sf : Arm64.State} {entry : BitVec 64}
    (h : Arm64.Steps hole2_emptyProg (s0.setPC entry) sf) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.TraceDeltaNoAllocFailed
      s0 sf :=
  LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_trans
    (s1 := s0.setPC entry)
    (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl)
    (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.steps_traceDeltaNoAllocFailed
      LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.execSyscall_noAllocFailed
      (fun pc _ he => nomatch (hole2_emptyProg_externAt pc).symm.trans he)
      h)

private theorem hfsr_linkedCallHook_noAllocFailed {α : Type}
    (entryTarget : BitVec 64)
    (specOf : GhostName → BitVec 64 → Arm64.Spec α)
    (fallback : Arm64.State → Arm64.State) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.HookNoAllocFailed
      (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3LinkedCallHook
        hole2_keepSub hole2_emptyProg
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
        entryTarget specOf fallback) := by
  classical
  intro s0
  unfold LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3LinkedCallHook
  split
  · split
    · rename_i hReal
      exact hfsr_emptyProg_steps_noAllocFailed (Classical.choose_spec hReal.2.2.2).1.toSteps
    · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl

private theorem hfsr_strCloneProg_externs_noAllocFailed (mpl : MultiPlacement) :
    ExternNoAllocFailed (hole2_strCloneProg mpl).externs := by
  intro sym f hf
  dsimp only [hole2_strCloneProg] at hf
  split at hf
  · injection hf with hfeq
    subst hfeq
    exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.hookNoAllocFailed_of_trace_eq
      _ hfsr_hookMemcpy_trace
  · split at hf
    · injection hf with hfeq
      subst hfeq
      exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.hookNoAllocFailed_of_trace_eq
        _ (fun _ => rfl)
    · cases hf

private theorem hfsr_strCloneGhostHook_noAllocFailed [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.HookNoAllocFailed
      (hole2_strCloneGhostHook mpl mmpl) := by
  classical
  intro s0
  unfold hole2_strCloneGhostHook
  split
  · split
    · rename_i hReal
      exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_trans
        (s1 := s0.setPC (mpl.base 623))
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl)
        (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.steps_traceDeltaNoAllocFailed
          LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.execSyscall_noAllocFailed
          (LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.externAt_noAllocFailed_of_externs
            LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.externNoAllocFailed_none
            (hfsr_strCloneProg_externs_noAllocFailed mpl))
          (Classical.choose_spec hReal.2.2.2.2).1.toSteps)
    · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl

private theorem hfsr_readFileLinkedHook_noAllocFailed {M : LibsignalBinary.Heap.AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Arm64.Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → LibsignalBinary.Heap.RustCliAllocBudget M)
    (lim : LibsignalBinary.Heap.BudgetLimits) (stk : Nat)
    (ReadEnv : CryptoVerification.LibsignalPublicApi.StoreKit.FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (Guard : Arm64.State → Prop)
    (fallback : Arm64.State → Arm64.State) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.HookNoAllocFailed
      (LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileLinkedHook
        keep P_real P_sub entry_io AOf lim stk ReadEnv Guard fallback) := by
  classical
  intro s0
  unfold LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileLinkedHook
  split
  · split
    · rename_i hReal
      exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq
        (Classical.choose_spec hReal.2.2.2.2).2.2.2.1
    · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl

private theorem hfsr_readStdinGhostHook_noAllocFailed [LibsignalPlacement]
    {M : LibsignalBinary.Heap.AllocCostModel}
    (keep : BitVec 64 → Bool) (P_real P_sub : Arm64.Program) (entry_io : BitVec 64)
    (AOf : GhostName → BitVec 64 → LibsignalBinary.Heap.RustCliAllocBudget M)
    (lim : LibsignalBinary.Heap.BudgetLimits) (stk : Nat)
    (fallback : Arm64.State → Arm64.State) :
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.HookNoAllocFailed
      (LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHook
        keep P_real P_sub entry_io AOf lim stk fallback) := by
  classical
  intro s0
  unfold LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHook
  split
  · split
    · rename_i hReal
      exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq
        (Classical.choose_spec hReal.2.2.2).2.2.2.1
    · unfold LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced.keepFilesTrace
      dsimp only
      split
      · rename_i hkeep
        exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq hkeep.2
      · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl
  · exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.traceDeltaNoAllocFailed_of_eq rfl

theorem hole2_hghNoAlloc
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ExternNoAllocFailed (cliGhostExterns (hole2_ghFixed mpl mmpl) (fun _ => none)) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have _ := hMm
  intro name f h
  unfold cliGhostExterns at h
  dsimp only [hole2_ghFixed,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3CliGhostHooksFixed,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFineSub,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookSub,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHookFineSub,
    LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHookSub] at h
  split at h
  · injection h with hfeq
    subst hfeq
    exact hfsr_linkedCallHook_noAllocFailed _ _ _
  · split at h
    · injection h with hfeq
      subst hfeq
      exact hfsr_linkedCallHook_noAllocFailed _ _ _
    · split at h
      · injection h with hfeq
        subst hfeq
        exact hfsr_linkedCallHook_noAllocFailed _ _ _
      · split at h
        · injection h with hfeq
          subst hfeq
          exact hfsr_linkedCallHook_noAllocFailed _ _ _
        · split at h
          · injection h with hfeq
            subst hfeq
            exact LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt.hookNoAllocFailed_of_trace_eq
              _ (fun _ => rfl)
          · split at h
            · injection h with hfeq
              subst hfeq
              exact hfsr_strCloneGhostHook_noAllocFailed mpl mmpl
            · split at h
              · injection h with hfeq
                subst hfeq
                exact hfsr_readFileLinkedHook_noAllocFailed _ _ _ _ _ _ _ _ _ _
              · split at h
                · injection h with hfeq
                  subst hfeq
                  exact hfsr_readStdinGhostHook_noAllocFailed _ _ _ _ _ _ _ _
                · split at h
                  · injection h with hfeq
                    subst hfeq
                    exact
                      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow_noAllocFailed mmpl
                  · split at h
                    · injection h with hfeq
                      subst hfeq
                      exact
                        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow_noAllocFailed mmpl
                    · cases h

section Hole2SegcloneIoHelpers

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.Musl (
  MuslSysPlacement muslSysPlacedLib
  muslBlk00_errno_location muslBlk01_syscall_ret muslBlk02_sccp
  muslBlk03_syscall_cp muslBlk04_aio_close muslBlk05_close
  muslBlk06_read muslBlk07_write muslBlk08_open
  muslBlk09_fstat muslBlk10_fstatat
  muslSysLib00 muslSysLib01 muslSysLib02 muslSysLib03
  muslSysLib04 muslSysLib05 muslSysLib06 muslSysLib08
  muslSysPl00 muslSysPC00 muslSysPl01 muslSysPC01
  muslSysPl02 muslSysPC02 muslSysPl03 muslSysPC03
  muslSysPl04 muslSysPC04 muslSysPl05 muslSysPC05
  muslSysPl06 muslSysPC06 muslSysPl08 muslSysPC08
  muslSysPC02_svc muslSysPC08_svc
  muslEmptyCStrData muslErrnoLocationSpec
  stdMemcpy_ok_of_hasWords
  ValidCPath ValidRelCPath
  placed_program_rebase_self
  sxtw64_truncate32 ofNat64_toNat_of_lt63 ofNat64_le_maxSyscallOk
  CodeLoadedAt seq_codeLoaded_lr
  step_str64_perm_c step_stp64_perm step_str32_perm step_stp32_64_perm
  muslErrnoLocation_block_ok muslSyscallRetOk_block_ok muslSyscallRetErr_block_ok
)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng ProgContainsMultiLib memcpySymWords)
open VerifiedLibraries.RustStd (mallocngPlacedCAddrs)
open CryptoVerification (ls_hook_ok_ultra_of_mem signalSessionIoMultiLib)
open CryptoVerification.LibsignalPublicApi.StoreKit (subroutine_ok_rocl_of_plain)
open CryptoVerification.SignalSession (
  PathOk blockingAncestor? pathComps writeFileHook writeStdoutHook
)
open CryptoVerification.SignalSession.Cli.Main.Placed (instIsLsBlockProg_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliExternsPlaced_writeFile cliExternsPlaced_writeStdout
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  cliGhostExterns_other cliGhostExterns_readFile_some cliGhostExterns_readStdin_some
)
open LibsignalBinary.Heap (RustCliAllocBudgetEntriesBase)
open LibsignalBinary.Heap.Fine (
  f3MallocngMpl f3NoShimV2Addr f3RdlAddrs f3RxWordCount f3StdLayout f3StubAddrs
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  rustAllocShimVmSpec rustAllocShimVm_ret_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineHookRustCliAllocBudgetEntries
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook (
  f3ReadFileFixedGhostHookFine f3ReadFileFixedGhostHookFine_ok_lit readFileAnyBudgetCondSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileCliIoInst (
  cliIoReadFileAnyBudgetCond_ok_of_entries cliIoReadFileAnyBudgetCond_ok_of_entries_of_readsCodeLoaded
  fineHookPoolErrnoSplit
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced (
  readStdinBudgetCondSpec writeFileHook_ok_placed writeStdoutHook_ok_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinCliIoInst (
  cliIoReadStdin_budgetCond_ok cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  f3ReadStdinGhostHookFine f3ReadStdinGhostHookFine_ok_bounded
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec (
  checkMultiBlocksFrom codeLoaded_of_checkProgSliceInWordTree progContainsMultiLib_of_wordTree
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslDirReadClose (
  OpenatLocalExecSpec OpenatLocalOutcome dirReadErrno32 dirReadErrno32_cases
  dirReadErrno32_ne_eintr dirReadErrnoNat dirReadErrnoNat_bounds execOpenat_rdonly_cloexec_dir
  muslClose48LocalSpec muslOpenNoCreatCloexecLocalExecSpec muslReadDir32Spec
  step_svc_close_fd_local
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (
  GoodComp ancestorWalkErrno?_eq_of_pathOk blockingAncestor?_ne_some_dir
  classifyOpenRdonly classifyOpenRdonly_err_cases classifyOpenRdonly_ok_spec
  goodComp_of_mem_pathComps hasDotDot_strOfComps hasLeadingSlash_strOfComps
  isEmpty_false_of_pathOk muslOpenRdonlyDetSpec normalizePath_ne_nil_of_pathOk
  pathComps_ne_nil strOfComps_pathComps trailingDir_false_of_pathOk validRelCPath_of_pathOk
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslReadStdin (
  muslReadFileOrStdio32Spec muslReadStdin32Spec
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (ExternPreservesOracleSymtab)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  cliIoCloseSym cliIoErrnoLocationSym cliIoMemcpySym cliIoOpenSym cliIoReadFileSym cliIoReadStdinSym
  cliIoReadSym cliIoRustAllocSym cliIoRustDeallocSym cliIoRustNoAllocShimSym cliIoRustReallocSym
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced (
  f3CliElf_mallocng_linkedAt_unique
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture (f3TrialElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (
  f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_stubs
  f3TrialRxProg_svc f3TrialRxProg_symbols f3TrialRxWordTree_eq f3TrialRxWordTree_size
  f3Trial_allocMemcpyVm_ok f3Trial_seg5ShimBundle
)

/-! ### `mallocngLib` Keep-Region and Entry Helpers -/

private noncomputable def hole2_checkMngInKeepSub : Bool :=
  (List.range mallocngLib.blocks.length).all fun k =>
    let b := (f3MallocngMpl.base k).toNat
    let len := (mallocngLib.blocks[k]?.map (fun blk => blk.code.length)).getD 0
    decide (0x469000 ≤ b ∧ b + len ≤ 0x46f000)

private theorem hole2_checkMngInKeepSub_ok : hole2_checkMngInKeepSub = true := by
  rfl_kernel

theorem hole2_keepMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (a : BitVec 64)
    (hsome : (mallocngLib.findCodeBlock mmpl a).isSome = true) :
    hole2_keepSub a = true := by
  have hbase := (f3CliElf_mallocng_linkedAt_unique hMm).1
  cases hf : mallocngLib.findCodeBlock mmpl a with
  | none => simp only [hf, Option.isSome_none, Bool.false_eq_true] at hsome
  | some k =>
    have hf' :
        (List.range mallocngLib.blocks.length).find?
          (fun j => decide (ProofLib.InRegion (mmpl.base j)
            (mallocngLib.blockPatched mmpl j).length a)) = some k := hf
    have hk : k < mallocngLib.blocks.length :=
      List.mem_range.mp (List.mem_of_find?_eq_some hf')
    have hin : (a - mmpl.base k).toNat < (mallocngLib.blockPatched mmpl k).length :=
      of_decide_eq_true (@List.find?_some _ (fun j => decide (ProofLib.InRegion (mmpl.base j)
        (mallocngLib.blockPatched mmpl j).length a)) _ _ hf')
    have hpat : (mallocngLib.blockPatched mmpl k).length = mallocngLib.blocks[k].code.length := by
      have hcode : mallocngLib.blockPatched mmpl k = (mallocngLib.blockProgram mmpl k).code := rfl
      rw [hcode]
      simp only [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hk]
      exact CodeBlock.length_patched_of_aligned _
        ((hole2_hPl_mng mmpl hMm).blocks_ok k hk).len_aligned
    have hbk := List.all_eq_true.mp hole2_checkMngInKeepSub_ok k (List.mem_range.mpr hk)
    simp only [List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some,
      decide_eq_true_eq] at hbk
    rw [hbase k hk, hpat] at hin
    have hlt_len : (a - f3MallocngMpl.base k).toNat < mallocngLib.blocks[k].code.length := hin
    rw [BitVec.toNat_sub] at hlt_len
    have ha_lt : a.toNat < 2 ^ 64 := a.isLt
    have hb_lt : (f3MallocngMpl.base k).toNat < 2 ^ 64 := (f3MallocngMpl.base k).isLt
    unfold hole2_keepSub
    by_cases hle : (f3MallocngMpl.base k).toNat ≤ a.toNat
    · have hsum : 2 ^ 64 - (f3MallocngMpl.base k).toNat + a.toNat =
          2 ^ 64 + (a.toNat - (f3MallocngMpl.base k).toNat) := by omega
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hlt_len
      exact decide_eq_true ⟨by omega, by omega⟩
    · rw [Nat.mod_eq_of_lt (by omega)] at hlt_len
      omega

theorem hole2_keepMallocngFull (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (a : BitVec 64)
    (hsome : (mallocngLib.findCodeBlock mmpl a).isSome = true) :
    hole2_keep a = true := by
  have hsub := of_decide_eq_true (hole2_keepMallocng mmpl hMm a hsome)
  exact decide_eq_true (Or.inr hsub)

private noncomputable def hole2_checkMallocngInRx (L : StdBinaryLayout)
    (mpl : MultiPlacement) (img : Arm64.Process.ElfImage) : Bool :=
  match img.segments[L.rxSegIdx]? with
  | none => false
  | some rxSeg =>
    withForcedNat (fastLen512 4096 rxSeg.bytes) fun rxLen =>
      (img.segments.take L.rxSegIdx).all
        (fun q => decide (q.start.toNat + fastLen512 4096 q.bytes ≤ rxSeg.start.toNat)) &&
      decide (rxSeg.start.toNat + rxLen ≤ 2 ^ 64) &&
      (List.range mallocngLib.blocks.length).all
        (fun i =>
          (mpl.base i).toNat % 4 == 0 &&
          decide (rxSeg.start.toNat ≤ (mpl.base i).toNat) &&
          decide ((mpl.base i).toNat +
            (mallocngLib.blocks[i]?.map (fun b => fastLen512 4096 b.code)).getD 0 ≤
            rxSeg.start.toNat + rxLen))

private theorem hole2_checkMallocngInRx_f3 :
    hole2_checkMallocngInRx f3StdLayout f3MallocngMpl f3TrialElf = true := by
  rfl_kernel

private theorem hole2_progContainsMallocng_of_inElf {L : StdBinaryLayout}
    {mpl : MultiPlacement} {img : Arm64.Process.ElfImage}
    (hpl : mallocngLib.Placeable mpl)
    (hin : mallocngLib.InElf img mpl)
    (hok : hole2_checkMallocngInRx L mpl img = true) :
    ProgContainsMallocng (L.rxProgram img) mpl := by
  unfold hole2_checkMallocngInRx at hok
  split at hok <;> try contradiction
  rename_i rxSeg hrxSeg
  simp only [Arm64.Process.withForcedNat_eq, Arm64.Process.fastLen512_eq_length,
    Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hpre, hwrap⟩, hblks⟩ := hok
  have hrx_lt : L.rxSegIdx < img.segments.length := by
    apply Classical.byContradiction
    intro hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hrxSeg
    contradiction
  have hrx_eq : img.segments[L.rxSegIdx] = rxSeg := by
    rw [List.getElem?_eq_getElem hrx_lt] at hrxSeg
    exact Option.some.inj hrxSeg
  have hsplit : img.segments =
      img.segments.take L.rxSegIdx ++ rxSeg :: img.segments.drop (L.rxSegIdx + 1) := by
    rw [← hrx_eq, List.getElem_cons_drop, List.take_append_drop]
  have hpre' : (img.segments.take L.rxSegIdx).all (Snapshot.Below rxSeg.start) = true := by
    rw [List.all_eq_true] at hpre ⊢
    intro q hq
    have hq0 := hpre q hq
    simp only [Snapshot.Below, decide_eq_true_eq] at hq0 ⊢
    exact hq0
  refine ProgContainsMultiLib.of_noExterns hpl (StdBinaryLayout.rxProgram_svc L img)
    (fun m hPm i hi => ?_)
    (fun pc => congrFun (StdBinaryLayout.rxProgram_externAt? L img) pc)
  have hP_eq : L.rxProgram img =
      { base := rxSeg.start, code := rxSeg.bytes, svc := Syscall.standard } := by
    simp only [StdBinaryLayout.rxProgram, hrxSeg]
  rw [hP_eq] at hPm
  rw [Program.codeLoaded_iff] at hPm ⊢
  obtain ⟨_, _, hP_bytes⟩ := hPm
  have hbi := List.all_eq_true.mp hblks i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some] at hbi
  rcases hbi with ⟨⟨hal_i, hle_i⟩, hfit_i⟩
  have hbase_eq : (mallocngLib.blockProgram mpl i).base = mpl.base i := rfl
  have hcode_eq : (mallocngLib.blockProgram mpl i).code =
      mallocngLib.blocks[i].patched (mallocngLib.blockPlacement mpl i) := by
    simp only [MultiPlacedLib.blockProgram, PlacedLib.program, mallocngLib.blockLib_text hi]
  have hlen_i : (mallocngLib.blockProgram mpl i).code.length =
      mallocngLib.blocks[i].code.length := by
    rw [hcode_eq]
    exact CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok i hi).len_aligned
  refine ⟨by rw [hbase_eq]; exact hal_i, by rw [hbase_eq, hlen_i]; omega, fun k hk => ?_⟩
  let idx := ((mpl.base i).toNat - rxSeg.start.toNat) + k
  have hidx_lt : idx < rxSeg.bytes.length := by rw [hlen_i] at hk; omega
  have hk_pat : k < (mallocngLib.blocks[i].patched
      (mallocngLib.blockPlacement mpl i)).length := by rwa [← hcode_eq]
  obtain ⟨p, hcell1, _⟩ := hin.blocks i hi k hk_pat
  have haddr_eq : rxSeg.start + BitVec.ofNat 64 idx = mpl.base i + BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : idx < 2 ^ 64 := by omega
    have h2 : k < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hcell2 : Snapshot.cellAt img.segments (rxSeg.start + BitVec.ofNat 64 idx) =
      some (some rxSeg.perm, rxSeg.bytes[idx]) := by
    rw [hsplit]
    exact Snapshot.cellAt_of_split hpre' hidx_lt hwrap
  rw [← haddr_eq, hcell2, Option.some.injEq, Prod.mk.injEq] at hcell1
  obtain ⟨hrd, hperm⟩ := hP_bytes idx hidx_lt
  rw [hbase_eq, ← haddr_eq]
  have hbyte_eq : (mallocngLib.blockProgram mpl i).code[k] = rxSeg.bytes[idx] := by
    simp only [hcode_eq]
    exact hcell1.2.symm
  exact ⟨hrd.trans hbyte_eq.symm, hperm⟩

theorem hole2_progContainsMallocng (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    ProgContainsMallocng f3TrialRxProg mmpl := by
  have hbase := (f3CliElf_mallocng_linkedAt_unique hMm).1
  obtain ⟨img, hparse, hpl, hin⟩ := hMm
  cases cliElf_parse.symm.trans hparse
  refine hole2_progContainsMallocng_of_inElf hpl hin ?_
  have hf3 := hole2_checkMallocngInRx_f3
  unfold hole2_checkMallocngInRx at hf3 ⊢
  cases hrx : f3TrialElf.segments[f3StdLayout.rxSegIdx]? with
  | none =>
    rw [hrx] at hf3
    cases hf3
  | some rxSeg =>
    rw [hrx] at hf3
    simp only [Arm64.Process.withForcedNat_eq, Bool.and_eq_true, List.all_eq_true] at hf3 ⊢
    refine ⟨hf3.1, fun i hi => ?_⟩
    rw [hbase i (List.mem_range.mp hi)]
    exact hf3.2 i hi

private theorem hole2_lookupBlockSymAux_lt {sym : String} :
    ∀ {cur idx off : Nat} {blks : List CodeBlock},
      lookupBlockSymAux sym cur blks = some (idx, off) → idx < cur + blks.length
  | _, _, _, [], h => by simp only [lookupBlockSymAux] at h; nomatch h
  | cur, idx, off, b :: bs, h => by
    unfold lookupBlockSymAux at h
    cases hlk : lookup sym b.symbols with
    | some o =>
      rw [hlk] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      simp only [List.length_cons]
      omega
    | none =>
      rw [hlk] at h
      have hlt := hole2_lookupBlockSymAux_lt h
      simp only [List.length_cons] at hlt ⊢
      omega

private theorem hole2_lookupBlockSym_lt {sym : String} {blks : List CodeBlock} {idx off : Nat}
    (h : lookupBlockSym sym blks = some (idx, off)) : idx < blks.length := by
  have h0 := hole2_lookupBlockSymAux_lt h
  omega

private theorem hole2_mngFnAddr_eq {mmpl : MultiPlacement}
    (hbase : ∀ i < mallocngLib.blocks.length, mmpl.base i = f3MallocngMpl.base i)
    (sym : String) :
    mallocngLib.fnAddr mmpl sym = mallocngLib.fnAddr f3MallocngMpl sym := by
  unfold MultiPlacedLib.fnAddr
  cases h : lookupBlockSym sym mallocngLib.blocks with
  | none => exact hbase 0 (by decide)
  | some p =>
    dsimp only
    rw [hbase p.1 (hole2_lookupBlockSym_lt h)]

private theorem hole2_cAddrs_eq (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    mallocngPlacedCAddrs mmpl = mallocngPlacedCAddrs f3MallocngMpl := by
  have hbase := (f3CliElf_mallocng_linkedAt_unique hMm).1
  unfold mallocngPlacedCAddrs
  simp only [hole2_mngFnAddr_eq hbase]

theorem hole2_fineHookAllocEntries (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) f3TrialRxProg f3RdlAddrs :=
  fineHookRustCliAllocBudgetEntries (hole2_progContainsMallocng mmpl hMm)
    γ tp cliElfImage.brkStart
    (hole2_cAddrs_eq mmpl hMm ▸ f3Trial_seg5ShimBundle.rdlShims)
    f3Trial_allocMemcpyVm_ok

private theorem hole2_stdMemcpy_ok :
    subroutine_ok f3TrialRxProg 0x469650#64 stdMemcpySpec :=
  stdMemcpy_ok_of_hasWords f3TrialRxProg f3StdLayout.memcpyAddr f3TrialRxProg_no_ext
    (hasWords_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
      (by rw [f3TrialRxProg_base]) (by decide) f3TrialRxProg_stubs f3TrialRxProg_symbols
      (by rfl_kernel))

private theorem hole2_noAllocShim_ok :
    subroutine_ok f3TrialRxProg 0x469640#64 rustAllocShimVmSpec :=
  rustAllocShimVm_ret_ok f3Trial_seg5ShimBundle.noAllocShimV2

/-! #### 9-Block `musl` Syscall Sub-Library on `f3TrialRxProg` -/

private def hole2_muslFullMpl : MultiPlacement where
  base i :=
    [0x46ba94#64, 0x46bbc0#64, 0x46e1c4#64, 0x46e1e8#64, 0x46e1f8#64,
     0x46e1fc#64, 0x46e240#64, 0x46e274#64, 0x46bb24#64, 0x4b0000#64, 0x4b1000#64].getD i 0#64
  ρ s :=
    if s == "muslEmptyCStr" then 0x4b2000#64
    else if s == "__procfdname" then 0x4b3000#64
    else if s == "fstat" then 0x4b0000#64
    else if s == "fstatat" then 0x4b1000#64
    else 0#64

private theorem hole2_muslFullMpl_placeable :
    muslSysPlacedLib.Placeable hole2_muslFullMpl :=
  muslSysPlacedLib.placeable_of_checkPlaceable (by rfl_kernel)

@[reducible] private local instance hole2_instMuslSysPlacement : MuslSysPlacement where
  mpl := hole2_muslFullMpl
  placeable := hole2_muslFullMpl_placeable

private def hole2_musl9Lib : MultiPlacedLib where
  name := "musl_sys"
  blocks := [
    muslBlk00_errno_location, muslBlk01_syscall_ret, muslBlk02_sccp,
    muslBlk03_syscall_cp, muslBlk04_aio_close, muslBlk05_close,
    muslBlk06_read, muslBlk07_write, muslBlk08_open]
  data := []
  exports := [
    "___errno_location", "__errno_location", "__syscall_ret",
    "__syscall_cp", "__aio_close", "close", "read", "write", "open"]

private theorem hole2_musl9_placeable :
    hole2_musl9Lib.Placeable hole2_muslFullMpl :=
  hole2_musl9Lib.placeable_of_checkPlaceable (by rfl_kernel)

private theorem hole2_progContainsMusl9 :
    ProgContainsMultiLib hole2_musl9Lib f3TrialRxProg hole2_muslFullMpl :=
  progContainsMultiLib_of_wordTree f3RxWordCount f3TrialRxWordTree_eq f3TrialRxWordTree_size
    hole2_musl9_placeable f3TrialRxProg_svc f3TrialRxProg_no_ext
    (by rw [f3TrialRxProg_base]; rfl_kernel)

private theorem hole2_musl9_resolve_eq :
    hole2_musl9Lib.resolve hole2_muslFullMpl =
      muslSysPlacedLib.resolve hole2_muslFullMpl := by
  funext sym
  unfold MultiPlacedLib.resolve lookupBlockSym hole2_musl9Lib muslSysPlacedLib
  dsimp only [lookupBlockSymAux]
  cases lookup sym muslBlk00_errno_location.symbols <;> try rfl
  cases lookup sym muslBlk01_syscall_ret.symbols <;> try rfl
  cases lookup sym muslBlk02_sccp.symbols <;> try rfl
  cases lookup sym muslBlk03_syscall_cp.symbols <;> try rfl
  cases lookup sym muslBlk04_aio_close.symbols <;> try rfl
  cases lookup sym muslBlk05_close.symbols <;> try rfl
  cases lookup sym muslBlk06_read.symbols <;> try rfl
  cases lookup sym muslBlk07_write.symbols <;> try rfl
  cases lookup sym muslBlk08_open.symbols <;> try rfl
  dsimp only [hole2_muslFullMpl, muslBlk09_fstat, muslBlk10_fstatat, lookup]
  by_cases h9 : (sym == "fstat") = true
  · rcases beq_iff_eq.mp h9 with rfl; decide
  · by_cases h10 : (sym == "fstatat") = true
    · rcases beq_iff_eq.mp h10 with rfl; decide
    · have h9f : ("fstat" == sym) = false :=
        beq_eq_false_iff_ne.mpr (fun h => h9 (beq_iff_eq.mpr h.symm))
      have h10f : ("fstatat" == sym) = false :=
        beq_eq_false_iff_ne.mpr (fun h => h10 (beq_iff_eq.mpr h.symm))
      have h9f' : (sym == "fstat") = false := Bool.eq_false_iff.mpr h9
      have h10f' : (sym == "fstatat") = false := Bool.eq_false_iff.mpr h10
      simp only [List.find?, h9f, h10f, h9f', h10f', Option.map]

private theorem hole2_musl9_blockPlacement_eq (i : Nat) :
    hole2_musl9Lib.blockPlacement hole2_muslFullMpl i =
      muslSysPlacedLib.blockPlacement hole2_muslFullMpl i := by
  simp only [MultiPlacedLib.blockPlacement, hole2_musl9_resolve_eq]

private theorem hole2_musl9_blockProgram_eq (i : Nat) (lib : PlacedLib) (pl : Placement)
    (ht : (hole2_musl9Lib.blockLib i).text = lib.text)
    (hpl : muslSysPlacedLib.blockPlacement hole2_muslFullMpl i = pl) :
    hole2_musl9Lib.blockProgram hole2_muslFullMpl i =
      (lib.program pl).rebase pl.base (fun _ => none) := by
  rw [← placed_program_rebase_self lib pl]
  unfold MultiPlacedLib.blockProgram PlacedLib.program Program.rebase
  rw [ht, hole2_musl9_blockPlacement_eq i, hpl]

@[local simp] private theorem hole2_lk_errno :
    lookupBlockSymAux "___errno_location" 0 muslSysPlacedLib.blocks = some (0, 0) := by decide
@[local simp] private theorem hole2_lk_sysret :
    lookupBlockSymAux "__syscall_ret" 0 muslSysPlacedLib.blocks = some (1, 0) := by decide
@[local simp] private theorem hole2_lk_sccp :
    lookupBlockSymAux "__syscall_cp" 0 muslSysPlacedLib.blocks = some (3, 0) := by decide
@[local simp] private theorem hole2_lk_aioclose :
    lookupBlockSymAux "__aio_close" 0 muslSysPlacedLib.blocks = some (4, 0) := by decide
@[local simp] private theorem hole2_muslFullMpl_base0 :
    hole2_muslFullMpl.base 0 = 0x46ba94#64 := rfl
@[local simp] private theorem hole2_muslFullMpl_base1 :
    hole2_muslFullMpl.base 1 = 0x46bbc0#64 := rfl
@[local simp] private theorem hole2_muslFullMpl_base3 :
    hole2_muslFullMpl.base 3 = 0x46e1e8#64 := rfl
@[local simp] private theorem hole2_muslFullMpl_base4 :
    hole2_muslFullMpl.base 4 = 0x46e1f8#64 := rfl

private theorem hole2_condHI_adds_4096_false {a : BitVec 64} (ha : a.toNat ≤ 2 ^ 64 - 4096) :
    ConditionHolds .HI (addsPState64 a 4096#64) = false := by
  rw [conditionHolds_hi_addsPState64]
  by_cases heq : a = -4096#64
  · subst heq; decide
  · have hlt_strict : a.toNat < 2 ^ 64 - 4096 := by
      refine Nat.lt_of_le_of_ne ha fun h => heq (BitVec.eq_of_toNat_eq ?_)
      have : (-4096#64 : BitVec 64).toNat = 2 ^ 64 - 4096 := by decide
      omega
    have hadd : (a + 4096#64).toNat = a.toNat + 4096 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : 4096 % 2 ^ 64 = 4096 := by decide
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have hult : BitVec.ult (a + 4096#64) a = false := by
      simp only [BitVec.ult, hadd, decide_eq_false_iff_not]; omega
    rw [hult, Bool.false_and]

private theorem hole2_condHI_adds_4096_true {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ConditionHolds .HI (addsPState64 (-BitVec.ofNat 64 err) 4096#64) = true := by
  rw [conditionHolds_hi_addsPState64]
  have herr_mod : err % 2 ^ 64 = err := Nat.mod_eq_of_lt (by omega)
  have h4096_mod : 4096 % 2 ^ 64 = 4096 := by decide
  have hneg : (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, herr_mod, Nat.mod_eq_of_lt (by omega)]
  have hsum : (-BitVec.ofNat 64 err + 4096#64).toNat = 4096 - err := by
    rw [BitVec.toNat_add, hneg, BitVec.toNat_ofNat, h4096_mod]
    have : 2 ^ 64 - err + 4096 = 2 ^ 64 + (4096 - err) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hult : BitVec.ult (-BitVec.ofNat 64 err + 4096#64) (-BitVec.ofNat 64 err) = true := by
    simp only [BitVec.ult, hneg, hsum, decide_eq_true_eq]; omega
  have hne : (-BitVec.ofNat 64 err + 4096#64 != 0#64) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [hsum, BitVec.toNat_ofNat] at this
    omega
  rw [hult, hne]; rfl

private theorem hole2_neg_truncate32_neg_ofNat (err : Nat) :
    0#32 - (-BitVec.ofNat 64 err).truncate 32 = BitVec.ofNat 32 err := by bv_omega

private def hole2_muslSyscallRetOkSpec : Spec (BitVec 64) where
  pre := fun retVal s0 =>
    ⌜s0.readReg64 .x0 = retVal ∧ retVal.toNat ≤ 2 ^ 64 - 4096⌝ ∗ stackAt s0.sp 32
  post := fun retVal s0 sf =>
    ⌜sf.readReg64 .x0 = retVal ∧ StdStatePreserved s0 sf⌝ ∗ stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def hole2_muslSyscallRetErrSpec : Spec (Nat × BitVec 32) where
  pre := fun (err, e0) s0 =>
    ⌜s0.readReg64 .x0 = -BitVec.ofNat 64 err ∧ 1 ≤ err ∧ err ≤ 4095⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr s0 ↦₃₂ e0))
  post := fun (err, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -1#64 ∧ StdStatePreserved s0 sf⌝ ∗
    (stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ BitVec.ofNat 32 err))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def hole2_muslAioCloseSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = s0.readReg64 .x0 ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_muslErrnoLocation_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 0)
      (hole2_musl9Lib.fnAddr hole2_muslFullMpl "___errno_location")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl muslErrnoLocationSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 0 =
    muslSysPC00.rebase muslSysPl00.base (fun _ => none) from hole2_musl9_blockProgram_eq 0 muslSysLib00 muslSysPl00 rfl rfl]
  rw [show hole2_musl9Lib.fnAddr hole2_muslFullMpl "___errno_location" = muslSysPl00.base from rfl]
  wp_entry; wp_sym_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm],
    by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp only [wp_norm, arm64_norm, muslErrnoAddr], rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩

private theorem hole2_muslAioClose_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 4)
      (hole2_musl9Lib.resolve hole2_muslFullMpl "__aio_close")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl hole2_muslAioCloseSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 4 =
    muslSysPC04.rebase muslSysPl04.base (fun _ => none) from hole2_musl9_blockProgram_eq 4 muslSysLib04 muslSysPl04 rfl rfl]
  rw [show hole2_musl9Lib.resolve hole2_muslFullMpl "__aio_close" = muslSysPl04.base from rfl]
  wp_entry; wp_sym_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm],
    by simp (disch := decide) [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨⟨by simp only [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
    by simpa using hmem⟩

private theorem hole2_muslSyscallRetOk_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 1)
      (hole2_musl9Lib.fnAddr hole2_muslFullMpl "__syscall_ret")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl hole2_muslSyscallRetOkSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from hole2_musl9_blockProgram_eq 1 muslSysLib01 muslSysPl01 rfl rfl]
  rw [show hole2_musl9Lib.fnAddr hole2_muslFullMpl "__syscall_ret" = muslSysPl01.base from rfl]
  wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepConj_assoc]; repeat (apply SepWP.exists_left; intro)
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 2
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = false := hole2_condHI_adds_4096_false ‹_›
  simp only [hcond, Bool.false_eq_true, ↓reduceIte]; wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp_all [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp only [wp_norm, arm64_norm, hm2, hm1]⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [wp_norm, arm64_norm]

private theorem hole2_muslSyscallRetErr_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 1)
      (hole2_musl9Lib.fnAddr hole2_muslFullMpl "__syscall_ret")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl hole2_muslSyscallRetErrSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 1 =
    muslSysPC01.rebase muslSysPl01.base (fun _ => none) from hole2_musl9_blockProgram_eq 1 muslSysLib01 muslSysPl01 rfl rfl]
  rw [show hole2_musl9Lib.fnAddr hole2_muslFullMpl "__syscall_ret" = muslSysPl01.base from rfl]
  wp_entry
  wp_conv_pre => rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 2
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps
  have hcond : ConditionHolds .HI (addsPState64 _ 4096#64) = true := hole2_condHI_adds_4096_true ‹_› ‹_›
  simp only [hcond, ↓reduceIte]; wp_sym_steps
  wp_call_block hole2_muslErrnoLocation_blk_ok ()
  rcases ‹StdStatePreserved _ sf› with ⟨hbrk_sf, hfs_sf, htpidr_sf, htr_sf, hoidx_sf, horacle_sf, hphys_sf, _⟩
  simp only [wp_norm, arm64_norm] at hbrk_sf hfs_sf htpidr_sf htr_sf hoidx_sf horacle_sf hphys_sf
  simp only [muslErrnoAddr] at *; wp_sym_steps 3
  apply step_str32_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm3
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm3
  wp_sym_steps; wp_clear_temps
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, ‹sf.status = .Running›])
  refine ⟨fun hmem => ?_, by simp only [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm]; rfl, by simp only [wp_norm, arm64_norm, hbrk_sf.symm],
      by simp only [wp_norm, arm64_norm, hfs_sf.symm], by simp only [wp_norm, arm64_norm, htpidr_sf.symm],
      by simp only [wp_norm, arm64_norm, htr_sf.symm], by simp only [wp_norm, arm64_norm, hoidx_sf.symm],
      by simp only [wp_norm, arm64_norm, horacle_sf.symm], by simp only [wp_norm, arm64_norm, hphys_sf.symm],
      fun _ => by simp only [wp_norm, arm64_norm, hm3, ‹sf.mem = _›, hm2, hm1]⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    rw [show stackAt s0.sp 32 = cells (s0.sp - 32#64) 4 from stackAt_eq_cells s0.sp 4 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm, htpidr_sf.symm, hole2_neg_truncate32_neg_ofNat]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem hole2_muslSyscallCp_step {s0 : State} {target_pc : BitVec 64}
    {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s0.pc = muslSysPl03.base) (hrun : s0.status = .Running)
    (hcl : hole2_musl9Lib.CodeLoaded hole2_muslFullMpl s0.mem)
    (hnext : SepWP (muslSysPC02.rebase muslSysPl02.base (fun _ => none)) target_pc
      ((((((((s0.writeReg64 .x8 (s0.readReg64 .x0)).writeReg64 .x0 (s0.readReg64 .x1)).writeReg64
        .x1 (s0.readReg64 .x2)).writeReg64 .x2 (s0.readReg64 .x3)).writeReg64
        .x3 (s0.readReg64 .x4)).writeReg64 .x4 (s0.readReg64 .x5)).writeReg64
        .x5 (s0.readReg64 .x6)).setPC (muslSysPl02.base + 28#64)) P post) :
    SepWP (muslSysPC03.rebase muslSysPl03.base (fun _ => none)) target_pc s0 P post := by
  wp_sym_steps
  have hsccp : muslSysPl03.base + (muslSysPl03.ρ "sccp" - muslSysPl03.base) = muslSysPl02.base := rfl
  rw [hsccp]
  refine SepWP.of_sameHooks (P := muslSysPC03.rebase muslSysPl03.base (fun _ => none))
    (Q := muslSysPC02.rebase muslSysPl02.base (fun _ => none))
    (by intro pc
        change ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 2).rebase muslSysPl02.base (fun _ => none)).externAt? pc =
          ((muslSysPlacedLib.blockProgram MuslSysPlacement.mpl 3).rebase muslSysPl03.base (fun _ => none)).externAt? pc
        simp only [MultiPlacedLib.externAt?_blockProgram_rebase_none])
    rfl (hole2_musl9_blockProgram_eq 2 muslSysLib02 muslSysPl02 rfl rfl ▸ hcl 2 (by decide)) ?_
  wp_sym_steps
  simpa only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8] using hnext

private def hole2_muslSccpCloseLocalSpec : Spec (BitVec 64 × FdEntry) where
  pre := fun (fd, desc) s0 =>
    ⌜s0.readReg64 .x0 = 57#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind = .localFile ∨ desc.kind = .localDir)⌝
  post := fun (fd, _) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧
      sf.fs = s0.fs.setFd fd none ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_muslSccpCloseLocal_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 3)
      (hole2_musl9Lib.resolve hole2_muslFullMpl "__syscall_cp")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl hole2_muslSccpCloseLocalSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from hole2_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show hole2_musl9Lib.resolve hole2_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine hole2_muslSyscallCp_step hpc hrun h ?_
  refine step_svc_close_fd_local (fd := a_1) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4 h_5 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem hole2_muslClose48Local_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 5)
      (hole2_musl9Lib.fnAddr hole2_muslFullMpl "close")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl muslClose48LocalSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 5 =
    muslSysPC05.rebase muslSysPl05.base (fun _ => none) from hole2_musl9_blockProgram_eq 5 muslSysLib05 muslSysPl05 rfl rfl]
  rw [show hole2_musl9Lib.fnAddr hole2_muslFullMpl "close" = muslSysPl05.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 32 2 (by decide)]
  cells_unfold; simp only [sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep hole2_muslAioClose_blk_ok ()
  rcases ‹StdStatePreserved _ _› with ⟨hfs1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at hfs1 htr1 htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block_keep hole2_muslSccpCloseLocal_blk_ok (a_1, a_rest)
  rcases ‹SyscallPreserved _ _› with ⟨htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at htp2 hsig2 hb2 hbs2 hp2 hmp2
  wp_cut_codeLoaded; wp_sym_steps
  wp_call_block hole2_muslSyscallRetOk_blk_ok 0#64
  rcases ‹StdStatePreserved _ _› with ⟨hfs3, htr3, htp3, hsig3, hb3, hbs3, hp3, hmp3⟩
  simp only [wp_norm, arm64_norm, htp2, hsig2, hb2, hbs2, hp2, hmp2] at hfs3 htr3 htp3 hsig3 hb3 hbs3 hp3 hmp3
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · rw [satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *],
      by simp [wp_norm, arm64_norm, *], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · rw [show stackAt s0.sp 48 = stackAt (s0.sp - 16#64) 32 ∗ cells (s0.sp - 16#64) 2 from
        stackAt_split_cells s0.sp 32 2 (by decide)]
      cells_unfold; simp only [wp_norm, arm64_norm, *]; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem hole2_readReg32_slt_zero_false {w : BitVec 32} {fd : BitVec 64}
    (hfd : w.zeroExtend 64 = fd) (hlt : fd.toNat < 2 ^ 31) :
    w.slt 0#32 = false := by
  subst hfd
  have hw : w.toNat < 2 ^ 31 := by
    have := w.isLt
    simp only [BitVec.zeroExtend, BitVec.toNat_setWidth] at hlt
    omega
  unfold BitVec.slt BitVec.toInt
  simp; omega

private theorem hole2_step_svc_read_dir {prog : Program} {target_pc : BitVec 64}
    {s : State} {fd buf count : BitVec 64} {desc : FdEntry} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (_hx8 : s.readReg64 .x8 = 63#64)
    (hfd : (s.readReg32 .x0).zeroExtend 64 = fd)
    (hfd_lt : fd.toNat < 2 ^ 31 := by omega)
    (hbuf : s.readReg64 .x1 = buf)
    (hcnt : s.readReg64 .x2 = count)
    (hopen : s.fs.fds fd = some desc)
    (hkind : desc.kind = .localDir)
    (hrd : desc.accMode.canRead = true)
    (hnext :
      let s' := (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).setPC (pc + 4#64)
      SepWP prog target_pc s' P post oom)
    (hsvc : prog.evalInst (.system false 0#16) s = execRead s) :
    SepWP prog target_pc s P post oom := by
  have hpc_eq : s.setPC pc = s := by
    cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hslt : (s.readReg32 .x0).slt 0#32 = false := hole2_readReg32_slt_zero_false hfd hfd_lt
  have hexec : execRead s =
      (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).setPC (pc + 4#64) := by
    have hk_dir : (FdKind.localDir == FdKind.localDir) = true := rfl
    have hadv : (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).advancePC =
        (s.writeReg64 .x0 (-BitVec.ofNat 64 (dirReadErrnoNat buf count))).setPC (pc + 4#64) := by
      subst hpc; rfl
    refine Eq.trans ?_ hadv
    dsimp only [execRead, execReadCommon, dirReadErrnoNat]
    rw [hslt, hfd, hbuf, hcnt, hopen]; dsimp only
    rw [hkind, hrd, hk_dir]
    by_cases hva : buf.toNat + count.toNat > USER_VA_LIMIT
    · simp [hva, EFAULT_RET]
    · simp [hva, EISDIR]
  exact SepWP.step_pure hpc hrun hfetch (by rw [hpc_eq, hsvc, hexec]) (by cases s; rfl) hnext

private def hole2_muslSccpReadDirSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry) where
  pre := fun (fd, buf, count, desc) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      s0.fs.fds fd = some desc ∧
      desc.kind = .localDir ∧
      desc.accMode.canRead = true⌝
  post := fun (_, buf, count, _) s0 sf =>
    ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 (dirReadErrnoNat buf count) ∧
      sf.fs = s0.fs ∧
      sf.mem = s0.mem ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_muslSccpReadDir_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 3)
      (hole2_musl9Lib.resolve hole2_muslFullMpl "__syscall_cp")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl hole2_muslSccpReadDirSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from hole2_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show hole2_musl9Lib.resolve hole2_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine hole2_muslSyscallCp_step hpc hrun h ?_
  refine hole2_step_svc_read_dir (fd := a_1) (buf := a) (count := a_2) (desc := a_rest) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simpa [wp_norm, arm64_norm] using h_3) h_4
    (by simp [wp_norm, arm64_norm, h_5]) (by simp [wp_norm, arm64_norm, h_6])
    h_7 h_8 h_1 ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, h_2])
  dsimp only; (conv => arg 3; simp only [wp_norm, arm64_norm]); wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      rfl, by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
      by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem hole2_muslReadDir32_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 6)
      (hole2_musl9Lib.fnAddr hole2_muslFullMpl "read")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl muslReadDir32Spec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from hole2_musl9_blockProgram_eq 6 muslSysLib06 muslSysPl06 rfl rfl]
  rw [show hole2_musl9Lib.fnAddr hole2_muslFullMpl "read" = muslSysPl06.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep hole2_muslSccpReadDir_blk_ok (a_1, a, a_2, a_3)
  rcases ‹SyscallPreserved _ sf› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
  wp_conv_pre => rw [htp_e]
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗ (muslErrnoAddr sf ↦₃₂ a_rest_1))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have ⟨h1_err, h2_err⟩ := dirReadErrnoNat_bounds a a_2
  wp_call_block hole2_muslSyscallRetErr_blk_ok (dirReadErrnoNat a a_2, a_rest_1)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1] at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], dirReadErrno32_cases a a_2,
      dirReadErrno32_ne_eintr a a_2, by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [dirReadErrno32, muslErrnoAddr, wp_norm, arm64_norm, *] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private def hole2_muslSccpReadFileOrStdioSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × FdEntry × List (BitVec 8)) where
  pre := fun (fd, buf, count, desc, oldBuf) s0 =>
    ⌜s0.readReg64 .x0 = 63#64 ∧
      (s0.readReg32 .x1).zeroExtend 64 = fd ∧
      fd.toNat < 2 ^ 31 ∧
      s0.readReg64 .x2 = buf ∧
      s0.readReg64 .x3 = count ∧
      count.toNat ≤ Arm64.MAX_RW_COUNT ∧
      buf.toNat + count.toNat ≤ Arm64.USER_VA_LIMIT ∧
      (desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE) ∧
      oldBuf.length = count.toNat ∧
      s0.fs.fds fd = some desc ∧
      (desc.kind == .localFile || desc.kind == .stdio) = true ∧
      desc.accMode.canRead = true⌝ ∗
    (buf ↦ₛ oldBuf)
  post := fun (fd, buf, count, desc, oldBuf) s0 sf =>
    let chunk := ((s0.fs.fdBytes desc).drop desc.offset).take count.toNat
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 chunk.length ∧
      sf.fs = s0.fs.setFd fd (some { desc with offset := desc.offset + chunk.length }) ∧
      sf.trace = s0.trace ∧
      SyscallPreserved s0 sf⌝ ∗
    (buf ↦ₛ (chunk ++ oldBuf.drop chunk.length))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_muslSccpReadFileOrStdio_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 3)
      (hole2_musl9Lib.resolve hole2_muslFullMpl "__syscall_cp")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl hole2_muslSccpReadFileOrStdioSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from hole2_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show hole2_musl9Lib.resolve hole2_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  refine hole2_muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine SepWP.step_svc_read (fd := a_1) (buf := a) (count := a_2) (desc := a_3) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x0 = 63#64›])
    (by simpa [wp_norm, arm64_norm] using ‹(s0.readReg32 .x1).zeroExtend 64 = a_1›)
    ‹a_1.toNat < 2 ^ 31›
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x2 = a›])
    (by simp [wp_norm, arm64_norm, ‹s0.readReg64 .x3 = a_2›])
    ‹a_rest_1.length = a_2.toNat›
    ‹s0.fs.fds a_1 = some a_3›
    ‹(a_3.kind == .localFile || a_3.kind == .stdio) = true›
    ‹a_3.accMode.canRead = true› ?_
    (by simp [wp_norm, arm64_norm, Reg.x8, execRead, ‹s0.readReg64 .x0 = 63#64›])
    ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    ‹a.toNat + a_2.toNat ≤ Arm64.USER_VA_LIMIT›
    ‹a_3.kind = .localFile → a_3.offset + a_2.toNat ≤ Arm64.MAX_LFS_FILESIZE›
  dsimp only; rw [sepConj_emp]
  (conv => arg 3; simp only [wp_norm, arm64_norm])
  (conv => arg 4; simp only [wp_norm, arm64_norm, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x8])
  wp_sym_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp [wp_norm, arm64_norm], by cases a_3; simp_all [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], rfl, rfl, rfl, rfl, rfl,
      fun _ => by simp [wp_norm, arm64_norm]⟩, by simpa using hmem⟩
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem hole2_muslReadFileOrStdio32_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 6)
      (hole2_musl9Lib.fnAddr hole2_muslFullMpl "read")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl muslReadFileOrStdio32Spec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 6 =
    muslSysPC06.rebase muslSysPl06.base (fun _ => none) from hole2_musl9_blockProgram_eq 6 muslSysLib06 muslSysPl06 rfl rfl]
  rw [show hole2_musl9Lib.fnAddr hole2_muslFullMpl "read" = muslSysPl06.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps
  wp_call_block_keep hole2_muslSccpReadFileOrStdio_blk_ok (a_1, a, a_2, a_3, a_rest_1)
  rcases ‹SyscallPreserved _ _› with ⟨htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
  simp only [wp_norm, arm64_norm, hm1] at htp1 hsig1 hb1 hbs1 hp1 hmp1
  wp_cut_codeLoaded; wp_sym_steps
  apply SepWP.weaken_pre (P' := stackAt s0.sp 32 ∗
    (a ↦ₛ (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat ++
      a_rest_1.drop (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)))
  · rw [show stackAt s0.sp 32 = stackAt (s0.sp - 16#64) 16 ∗ cells (s0.sp - 16#64) 2 from
      stackAt_split_cells s0.sp 16 2 (by decide)]
    cells_unfold; simp only [wp_norm, arm64_norm]; sep_frame
  have hchunk_lt : (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length < 2 ^ 63 := by
    simp only [List.length_take]
    have := ‹a_2.toNat ≤ Arm64.MAX_RW_COUNT›
    simp only [Arm64.MAX_RW_COUNT] at this
    omega
  have hchunk_ok := ofNat64_le_maxSyscallOk hchunk_lt
  wp_call_block hole2_muslSyscallRetOk_blk_ok
    (BitVec.ofNat 64 (((s0.fs.fdBytes a_3).drop a_3.offset).take a_2.toNat).length)
  rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
  simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1, hmp1]
    at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
  apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
  refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
  · first | rw [satisfies_pure_sepConj] | rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, *], ?_, by simp [wp_norm, arm64_norm, *], ?_⟩,
      ProofLib.Satisfies.of_entails hmem ?_⟩
    · simp_all [wp_norm, arm64_norm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm] at *; sep_frame
  · unfold CalleeSavedPreserved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private def hole2_muslSccpOpenatLocalExecSpec :
    Spec (BitVec 64 × String × BitVec 32 × FsState × List TraceEvent × OpenatLocalOutcome) where
  pre := fun (cstr, path, flags, fs0, tr0, out) s0 =>
    ⌜s0.readReg64 .x0 = 56#64 ∧
      s0.readReg32 .x1 = AT_FDCWD_W32 ∧
      s0.readReg64 .x2 = cstr ∧
      s0.readReg32 .x3 = flags ||| O_LARGEFILE_W32 ∧
      s0.fs = fs0 ∧
      s0.trace = tr0 ∧
      ValidCPath path ∧
      OpenatLocalExecSpec fs0 tr0 path flags out⌝ ∗
    (cstr ↦ₛ cstrBytes path)
  post := fun (cstr, path, _, fs0, tr0, out) s0 sf =>
    match out with
    | .ok fd desc fs' traceExtra =>
      ⌜sf.readReg64 .x0 = fd ∧
        fd.toNat < 2 ^ 31 ∧
        fs'.fds fd = some desc ∧
        (desc.kind = .localFile ∨ desc.kind = .localDir) ∧
        desc.cloexec = true ∧
        sf.fs = fs' ∧
        sf.mem = s0.mem ∧
        sf.trace = tr0 ++ traceExtra ∧
        SyscallPreserved s0 sf⌝ ∗
      (cstr ↦ₛ cstrBytes path)
    | .err errPred =>
      ∃∗ errno : Nat,
        ⌜sf.readReg64 .x0 = -BitVec.ofNat 64 errno ∧
          1 ≤ errno ∧ errno ≤ 4095 ∧ errPred errno ∧
          sf.fs = fs0 ∧
          sf.mem = s0.mem ∧
          sf.trace = tr0 ∧
          SyscallPreserved s0 sf⌝ ∗
        (cstr ↦ₛ cstrBytes path)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem hole2_muslSccpOpenatLocalExec_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 3)
      (hole2_musl9Lib.resolve hole2_muslFullMpl "__syscall_cp")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl hole2_muslSccpOpenatLocalExecSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 3 =
    muslSysPC03.rebase muslSysPl03.base (fun _ => none) from hole2_musl9_blockProgram_eq 3 muslSysLib03 muslSysPl03 rfl rfl]
  rw [show hole2_musl9Lib.resolve hole2_muslFullMpl "__syscall_cp" = muslSysPl03.base from rfl]
  wp_entry
  obtain ⟨hlen_p, hval_p⟩ := h_8
  refine hole2_muslSyscallCp_step hpc hrun h ?_
  rw [← sepConj_emp (_ ↦ₛ _)]
  refine step_svc_openat_rw (path := a) (fname := a_1) rfl
    (by simp [wp_norm, arm64_norm, hrun])
    (by conv => lhs; simp (config := { decide := true }) only [arm64_norm])
    (by simp [wp_norm, arm64_norm, h_2]) (by simp [wp_norm, arm64_norm, h_4])
    hlen_p hval_p (fun hcs => ?_)
    (by simp [wp_norm, arm64_norm, Reg.x8, h_2])
  rw [sepConj_emp]
  have hexec := h_1 hcs (by simp [wp_norm, arm64_norm, h_6]) (by simp [wp_norm, arm64_norm, h_7])
    (by simpa [wp_norm, arm64_norm] using h_3) (by simpa [wp_norm, arm64_norm] using h_5)
  cases a_rest with
  | ok fd desc fs' traceExtra =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨hfd_lt, hfds, hkind, hclo, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [hole2_muslSccpOpenatLocalExecSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], hfd_lt, hfds, hkind, hclo,
        by simp [wp_norm, arm64_norm, State.appendTrace], rfl,
        by simp [wp_norm, arm64_norm, State.appendTrace, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [wp_norm, arm64_norm, State.appendTrace, Arm64.calleeSavedVRegs]
  | err errPred =>
    dsimp only [OpenatLocalExecSpec] at hexec
    rcases hexec with ⟨errno, h1, h2, hpred, hexec_eq⟩
    (conv => arg 3; rw [hexec_eq]; simp only [wp_norm, arm64_norm])
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · dsimp only [hole2_muslSccpOpenatLocalExecSpec]
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨by simp [wp_norm, arm64_norm], h1, h2, hpred,
        by simp [wp_norm, arm64_norm, h_6], rfl,
        by simp [wp_norm, arm64_norm, h_7], rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩,
        by simpa using hmem⟩
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm]

private theorem hole2_truncate32_and64 (x y : BitVec 64) :
    (x &&& y).truncate 32 = x.truncate 32 &&& y.truncate 32 := by ext i hi; simp

private theorem hole2_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    fd.getLsbD 31 = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow hfd

private theorem hole2_truncate32_getLsbD_31_false_of_lt {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd.truncate 32).getLsbD 31 = false := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hole2_getLsbD_31_false_of_lt hfd]; decide

private theorem hole2_mask32_or_zero_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 ||| 0#64) = fd := by
  simp only [BitVec.ushiftRight_zero, BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem hole2_setWidth64_setWidth32_and_mask_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 fd) &&& 4294967295#64 = fd := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
  rw [h1]
  simpa [BitVec.ushiftRight_zero, BitVec.or_zero] using hole2_mask32_or_zero_of_lt31 hfd

private theorem hole2_sxtw64_eq_self_of_lt31 {fd : BitVec 64} (hfd : fd.toNat < 2 ^ 31) :
    (fd >>> 0 &&& 4294967295#64 |||
      (if fd.getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = fd := by
  rw [hole2_getLsbD_31_false_of_lt hfd]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero, BitVec.ushiftRight_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change fd.toNat &&& (2 ^ 32 - 1) = fd.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]

private theorem hole2_neg_ofNat_toNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).toNat = 2 ^ 64 - err := by
  rw [BitVec.toNat_neg, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem hole2_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    (-BitVec.ofNat 64 err).getLsbD 31 = true := by
  rw [BitVec.getLsbD, hole2_neg_ofNat_toNat h1 h2, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 ^ 64 - err) / 2 ^ 31 = 2 ^ 33 - 1 := by omega
  rw [hdiv]; decide

private theorem hole2_truncate32_getLsbD_31_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err).truncate 32).getLsbD 31 = true := by
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hole2_getLsbD_31_neg_ofNat h1 h2]; decide

private theorem hole2_sxtw_neg_of_hi_ones {v : BitVec 64} (h : v >>> 32 = 0xffffffff#64) :
    (v >>> 0 &&& 4294967295#64 ||| 0xffffffffffffffff#64 &&& 0xffffffff00000000#64) = v := by
  bv_robdd

private theorem hole2_sxtw64_neg_ofNat {err : Nat} (h1 : 1 ≤ err) (h2 : err ≤ 4095) :
    ((-BitVec.ofNat 64 err) >>> 0 &&& 4294967295#64 |||
      (if (-BitVec.ofNat 64 err).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) = -BitVec.ofNat 64 err := by
  rw [hole2_getLsbD_31_neg_ofNat h1 h2]
  simp only [↓reduceIte]
  refine hole2_sxtw_neg_of_hi_ones (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_ushiftRight, hole2_neg_ofNat_toNat h1 h2, Nat.shiftRight_eq_div_pow]
  have hmax : (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  rw [hmax]; omega

private theorem hole2_zeroExtend64_getLsbD_6 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 6 = flags.getLsbD 6 := by simp

private theorem hole2_zeroExtend64_getLsbD_19 {flags : BitVec 32} :
    (flags.zeroExtend 64).getLsbD 19 = flags.getLsbD 19 := by simp

private theorem hole2_tmpfile_mask_eq_zero {flags : BitVec 32} (h : flags &&& 0x00404000#32 = 0#32) :
    (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = 0#32 := by
  have heq : (flags &&& 0x007fc000#32) &&& 0xffc07fff#32 = flags &&& 0x00404000#32 := by bv_bits
  rw [heq, h]

private theorem hole2_or_largefile_sxtw_truncate32 (flags : BitVec 32) :
    (((flags.zeroExtend 64 ||| 131072#64) >>> 0 &&& 4294967295#64 |||
      (if (flags.zeroExtend 64 ||| 131072#64).getLsbD 31 = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64).truncate 32) = flags ||| O_LARGEFILE_W32 := by
  rw [sxtw64_truncate32]
  change (flags.zeroExtend 64 ||| 131072#64).truncate 32 = flags ||| 0x00020000#32
  bv_bits

set_option maxHeartbeats 400000 in
private theorem hole2_muslOpenNoCreatCloexecLocalExec_blk_ok :
    subroutine_ok (hole2_musl9Lib.blockProgram hole2_muslFullMpl 8)
      (hole2_musl9Lib.fnAddr hole2_muslFullMpl "open")
      (hole2_musl9Lib.withCodeLoaded hole2_muslFullMpl muslOpenNoCreatCloexecLocalExecSpec) := by
  rw [show hole2_musl9Lib.blockProgram hole2_muslFullMpl 8 =
    muslSysPC08.rebase muslSysPl08.base (fun _ => none) from hole2_musl9_blockProgram_eq 8 muslSysLib08 muslSysPl08 rfl rfl]
  rw [show hole2_musl9Lib.fnAddr hole2_muslFullMpl "open" = muslSysPl08.base from rfl]
  wp_entry
  wp_conv_pre =>
    rw [show stackAt s0.sp 112 = stackAt (s0.sp - 80#64) 32 ∗ cells (s0.sp - 80#64) 10 from
      stackAt_split_cells s0.sp 32 10 (by decide)]
  cells_unfold; simp only [sepExists_sepConj_left, sepConj_assoc]
  repeat (apply SepWP.exists_left; intro)
  wp_cut_codeLoaded
  apply step_stp64_perm; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· wp_norm_lhs); (· rfl); (· rfl)
  (· wp_sep_access); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm1
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm1
  wp_sym_steps 1
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm2
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm2
  wp_sym_steps 1
  apply step_str64_perm_c; (· wp_norm_lhs); (· wp_norm_lhs); (· wp_norm_lhs)
  (· first | wp_norm_lhs | wp_norm_goal); (· wp_norm_lhs); (· rfl); (· wp_sep_access); (· wp_norm_lhs)
  intro _ hm3
  try simp only [State.mem_writeReg64, State.mem_writeReg32, State.mem_setPState,
    State.mem_advancePC, State.mem_setPC, State.mem_setMem] at hm3
  (conv => arg 3; simp only [wp_norm, arm64_norm, h_3, hole2_zeroExtend64_getLsbD_6, h_4])
  wp_sym_steps 3
  have htmp := hole2_tmpfile_mask_eq_zero h_5
  (conv => arg 3; simp only [wp_norm, arm64_norm, hole2_truncate32_and64, h_3, htmp])
  wp_sym_steps
  have hcwd : (-100#32 : BitVec 32) = AT_FDCWD_W32 := by decide
  have hflg := hole2_or_largefile_sxtw_truncate32 a_2
  have ⟨_, _⟩ := ‹ValidCPath a›
  wp_call_block_keep hole2_muslSccpOpenatLocalExec_blk_ok (a_1, a, a_2, s0.fs, s0.trace, a_rest_1)
  cases a_rest_1 with
  | ok fd desc fs' traceExtra =>
    wp_conv_pre => try dsimp only [hole2_muslSccpOpenatLocalExecSpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hx0, hfd_lt, hfds, hkind, hclo, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsvc08 : muslSysPC08.svc = Syscall.standard := rfl
    have hsxtw := hole2_sxtw64_eq_self_of_lt31 hfd_lt
    have hmask0 := hole2_mask32_or_zero_of_lt31 hfd_lt
    have hfd_ze_mask := hole2_setWidth64_setWidth32_and_mask_of_lt31 hfd_lt
    have hfd_ze : BitVec.setWidth 64 (BitVec.setWidth 32 fd) = fd := by bv_omega
    have htbnz := hole2_getLsbD_31_false_of_lt hfd_lt
    have htbnz32 := hole2_truncate32_getLsbD_31_false_of_lt hfd_lt
    wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, hmask0, htbnz, htbnz32])
    wp_sym_steps 2
    simp only [wp_norm, arm64_norm, hole2_zeroExtend64_getLsbD_19, h_6]
    have hdesc_eq : ({ desc with cloexec := true } : FdEntry) = desc := by
      cases desc; simp at hclo; subst hclo; rfl
    have hsetfd_eq : fs'.setFd fd (some { desc with cloexec := true }) = fs' := by
      rw [hdesc_eq]; exact FsState.setFd_eq_self hfds
    have h1_clo : (1#64 &&& 1#64 != 0#64) = true := by decide
    wp_sym_steps
    refine step_svc_fcntl_setfd_local (fd := fd) (arg := 1#64) rfl
      (by simp [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hfd_ze]) hfd_lt
      (by simp [wp_norm, arm64_norm, F_SETFD_W32]) (by simp [wp_norm, arm64_norm])
      (by simpa [wp_norm, arm64_norm, hfs1] using hfds) hkind ?_
      (by simp [wp_norm, arm64_norm, *])
    dsimp only
    (conv => arg 3; simp only [wp_norm, arm64_norm, hfs1, h1_clo, hsetfd_eq])
    wp_sym_steps
    have hfd_ok : fd.toNat ≤ 2 ^ 64 - 4096 := by omega
    wp_cut_codeLoaded
    wp_call_block hole2_muslSyscallRetOk_blk_ok fd
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp [wp_norm, arm64_norm, *], by simp_all [wp_norm, arm64_norm],
        by simp_all [wp_norm, arm64_norm], ?_⟩, ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]
  | err errPred =>
    wp_conv_pre => try dsimp only [hole2_muslSccpOpenatLocalExecSpec]; simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro errno
    apply SepWP.pure_elim
    rintro ⟨hx0, h1, h2, hpred, hfs1, hmem1, htr1, htp1, hsig1, hb1, hbs1, hp1, hmp1⟩
    try simp only [wp_norm, arm64_norm, *] at htp1 hsig1 hb1 hbs1 hp1 hmp1
    have hsxtw := hole2_sxtw64_neg_ofNat h1 h2
    have htbnz := hole2_getLsbD_31_neg_ofNat h1 h2
    have htbnz32 := hole2_truncate32_getLsbD_31_neg_ofNat h1 h2
    have htp_e : muslErrnoAddr s0 = muslErrnoAddr sf := by unfold muslErrnoAddr; rw [htp1]
    wp_conv_pre => rw [htp_e]
    wp_cut_codeLoaded; wp_sym_steps 1
    (conv => arg 3; simp only [wp_norm, arm64_norm, hx0, hsxtw, htbnz, htbnz32])
    wp_sym_steps
    wp_call_block hole2_muslSyscallRetErr_blk_ok (errno, a_3)
    rcases ‹StdStatePreserved _ _› with ⟨hfs2, htr2, htp2, hsig2, hb2, hbs2, hp2, hmp2⟩
    try simp only [wp_norm, arm64_norm, htp1, hsig1, hb1, hbs1, hp1]
      at hfs2 htr2 htp2 hsig2 hb2 hbs2 hp2 hmp2
    wp_sym_steps
    apply SepWP.done (by simp [wp_norm, arm64_norm, *]) (by simp [wp_norm, arm64_norm, *])
    refine ⟨fun hmem => ?_, by simp [wp_norm, arm64_norm, *], ?_⟩
    · try dsimp only [muslOpenNoCreatCloexecLocalExecSpec]
      try rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨errno, ?_⟩
      try rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨h1, h2, hpred, by simp [wp_norm, arm64_norm, *],
        by simp [wp_norm, arm64_norm, *], by simp [wp_norm, arm64_norm, *], ?_⟩,
        ProofLib.Satisfies.of_entails hmem ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> simp [wp_norm, arm64_norm, *]
      · rw [show stackAt (State.sp s0) 112 =
            stackAt (State.sp s0 - 80#64) 32 ∗ cells (State.sp s0 - 80#64) 10 from
          stackAt_split_cells (State.sp s0) 32 10 (by decide)]
        cells_unfold; simp only [wp_norm, arm64_norm, muslErrnoAddr, *]; sep_frame
    · unfold CalleeSavedPreserved
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [wp_norm, arm64_norm, *]

private theorem hole2_f3Rx_hooksUnfetched (m : Memory) (_ : f3TrialRxProg.CodeLoaded m) :
    f3TrialRxProg.HooksUnfetched m :=
  fun _ pc _ he => False.elim (he (f3TrialRxProg_no_ext pc))

private theorem hole2_muslErrnoLocation_ok :
    subroutine_ok f3TrialRxProg 0x46ba94#64 muslErrnoLocationSpec := by
  have hfn : hole2_musl9Lib.fnAddr hole2_muslFullMpl "___errno_location" = 0x46ba94#64 := by decide
  rw [← hfn]
  exact hole2_musl9Lib.subroutine_ok_of_pureMem (j := 0) (by decide) hole2_muslErrnoLocation_blk_ok
    hole2_progContainsMusl9.codeLoaded hole2_f3Rx_hooksUnfetched f3TrialRxProg_svc

private theorem hole2_muslClose48Local_ok :
    subroutine_ok f3TrialRxProg 0x46e1fc#64 muslClose48LocalSpec := by
  have hfn : hole2_musl9Lib.fnAddr hole2_muslFullMpl "close" = 0x46e1fc#64 := by decide
  rw [← hfn]
  exact hole2_musl9Lib.subroutine_ok_of_pureMem (j := 5) (by decide) hole2_muslClose48Local_blk_ok
    hole2_progContainsMusl9.codeLoaded hole2_f3Rx_hooksUnfetched f3TrialRxProg_svc

private theorem hole2_muslReadDir32_ok :
    subroutine_ok f3TrialRxProg 0x46e240#64 muslReadDir32Spec := by
  have hfn : hole2_musl9Lib.fnAddr hole2_muslFullMpl "read" = 0x46e240#64 := by decide
  rw [← hfn]
  exact hole2_musl9Lib.subroutine_ok_of_pureMem (j := 6) (by decide) hole2_muslReadDir32_blk_ok
    hole2_progContainsMusl9.codeLoaded hole2_f3Rx_hooksUnfetched f3TrialRxProg_svc

private theorem hole2_muslReadFileOrStdio32_ok :
    subroutine_ok f3TrialRxProg 0x46e240#64 muslReadFileOrStdio32Spec := by
  have hfn : hole2_musl9Lib.fnAddr hole2_muslFullMpl "read" = 0x46e240#64 := by decide
  rw [← hfn]
  exact hole2_musl9Lib.subroutine_ok_of_pureMem (j := 6) (by decide) hole2_muslReadFileOrStdio32_blk_ok
    hole2_progContainsMusl9.codeLoaded hole2_f3Rx_hooksUnfetched f3TrialRxProg_svc

private theorem hole2_muslOpenNoCreatCloexecLocalExec_ok :
    subroutine_ok f3TrialRxProg 0x46bb24#64 muslOpenNoCreatCloexecLocalExecSpec := by
  have hfn : hole2_musl9Lib.fnAddr hole2_muslFullMpl "open" = 0x46bb24#64 := by decide
  rw [← hfn]
  exact hole2_musl9Lib.subroutine_ok_of_pureMem (j := 8) (by decide)
    hole2_muslOpenNoCreatCloexecLocalExec_blk_ok
    hole2_progContainsMusl9.codeLoaded hole2_f3Rx_hooksUnfetched f3TrialRxProg_svc

private theorem hole2_muslReadStdin32_ok :
    subroutine_ok f3TrialRxProg 0x46e240#64 muslReadStdin32Spec := by
  apply Arm64.subroutine_ok.of_codeLoaded
  rintro ⟨buf, count, desc, oldBuf⟩ R s0 hpc hrun hpre hsp _hL
  simp only [muslReadStdin32Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcnt_le, hva_le, hlen, hfds0, hkind, hrd⟩, hm⟩
  have hx0_ze : (s0.readReg32 .x0).zeroExtend 64 = 0#64 := by rw [hx0]; rfl
  have h0_lt : (0#64 : BitVec 64).toNat < 2 ^ 31 := by decide
  have hk_or : (desc.kind == .localFile || desc.kind == .stdio) = true := by rw [hkind]; rfl
  have hlfs : desc.kind = .localFile → desc.offset + count.toNat ≤ Arm64.MAX_LFS_FILESIZE := by
    rw [hkind]; intro h; cases h
  have hfdbytes : s0.fs.fdBytes desc = s0.fs.stdin := by simp only [FsState.fdBytes, hkind]
  refine hole2_muslReadFileOrStdio32_ok.mono_outcome (0#64, buf, count, desc, oldBuf) R s0 hpc hrun
    ?_ hsp (fun sf hout => ?_)
  · simp only [muslReadFileOrStdio32Spec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_ze, h0_lt, hx1, hx2, hcnt_le, hva_le, hlfs, hlen, hfds0, hk_or, hrd⟩, hm⟩
  · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [muslReadFileOrStdio32Spec, muslReadStdin32Spec, hfdbytes] using hq
    · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))

private theorem hole2_setFs_appendTrace_nil (s : State) (fs' : FsState) :
    (s.setFs fs').appendTrace [] = s.setFs fs' := by
  cases s; simp only [State.setFs, State.appendTrace, List.append_nil]

private theorem hole2_execOpenat_rdonly_cloexec_err_anc {s : State} {path : String}
    {err : BitVec 64}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = some err) :
    execOpenat s = (s.writeReg64 .x0 (-err)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  rw [ProofLib.ancestorWalkErrno_eq_strict] at hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_cr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres]
  cases hsanc : strictAncestorWalkErrno? s.fs path with
  | some e =>
    rw [hsanc] at hanc
    injection hanc with he; subst he; rfl
  | none =>
    rw [hsanc] at hanc
    cases hlast : ((splitSlash path).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) with
    | true =>
      rw [hlast] at hanc
      simp only [↓reduceIte, Option.some.injEq] at hanc
      subst hanc; rfl
    | false =>
      rw [hlast] at hanc; cases hanc

private theorem hole2_execOpenat_rdonly_cloexec_missing {s : State} {path : String}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hnone : s.fs.files path = none) :
    execOpenat s = (s.writeReg64 .x0 (-ENOENT)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = none := hnone
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_cr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge]
  simp

private theorem hole2_execOpenat_rdonly_cloexec_emfile_dir {s : State} {path : String}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hdir : s.fs.files path = some .dir)
    (halloc : s.fs.allocFd = none) :
    execOpenat s = (s.writeReg64 .x0 (-EMFILE)).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hrd_ne : (FdAccessMode.rdonly != FdAccessMode.rdonly) = false := rfl
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some .dir := hdir
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_tr, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, hrd_ne, halloc]
  simp

private theorem hole2_execOpenat_rdonly_cloexec_file_or_emfile {s : State} {path : String}
    {bs : List (BitVec 8)}
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path)
    (hne : path.isEmpty = false)
    (hlead : hasLeadingSlash path = false)
    (hdot : hasDotDot path = false)
    (htd : trailingDir path = false)
    (hnorm_ne : normalizePath path ≠ [])
    (hanc : ancestorWalkErrno? s.fs path = none)
    (hfile : s.fs.files path = some (.file bs)) :
    execOpenat s =
      match s.fs.allocFd with
      | none => (s.writeReg64 .x0 (-EMFILE)).advancePC
      | some fd =>
        ((s.setFs (s.fs.setFd fd (some
            { path := path, accMode := .rdonly, append := false, cloexec := true,
              offset := 0, kind := .localFile }))).writeReg64 .x0 fd).advancePC := by
  have hf_bad : (((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& ~~~OPENAT_KNOWN_MASK) != 0#32 ||
      ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32) == 3#32) = false := by decide
  have hf_m0 : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& 3#32 == 0#32) = true := by decide
  have hf_cr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CREAT_W32 != 0#32) = false := by decide
  have hf_tr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_TRUNC_W32 != 0#32) = false := by decide
  have hf_ap : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_APPEND_W32 != 0#32) = false := by decide
  have hf_dr : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_DIRECTORY_W32 != 0#32) = false := by decide
  have hf_cl : ((O_LARGEFILE_W32 ||| O_CLOEXEC_W32) &&& O_CLOEXEC_W32 != 0#32) = true := by decide
  have hres : resolveCwdPath AT_FDCWD_W32 path = .ok (normalizePath path) := by
    simp [resolveCwdPath, hne, hlead, hdot]
  have hge : s.fs.getEntry (normalizePath path) = some (.file bs) := hfile
  have hself : s.fs.setEntry (normalizePath path) (some (.file bs)) = s.fs :=
    FsState.setEntry_self_of_nonEmpty hnorm_ne hge
  obtain ⟨hsanc, hlast⟩ := ProofLib.strictAncestorWalkErrno_of_none hanc
  dsimp only [execOpenat, checkOpenFlags, openatPure, applyOpenVerdict]
  rw [hdfd, hflags, hf_bad, hf_m0, hf_cr, hf_tr, hf_ap, hf_dr, hf_cl, hcs]
  simp only [Bool.false_eq_true, Bool.false_and, Bool.and_false, ↓reduceIte]
  rw [hres, hsanc]
  dsimp only
  rw [hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hge, htd]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  cases s.fs.allocFd with
  | none => rfl
  | some fd => simp [hself]

private abbrev _root_.Arm64.Process.FsEntry := _root_.Arm64.FsEntry

private theorem hole2_classifyOpenRdonly_err_of_none_some
    (fs : FsState) (path : String) (e : Arm64.Process.FsEntry) {errno : Nat}
    (hb : blockingAncestor? fs path = none)
    (hf : fs.files path = some e)
    (hcl : classifyOpenRdonly fs path = .err errno) :
    fs.allocFd = none ∧ errno = 24 := by
  unfold classifyOpenRdonly at hcl
  rw [hb, hf] at hcl
  cases ha : fs.allocFd with
  | none =>
    rw [ha] at hcl
    cases e <;> (dsimp only at hcl; injection hcl with he; exact ⟨rfl, he.symm⟩)
  | some fd =>
    rw [ha] at hcl
    cases e <;> nomatch hcl

private theorem hole2_execOpenat_of_classifyOpenRdonly_err {s : State} {path : String} {errno : Nat}
    (hpok : PathOk path = true)
    (hmax : ((pathComps path).all fun c => decide (c.length ≤ NAME_MAX)) = true)
    (hcl : classifyOpenRdonly s.fs path = .err errno)
    (hdfd : s.readReg32 .x0 = AT_FDCWD_W32)
    (hflags : s.readReg32 .x2 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32)
    (hcs : readCString s.mem (s.readReg64 .x1) = .ok path) :
    execOpenat s = (s.writeReg64 .x0 (-BitVec.ofNat 64 errno)).advancePC := by
  have hcs_ne := pathComps_ne_nil path
  have hg : ∀ c ∈ pathComps path, GoodComp c :=
    fun c hc => goodComp_of_mem_pathComps hpok hc
  have hp_eq := strOfComps_pathComps path
  have hne : path.isEmpty = false := isEmpty_false_of_pathOk hpok
  have hlead : hasLeadingSlash path = false := by
    rw [← hp_eq]; exact hasLeadingSlash_strOfComps hcs_ne hg
  have hdot : hasDotDot path = false := by
    rw [← hp_eq]; exact hasDotDot_strOfComps hcs_ne hg
  have htd : trailingDir path = false := trailingDir_false_of_pathOk hpok
  have hnorm_ne : normalizePath path ≠ [] := normalizePath_ne_nil_of_pathOk hpok
  have hanc_eq := ancestorWalkErrno?_eq_of_pathOk s.fs hpok hmax
  have hcl0 := hcl
  unfold classifyOpenRdonly at hcl
  cases hb : blockingAncestor? s.fs path with
  | some a =>
    rw [hb] at hcl hanc_eq
    cases a with
    | none =>
      have he : errno = 2 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
      subst he
      exact hole2_execOpenat_rdonly_cloexec_err_anc hdfd hflags hcs hne hlead hdot hanc_eq
    | some e =>
      cases e with
      | dir => exact absurd hb (blockingAncestor?_ne_some_dir s.fs path)
      | file _ =>
        have he : errno = 20 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
        subst he
        exact hole2_execOpenat_rdonly_cloexec_err_anc hdfd hflags hcs hne hlead hdot hanc_eq
  | none =>
    rw [hb] at hcl hanc_eq
    cases hf : s.fs.files path with
    | none =>
      rw [hf] at hcl
      have he : errno = 2 := by dsimp only at hcl; injection hcl with he'; exact he'.symm
      subst he
      exact hole2_execOpenat_rdonly_cloexec_missing hdfd hflags hcs hne hlead hdot hanc_eq hf
    | some e =>
      obtain ⟨ha, rfl⟩ := hole2_classifyOpenRdonly_err_of_none_some s.fs path e hb hf hcl0
      cases e with
      | dir =>
        exact hole2_execOpenat_rdonly_cloexec_emfile_dir hdfd hflags hcs hne hlead hdot hanc_eq hf ha
      | file bs =>
        have hexec := hole2_execOpenat_rdonly_cloexec_file_or_emfile hdfd hflags hcs hne hlead hdot
          htd hnorm_ne hanc_eq hf
        rw [ha] at hexec
        exact hexec

private theorem hole2_muslOpenRdonlyDet_ok :
    subroutine_ok f3TrialRxProg 0x46bb24#64 muslOpenRdonlyDetSpec := by
  apply Arm64.subroutine_ok.of_codeLoaded
  rintro ⟨cstr, path, e0⟩ R s0 hpc hrun hpre hsp _hL
  simp only [muslOpenRdonlyDetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpok, hmax, hlen, hlat⟩, hm⟩
  obtain ⟨hcp, hlead, hdot⟩ := validRelCPath_of_pathOk hpok hlen hlat
  have hne := isEmpty_false_of_pathOk hpok
  have htd := trailingDir_false_of_pathOk hpok
  have hnorm_ne := normalizePath_ne_nil_of_pathOk hpok
  have hb6 : O_CLOEXEC_W32.getLsbD 6 = false := by decide
  have htmp : O_CLOEXEC_W32 &&& 0x00404000#32 = 0#32 := by decide
  have hb19 : O_CLOEXEC_W32.getLsbD 19 = true := by decide
  have hfl_eq : O_CLOEXEC_W32 ||| O_LARGEFILE_W32 = O_LARGEFILE_W32 ||| O_CLOEXEC_W32 := by decide
  cases hcl : classifyOpenRdonly s0.fs path with
  | ok fd kind =>
    obtain ⟨hb_none, halloc, _, hfd_max, _, hkind_cases⟩ := classifyOpenRdonly_ok_spec hcl
    have hfd_lt : fd.toNat < 2 ^ 31 := by
      have hmmax : FsState.maxOpenFds = 1024 := rfl
      rw [hmmax] at hfd_max
      have h1024_lt : (1024 : Nat) < 2 ^ 31 := by decide
      exact Nat.lt_trans hfd_max h1024_lt
    have hanc_none : ancestorWalkErrno? s0.fs path = none := by
      rw [ancestorWalkErrno?_eq_of_pathOk s0.fs hpok hmax, hb_none]
    let desc : FdEntry :=
      { path := path, accMode := .rdonly, append := false, cloexec := true,
        offset := 0, kind := kind }
    let fs' : FsState := s0.fs.setFd fd (some desc)
    refine hole2_muslOpenNoCreatCloexecLocalExec_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .ok fd desc fs' []) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      rcases hkind_cases with ⟨rfl, hdir⟩ | ⟨rfl, bs, hfile⟩
      · have hexec := execOpenat_rdonly_cloexec_dir hs_x0 (hfl_eq ▸ hs_x2) hcs hne hlead hdot
          (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hdir) (hs_fs.symm ▸ halloc)
        rw [hs_fs] at hexec
        refine ⟨hfd_lt, by simp only [fs', FsState.setFd, beq_self_eq_true, ↓reduceIte], Or.inr rfl, rfl, ?_⟩
        rw [hole2_setFs_appendTrace_nil]; exact hexec
      · have hexec := hole2_execOpenat_rdonly_cloexec_file_or_emfile hs_x0 (hfl_eq ▸ hs_x2) hcs hne
          hlead hdot htd hnorm_ne (hs_fs.symm ▸ hanc_none) (hs_fs.symm ▸ hfile)
        rw [hs_fs, halloc] at hexec
        refine ⟨hfd_lt, by simp only [fs', FsState.setFd, beq_self_eq_true, ↓reduceIte], Or.inl rfl, rfl, ?_⟩
        rw [hole2_setFs_appendTrace_nil]; exact hexec
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simpa only [muslOpenNoCreatCloexecLocalExecSpec, muslOpenRdonlyDetSpec, hcl,
          List.append_nil] using hq
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))
  | err errno =>
    have herr_cases := classifyOpenRdonly_err_cases hcl
    have herr_bounds : 1 ≤ errno ∧ errno ≤ 4095 := by
      rcases herr_cases with rfl | rfl | rfl <;> decide
    refine hole2_muslOpenNoCreatCloexecLocalExec_ok.mono_outcome
      (cstr, path, O_CLOEXEC_W32, e0, .err (· = errno)) R s0 hpc hrun ?_ hsp (fun sf hout => ?_)
    · simp only [muslOpenNoCreatCloexecLocalExecSpec, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hb6, htmp, hb19, hcp, ?_⟩, hm⟩
      intro s hcs hs_fs _ hs_x0 hs_x2
      refine ⟨errno, herr_bounds.1, herr_bounds.2, rfl, ?_⟩
      exact hole2_execOpenat_of_classifyOpenRdonly_err hpok hmax (hs_fs.symm ▸ hcl) hs_x0
        (hfl_eq ▸ hs_x2) hcs
    · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex_st, hq⟩ | ⟨ho_st, hq⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        simp only [muslOpenNoCreatCloexecLocalExecSpec, muslOpenRdonlyDetSpec, hcl,
          sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
        rcases hq with ⟨errno', ⟨_, _, rfl, hx0', hfs', htr', hpres'⟩, hm_cells⟩
        exact ⟨⟨hx0', hfs', htr', hpres'⟩, hm_cells⟩
      · exact Or.inr (Or.inl ⟨hp_st, hq⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hq⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hq⟩))

/-! #### `signalSessionIoMultiLib` Placement and `readFile` / `readStdin` Discharges -/

private abbrev hole2_ioMpl : MultiPlacement :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen.h2fsreads_ioMpl

private theorem hole2_ioMpl_placeable :
    signalSessionIoMultiLib.Placeable hole2_ioMpl :=
  signalSessionIoMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

set_option maxRecDepth 400000 in
private theorem hole2_io_readsCodeLoaded :
    ∀ m : Memory, f3TrialRxProg.CodeLoaded m →
      LibsignalBinary.Proofs.SignalSession.CliIo.Sym.CliIoReadsCodeLoaded hole2_ioMpl m :=
  fun _ hCL =>
    LibsignalBinary.Proofs.SignalSession.CliIo.Sym.cliIoReadsCodeLoaded_of_blocks
      (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
        (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)
      (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
        (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)
      (codeLoaded_of_checkProgSliceInWordTree f3TrialRxWordTree_eq f3TrialRxWordTree_size
        (by rw [f3TrialRxProg_base]; rfl_kernel) hCL)

theorem hole2_readFileCond_ok
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg 0x4691b4#64
      (readFileAnyBudgetCondSpec
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) :=
  hole2_rf_readFile_cond_ok mmpl hMm γ tp

theorem hole2_readStdinCond_ok
    (mmpl : MultiPlacement) (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    subroutine_ok f3TrialRxProg 0x469000#64
      (readStdinBudgetCondSpec
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits extHookStack) := by
  have hres : signalSessionIoMultiLib.resolve hole2_ioMpl cliIoReadStdinSym = 0x469000#64 := by rfl
  have hread_a : signalSessionIoMultiLib.resolve hole2_ioMpl cliIoReadSym = 0x46e240#64 := by decide
  have hmemcpy_a : signalSessionIoMultiLib.resolve hole2_ioMpl cliIoMemcpySym = f3StdLayout.memcpyAddr := by
    decide
  have hshim_a : signalSessionIoMultiLib.resolve hole2_ioMpl cliIoRustNoAllocShimSym = 0x469640#64 := by
    decide
  have halloc_a :
      ({ alloc := signalSessionIoMultiLib.resolve hole2_ioMpl cliIoRustAllocSym
         dealloc := signalSessionIoMultiLib.resolve hole2_ioMpl cliIoRustDeallocSym
         realloc := signalSessionIoMultiLib.resolve hole2_ioMpl cliIoRustReallocSym } :
        LibsignalBinary.Heap.RustAllocAddrs) = f3StubAddrs := by
    rfl_kernel
  have hEntries := halloc_a ▸ hole2_stubEntries mmpl hMm γ tp
  rw [← hres]
  exact cliIoReadStdin_budgetCond_ok_of_readsCodeLoaded
    (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
    hole2_ioMpl_placeable (Nat.le_refl _) hole2_io_readsCodeLoaded
    (fun _ _ => f3TrialRxProg_no_ext _) (fun _ _ => f3TrialRxProg_no_ext _)
    (hread_a ▸ hole2_muslReadStdin32_ok)
    (hmemcpy_a ▸ f3Trial_allocMemcpyVm_ok)
    (hshim_a ▸ hole2_noAllocShim_ok)
    (hEntries.alloc cliBudgetLimits) (hEntries.realloc cliBudgetLimits)
    (hEntries.dealloc cliBudgetLimits)
    (fun hsat hmap =>
      LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase.fineHookRustCliAllocBudget_mapped_lt_userVa
        (by decide) hsat hmap)

theorem hole2_hioOf
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W)) cliIo hole2_hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp
  let P_sub := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
  let H := cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W)
  have hsvc_real : hole2_emptyProg.svc = Arm64.Syscall.standard := rfl
  have hsvc_sub : P_sub.svc = Arm64.Syscall.standard :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
  have hreal_no : ∀ pc, hole2_keepSub pc = true → hole2_emptyProg.externAt? pc = none :=
    fun _ _ => rfl
  have hsub_no : ∀ pc, P_sub.externAt? pc = none :=
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
  have hPl : mallocngLib.Placeable mmpl := hole2_hPl_mng mmpl hMm
  have hKeep : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keepSub a = true :=
    hole2_keepMallocng mmpl hMm
  have hstk : extHookStack ≤ hole2_hookStack := Nat.le_refl _
  exact
    { readStdin :=
        CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain <|
          CryptoVerification.ls_hook_ok_ultra_of_mem
            (prog := CryptoVerification.SignalSession.Cli.Main.Placed.lsProg_617 H) (i := 617)
            ⟨LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHookFine
              hole2_keepSub hole2_emptyProg P_sub (hole2_targets mpl).readStdin mmpl
              cliElfImage.brkStart cliBudgetLimits hole2_hookStack,
             CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readStdin_some
              (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) rfl,
             LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.f3ReadStdinGhostHookFine_ok_bounded
              hsvc_real hsvc_sub hreal_no hsub_no hPl hKeep hstk
              (hole2_readStdinCond_ok mmpl hMm) γ tp⟩
            (by decide)
      readFile :=
        CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain <|
          CryptoVerification.ls_hook_ok_ultra_of_mem
            (prog := CryptoVerification.SignalSession.Cli.Main.Placed.lsProg_617 H) (i := 617)
            ⟨LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFine
              hole2_keepSub hole2_emptyProg P_sub (hole2_targets mpl).readFile mmpl
              cliElfImage.brkStart cliBudgetLimits hole2_hookStack,
             CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readFile_some
              (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) rfl,
             LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFine_ok_lit
              hsvc_real hsvc_sub hreal_no hsub_no hPl hKeep hstk
              (hole2_readFileCond_ok mmpl hMm) γ tp⟩
            (by decide)
      writeFile :=
        CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain <|
          CryptoVerification.ls_hook_ok_ultra_of_mem
            (prog := CryptoVerification.SignalSession.Cli.Main.Placed.lsProg_617 H) (i := 617)
            ⟨CryptoVerification.SignalSession.writeFileHook,
             (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_other
              (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (CryptoVerification.SignalSession.Cli.MainHops.cliExternsPlaced_writeFile mmpl W),
             LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced.writeFileHook_ok_placed
              _ cliBudgetLimits hole2_hookStack⟩
            (by decide)
      writeStdout :=
        CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain <|
          CryptoVerification.ls_hook_ok_ultra_of_mem
            (prog := CryptoVerification.SignalSession.Cli.Main.Placed.lsProg_617 H) (i := 617)
            ⟨CryptoVerification.SignalSession.writeStdoutHook,
             (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_other
              (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (CryptoVerification.SignalSession.Cli.MainHops.cliExternsPlaced_writeStdout mmpl W),
             LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadStdinBudgetPlaced.writeStdoutHook_ok_placed
              _ cliBudgetLimits hole2_hookStack⟩
            (by decide) }

end Hole2SegcloneIoHelpers

section SegcHooksBundleHelpers

open Arm64 ProofLib ProofLib.StdStartup
open ProofLib.StdStartup.Stage1Internal (step_str64_perm)
open CryptoVerification (IsLsBlockProg lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.SignalSession (lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (IsFsC cliGhostExterns_readFile_some cliGhostExterns_stringClone_some)
open LibsignalBinary.Heap (AllocCallPreserved AllocCostModel BudgetLimits FitsEvents
  NullAllowed OomPreserved PoolPreserved RustCliAllocBudget RustLayoutOk VmPreserved
  not_nullAllowed_of_fitsAllocEvents rustAllocEvents rustCliAllocBudgetSpecBase)
open LibsignalBinary.Heap.Fine (f3NoShimV2Addr f3RdlAddrs f3RxWordCount f3StubNoShimAddr)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec extHookStack_split_48
  rustAllocShimVmSpec stringCloneBudgetCondSpec stringCloneBudgetSpec stringCloneEvents
  stringCloneNoOomSpec)
open LibsignalBinary.Proofs.Common.StringCloneFlat (rustStringCloneInstrs)
open LibsignalBinary.Proofs.Common.StringClonePlaced (blkLib_623 blkLib_eq_623 instIsLsBlockProg_623
  lsHandleErrorPlacedSym lsProg_623 lsProg_623_hasInstrs lsRustAllocPlacedSym
  lsRustNoAllocShimPlacedSym)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk (cliRunHooksPlaced_of_ghost)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen
  SpecPreservesFsTrace SpecStripSInvariant
  keepFsTrace keepFsTrace_fsT real_subroutine_run_of_stripS
  satisfies_of_stripExecOutside satisfies_stripExecOutside specPreservesFsTrace_alloc
  standard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook
  (f3ReadFileFixedGhostHookFine f3ReadFileFixedGhostHookFine_ok_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (ActiveF3CallPre
  f3StringCloneFallback f3StringCloneFallback_ok_noOom_fine hookOk_stringCloneBudget_of_noOom
  specPreservesFsTrace_stringCloneNoOom specStripSInvariant_fine_alloc
  specStripSInvariant_fine_stringCloneNoOom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (cliRunHooksBundle_of_hookSat_mono_stk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (f3HandleErrorIdx
  f3LsBlockBases f3LsBlockBases_len f3LsBlocksLen f3LsSymAddrs libsignalBlocks_len
  lsInternedMultiLib ls_idsOk ls_names_nodup ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
  (f3CliElf_libsignal_inElf_unique f3CliElf_libsignal_placed f3CliElf_rho_handleError_eq_of_linkedAt
   f3CliElf_rho_noAllocShim_of_linkedAt f3HandleErrorSym f3LsMpl f3TrialElf f3TrialElf_parse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3RxSegBase f3TrialRxProg
  f3TrialRxProg_base f3TrialRxProg_no_ext f3TrialRxProg_svc f3TrialRxWordTree_eq
  f3TrialRxWordTree_size f3Trial_allocMemcpyVm_ok f3Trial_seg5ShimBundle)
open VerifiedLibraries.RustStd
  (allocCallPreserved_trans fetch_instr_at fetch_instr_at0 hookFrame_eq_stackFrame4096)

private theorem segc_perm_writeBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes a bs).perm = m.perm := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    simp only [Memory.writeBytes]
    exact (ih _ _).trans (Memory.perm_write8 m a b)

private theorem segc_stripS_mem (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl
private theorem segc_stripS_r64 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem segc_stripS_status (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl
private theorem segc_stripS_pc (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl
private theorem segc_stripS_sp (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl
private theorem segc_step_running {P : Program} {s s' : State} (h : Step P s s') :
    s.status = .Running := by cases h <;> assumption
private theorem segc_subroutineStop_stripS_iff {keep : BitVec 64 → Bool} {s0 s : State} :
    SubroutineStop s0 (stripS keep s) ↔ SubroutineStop s0 s := by
  cases s0; cases s; rfl
private theorem segc_calleeSavedPreserved_stripS {keep : BitVec 64 → Bool} {s0 sf : State}
    (h : CalleeSavedPreserved (stripS keep s0) (stripS keep sf)) :
    CalleeSavedPreserved s0 sf := by
  cases s0; cases sf; exact h
private theorem segc_steps_preserves_halted {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all
private theorem segc_steps_preserves_exception {P : Program} {u v : State} {msg : String}
    (hs : Steps P u v) (hu : u.status = .Exception msg) : v.status = .Exception msg := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all
private theorem segc_subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hr]; decide
  · rw [hp]; decide
  · rw [he]; nofun
  · rw [ho]; decide
private theorem segc_subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, he, _⟩ | ⟨ho, _⟩
  · exact Or.inl hret
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he⟩))
  · exact Or.inr (Or.inr (Or.inr ho))

@[local simp, local arm64_norm]
private theorem segc_sigActions_setPC_eq (s : State) (pc : BitVec 64) :
    (s.setPC pc).sigActions = s.sigActions := by cases s; rfl
@[local simp, local arm64_norm]
private theorem segc_sigActions_setMem_eq (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
@[local simp, local arm64_norm]
private theorem segc_sigActions_writeReg64_eq (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigActions = s.sigActions := by cases s; cases r <;> rfl
@[local simp, local arm64_norm]
private theorem segc_setMem_setMem_eq (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by cases s; rfl
@[local simp, local arm64_norm]
private theorem segc_setPC_setMem_eq (s : State) (m : Memory) (pc : BitVec 64) :
    (s.setMem m).setPC pc = (s.setPC pc).setMem m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem segc_mem_setMem_eq (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem segc_mem_setPC_eq (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm]
private theorem segc_mem_writeReg64_eq (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl

private theorem segc_bv_sub_add_cancel48 (sp : BitVec 64) : sp - 48#64 + 48#64 = sp := by bv_omega
private theorem segc_bv_add_neg48 (sp : BitVec 64) : sp + (-48#64) = sp - 48#64 := by bv_omega
private theorem segc_bv_add_neg16 (sp : BitVec 64) : sp + (-16#64) = sp - 16#64 := by bv_omega

attribute [local arm64_norm] bv_sub_add_lit segc_bv_sub_add_cancel48 segc_bv_add_neg48 segc_bv_add_neg16

private theorem segc_pool_setMem_perm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {m : Memory} (hm : m.perm = s.mem.perm) :
    A.pool lim st (s.setMem m) = A.pool lim st s :=
  A.pool_transport lim st s _ ⟨⟨rfl, rfl, rfl⟩, by cases s; rfl, fun a => by
    cases s; exact congrFun hm a, fun _ _ _ => by cases s; rfl⟩

private theorem segc_step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr,
      hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 (funext fun a => by rw [Memory.perm_write64, Memory.perm_write64])) hm2

local macro "segc_wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "segc_wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply segc_step_stp64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

private def segc_memcpyIdx : Nat := 1554
private def segc_rustAllocIdx : Nat := 407

set_option maxRecDepth 200000 in
private theorem segc_pins_chk :
    (Nat.blt 623 f3LsBlocksLen &&
     (f3LsBlockBases.getD 623 0#64 == 0x4686a0#64) &&
     Nat.blt segc_memcpyIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD segc_memcpyIdx "" == "memcpy") &&
     (Arm64.Obj.Interned.lookupBlockSymId segc_memcpyIdx lsInternedMultiLib.blocks == none) &&
     (f3LsSymAddrs.getD segc_memcpyIdx 0#64 == 0x469650#64) &&
     Nat.blt segc_rustAllocIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD segc_rustAllocIdx "" == lsRustAllocPlacedSym) &&
     (Arm64.Obj.Interned.lookupBlockSymId segc_rustAllocIdx lsInternedMultiLib.blocks == none) &&
     (f3LsSymAddrs.getD segc_rustAllocIdx 0#64 == 0x469630#64) &&
     (f3LsSymAddrs.getD f3HandleErrorIdx 0#64 == 0x468964#64) &&
     (blkLib_623.text.code.length == 132)) = true := by
  decide

set_option maxRecDepth 200000 in
private theorem segc_f3LsMpl_rho_of_idx {s : String} {idx : Nat}
    (hidx : lsInternedMultiLib.names.idxOf s = idx) :
    f3LsMpl.ρ s = f3LsSymAddrs.getD idx 0#64 := by
  have h : f3LsMpl.ρ s =
      f3LsSymAddrs.getD (lsInternedMultiLib.names.idxOf s) 0#64 := rfl
  rw [h, hidx]

set_option maxRecDepth 200000 in
private theorem segc_mpl_pins (mpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mpl.base 623 = 0x4686a0#64 ∧
    mpl.ρ lsRustNoAllocShimPlacedSym = 0x469640#64 ∧
    mpl.ρ lsRustAllocPlacedSym = 0x469630#64 ∧
    mpl.ρ "memcpy" = 0x469650#64 ∧
    mpl.ρ f3HandleErrorSym = 0x468964#64 ∧
    (libsignalSessionLib.blockProgram mpl 623).code.length = 132 := by
  have hc := segc_pins_chk
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h623_f3, hb623⟩, hmc_lt⟩, hmc_nm⟩, hmc_id⟩, hmc_addr⟩,
    hal_lt⟩, hal_nm⟩, hal_id⟩, hal_addr⟩, hhe_addr⟩, hlen623⟩
  have hlen_ls : libsignalSessionLib.blocks.length = f3LsBlocksLen :=
    Nat.beq_eq.mp libsignalBlocks_len
  have hlen_bs : f3LsBlockBases.length = f3LsBlocksLen :=
    Nat.beq_eq.mp f3LsBlockBases_len
  have h623 : 623 < libsignalSessionLib.blocks.length := by omega
  obtain ⟨img, hparse, hPl1, hIn1⟩ := hLs
  cases f3TrialElf_parse.symm.trans hparse
  have huniq := f3CliElf_libsignal_inElf_unique hPl1 hIn1
  have hb0 : f3LsMpl.base 623 = f3LsBlockBases.getD 623 0#64 := rfl
  have hb_mpl : mpl.base 623 = 0x4686a0#64 := (huniq.1 623 h623).trans (hb0.trans hb623)
  have hshim_mpl : mpl.ρ lsRustNoAllocShimPlacedSym = 0x469640#64 :=
    f3CliElf_rho_noAllocShim_of_linkedAt ⟨f3TrialElf, f3TrialElf_parse, hPl1, hIn1⟩
  have hal_mem : lsRustAllocPlacedSym ∈ lsInternedMultiLib.names := by
    rw [← hal_nm, Arm64.Obj.Interned.getD_of_lt hal_lt]; exact List.getElem_mem hal_lt
  have hal_none : Arm64.Obj.lookupBlockSym lsRustAllocPlacedSym libsignalSessionLib.blocks = none := by
    rw [← hal_nm, ls_toMultiPlacedLib_eq,
      Arm64.Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hal_lt]
    exact hal_id
  have hal_idx : lsInternedMultiLib.names.idxOf lsRustAllocPlacedSym = segc_rustAllocIdx := by
    rw [← hal_nm]; exact Arm64.Obj.Interned.idxOf_getD ls_names_nodup hal_lt
  have hal_mpl : mpl.ρ lsRustAllocPlacedSym = 0x469630#64 :=
    (huniq.2.2.1 _ hal_mem hal_none).trans ((segc_f3LsMpl_rho_of_idx hal_idx).trans hal_addr)
  have hmc_mem : "memcpy" ∈ lsInternedMultiLib.names := by
    rw [← hmc_nm, Arm64.Obj.Interned.getD_of_lt hmc_lt]; exact List.getElem_mem hmc_lt
  have hmc_none : Arm64.Obj.lookupBlockSym "memcpy" libsignalSessionLib.blocks = none := by
    rw [← hmc_nm, ls_toMultiPlacedLib_eq,
      Arm64.Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hmc_lt]
    exact hmc_id
  have hmc_idx : lsInternedMultiLib.names.idxOf "memcpy" = segc_memcpyIdx := by
    rw [← hmc_nm]; exact Arm64.Obj.Interned.idxOf_getD ls_names_nodup hmc_lt
  have hmc_mpl : mpl.ρ "memcpy" = 0x469650#64 :=
    (huniq.2.2.1 _ hmc_mem hmc_none).trans ((segc_f3LsMpl_rho_of_idx hmc_idx).trans hmc_addr)
  have hhe_pin := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3HandleError_pin_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hhe_pin
  have hhe_idx : lsInternedMultiLib.names.idxOf f3HandleErrorSym = f3HandleErrorIdx := by
    change lsInternedMultiLib.names.idxOf
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3HandleErrorSym = _
    rw [← hhe_pin.1.2]; exact Arm64.Obj.Interned.idxOf_getD ls_names_nodup hhe_pin.1.1
  have hhe_mpl : mpl.ρ f3HandleErrorSym = 0x468964#64 :=
    (f3CliElf_rho_handleError_eq_of_linkedAt ⟨f3TrialElf, f3TrialElf_parse, hPl1, hIn1⟩).trans
      ((segc_f3LsMpl_rho_of_idx hhe_idx).trans hhe_addr)
  have hcode_mpl : (libsignalSessionLib.blockProgram mpl 623).code =
      (libsignalSessionLib.blocks[623]'h623).patched (libsignalSessionLib.blockPlacement mpl 623) := by
    unfold Arm64.Obj.MultiPlacedLib.blockProgram Arm64.Obj.PlacedLib.program
    dsimp only
    rw [libsignalSessionLib.blockLib_text h623]
  have hblk_len : (libsignalSessionLib.blocks[623]'h623).code.length = 132 := by
    rw [← libsignalSessionLib.blockLib_text h623, ← blkLib_eq_623]; exact hlen623
  have hprog_len : (libsignalSessionLib.blockProgram mpl 623).code.length = 132 := by
    rw [hcode_mpl, Arm64.Obj.CodeBlock.length_patched_of_aligned _ (hPl1.blocks_ok 623 h623).len_aligned]
    exact hblk_len
  exact ⟨hb_mpl, hshim_mpl, hal_mpl, hmc_mpl, hhe_mpl, hprog_len⟩

private theorem segc_mkProg_code (b : BitVec 64) (c : List (BitVec 8))
    (ext : String → Option (State → State)) (sv : State → State) :
    ({ base := b, code := c, externs := ext, stubs := [], svc := sv : Program }).code = c := rfl

private theorem segc_blockProgram_base (lib : Arm64.Obj.MultiPlacedLib) (mpl : MultiPlacement) (i : Nat) :
    (lib.blockProgram mpl i (fun _ => none)).base = mpl.base i := rfl

private theorem segc_readWordOff_congr {P1 P2 : Program} (h : P1.code = P2.code) (off : Nat) :
    P1.readWordOff off = P2.readWordOff off := by
  unfold Program.readWordOff; rw [h]

private noncomputable def segc_str1ExtProg (mpl : MultiPlacement) : Program where
  base := mpl.base 623
  code := (hole2_str1Prog mpl).code
  externs := (hole2_strCloneProg mpl).externs
  stubs := []
  svc := Arm64.Syscall.standard

private theorem segc_str1ExtProg_codeLoaded_iff (mpl : MultiPlacement) (m : Memory) :
    (segc_str1ExtProg mpl).CodeLoaded m ↔ (hole2_str1Prog mpl).CodeLoaded m := by
  have hbase : (segc_str1ExtProg mpl).base = (hole2_str1Prog mpl).base := rfl
  have hcode : (segc_str1ExtProg mpl).code = (hole2_str1Prog mpl).code := by
    unfold segc_str1ExtProg
    exact segc_mkProg_code _ _ _ _
  rw [Program.codeLoaded_iff, Program.codeLoaded_iff, hbase, hcode]

private theorem segc_externAt_eq (mpl : MultiPlacement)
    (_hb : mpl.base 623 = 0x4686a0#64)
    (_hmc : mpl.ρ "memcpy" = 0x469650#64)
    (_hhe : mpl.ρ f3HandleErrorSym = 0x468964#64)
    (pc : BitVec 64) :
    (segc_str1ExtProg mpl).externAt? pc = (hole2_strCloneProg mpl).externAt? pc :=
  rfl

private theorem segc_steps_to_strClone (mpl : MultiPlacement)
    (hb : mpl.base 623 = 0x4686a0#64)
    (hmc : mpl.ρ "memcpy" = 0x469650#64)
    (hhe : mpl.ρ f3HandleErrorSym = 0x468964#64)
    {s1 s2 : State} (h : Steps (segc_str1ExtProg mpl) s1 s2) :
    Steps (hole2_strCloneProg mpl) s1 s2 := by
  induction h with
  | refl s => exact Steps.refl s
  | @step a b c h1 _ ih =>
    have hstep : Step (hole2_strCloneProg mpl) a b := by
      have hext := segc_externAt_eq mpl hb hmc hhe a.pc
      cases h1 with
      | @exec inst hr hfm =>
        have hfm' : (hole2_strCloneProg mpl).fetchMem a.mem a.pc = some inst := by
          unfold Program.fetchMem at hfm ⊢; rwa [← hext]
        have hev : (segc_str1ExtProg mpl).evalInst inst a = (hole2_strCloneProg mpl).evalInst inst a := rfl
        rw [hev]
        exact Step.exec hr hfm'
      | halt_unmapped hr hfm hnone =>
        have hfm' : (hole2_strCloneProg mpl).fetchMem a.mem a.pc = none := by
          unfold Program.fetchMem at hfm ⊢; rwa [← hext]
        exact Step.halt_unmapped hr hfm' (hext ▸ hnone)
      | extern hr he hkf hsym =>
        exact Step.extern hr (hext ▸ he) hkf hsym
      | extern_fault hr he hnkf =>
        exact Step.extern_fault hr (hext ▸ he) hnkf
    exact Steps.step hstep ih

private theorem segc_steps_rx_to_str1Ext (mpl : MultiPlacement)
    {s1 s2 : State} (h : Steps f3TrialRxProg s1 s2) :
    Steps (segc_str1ExtProg mpl) s1 s2 := by
  induction h with
  | refl s => exact Steps.refl s
  | @step a b c h1 _ ih =>
    have hext : f3TrialRxProg.externAt? a.pc = (segc_str1ExtProg mpl).externAt? a.pc :=
      f3TrialRxProg_no_ext a.pc
    have hstep : Step (segc_str1ExtProg mpl) a b := by
      cases h1 with
      | @exec inst hr hfm =>
        have hfm' : (segc_str1ExtProg mpl).fetchMem a.mem a.pc = some inst := by
          unfold Program.fetchMem at hfm ⊢; rwa [← hext]
        have hev : f3TrialRxProg.evalInst inst a = (segc_str1ExtProg mpl).evalInst inst a := by
          unfold Program.evalInst; rw [f3TrialRxProg_svc]; rfl
        rw [hev]
        exact Step.exec hr hfm'
      | halt_unmapped hr hfm hnone =>
        have hfm' : (segc_str1ExtProg mpl).fetchMem a.mem a.pc = none := by
          unfold Program.fetchMem at hfm ⊢; rwa [← hext]
        exact Step.halt_unmapped hr hfm' (hext ▸ hnone)
      | extern hr he hkf hsym =>
        exact Step.extern hr (hext ▸ he) hkf hsym
      | extern_fault hr he hnkf =>
        exact Step.extern_fault hr (hext ▸ he) hnkf
    exact Steps.step hstep ih

private theorem segc_rx_memcpy_run (mpl : MultiPlacement)
    (x : BitVec 64 × BitVec 64 × List (BitVec 8)) (R' : SepProp) (s : State)
    (hpc : s.pc = 0x469650#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hpre : s.mem ⊨ allocMemcpyVmSpec.pre x s ∗ R')
    (hRx : f3TrialRxProg.CodeLoaded s.mem) :
    ∃ sf : State,
      Steps (segc_str1ExtProg mpl) s sf ∧
      SubroutineOutcome allocMemcpyVmSpec x R' s sf := by
  obtain ⟨sf, hsteps, hout, _⟩ :=
    f3Trial_allocMemcpyVm_ok.no_fault_before_outcome x R' s hpc hrun hpre hsp hRx
  exact ⟨sf, segc_steps_rx_to_str1Ext mpl hsteps, hout⟩

set_option linter.style.haveILetI false in
private theorem segc_clone_hasInstrs (mpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    hasInstrs (segc_str1ExtProg mpl) 0x4686a0#64
      (rustStringCloneInstrs 0x4686a0#64 0x469640#64 0x469630#64 0x469650#64 0x468964#64) := by
  obtain ⟨hb, hsh, hal, hmc, hhe, _⟩ := segc_mpl_pins mpl hLs
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hls_base : lsmpl.base 623 = 0x4686a0#64 := hb
  have hls_sh : lsρ lsRustNoAllocShimPlacedSym = 0x469640#64 := hsh
  have hls_al : lsρ lsRustAllocPlacedSym = 0x469630#64 := hal
  have hls_mc : lsρ "memcpy" = 0x469650#64 := hmc
  have hls_he : lsρ lsHandleErrorPlacedSym = 0x468964#64 := hhe
  have hbase623 := lsProg_623_hasInstrs (fun _ => none)
  rw [hls_base, hls_sh, hls_al, hls_mc, hls_he] at hbase623
  have heq_prog : lsProg_623 (fun _ => none) =
      libsignalSessionLib.blockProgram mpl 623 (fun _ => none) :=
    (instIsLsBlockProg_623 (fun _ => none)).eq_blockProgram
  intro i hi
  have hf0 := hbase623 i hi
  rw [heq_prog] at hf0
  let pc := 0x4686a0#64 + BitVec.ofNat 64 (4 * i)
  have hext_segc : (segc_str1ExtProg mpl).externAt? pc = none := rfl
  unfold Program.fetch at hf0 ⊢
  rw [hext_segc]
  split at hf0
  · cases hf0
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hbase_eq :
        (segc_str1ExtProg mpl).base =
          (libsignalSessionLib.blockProgram mpl 623 (fun _ => none)).base := by
      rw [segc_blockProgram_base]
      rfl
    have hcode_eq :
        (segc_str1ExtProg mpl).code =
          (libsignalSessionLib.blockProgram mpl 623 (fun _ => none)).code := by
      unfold segc_str1ExtProg
      rw [segc_mkProg_code]
      unfold hole2_str1Prog
      exact segc_mkProg_code _ _ _ _
    rw [hbase_eq, segc_readWordOff_congr hcode_eq]
    exact hf0

-- 3. `stripS` Commutation & Same-Program `StepsUntil` Lift

private theorem segc_frozen_stripExecOutside {k : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) {a : BitVec 64} (hfz : m.Frozen a) :
    (stripExecOutside k m).Frozen a := by
  unfold Memory.Frozen at hfz ⊢
  rw [strip_perm]
  cases hp : m.perm a with
  | none => rw [hp] at hfz; cases hfz
  | some p =>
    rw [hp] at hfz
    cases hk : k a
    · by_cases hx : p.x = true
      · have hxm : (m.perm a).x = true := by rw [hp]; exact hx
        obtain ⟨hr, hnw⟩ := hfr a hxm
        rw [hp] at hr hnw
        rcases p with ⟨r, w, x, lf, an⟩
        simp only [Option.r, Option.w, Option.frozen, Perm.frozen] at hr hnw hfz ⊢
        subst hr hnw
        cases x <;> rfl
      · have hxf : p.x = false := Bool.eq_false_iff.mpr hx
        rcases p with ⟨r, w, x, lf, an⟩
        simp only at hxf
        subst hxf
        exact hfz
    · exact hfz

private theorem segc_stepsUntil_of_stripS_sameProg
    {keep : BitVec 64 → Bool} {P : Program} {s0 : State}
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hext_comm : ∀ (pc : BitVec 64) (f : State → State),
      P.externAt? pc = some f →
      pc ≠ s0.readReg64 .lr ∧
      (∀ st : State, ExecFrozen st.mem →
        (stripExecOutside keep st.mem).KeepsFrozen (f (stripS keep st)).mem →
        f (stripS keep st) = stripS keep (f st) ∧
        ExecFrozen (f st).mem ∧
        st.mem.KeepsFrozen (f st).mem ∧
        (f st).symtab = st.symtab))
    (hlr_out : keep (s0.readReg64 .lr) = false)
    {s1' sf' : State}
    (hsteps : Steps P s1' sf')
    (hstop' : SubroutineStop s0 sf')
    (hnhalt' : sf'.status ≠ .Halted) :
    ∀ s1 : State,
      s1' = stripS keep s1 →
      ExecFrozen s1.mem →
      ∃ sf : State,
        StepsUntil P (SubroutineStop s0) s1 sf ∧
        SubroutineStop s0 sf ∧
        sf' = stripS keep sf ∧
        ExecFrozen sf.mem := by
  induction hsteps with
  | refl s' =>
    intro s1 hs1 hfr1
    exact ⟨s1, StepsUntil.refl s1, segc_subroutineStop_stripS_iff.mp (hs1 ▸ hstop'), hs1, hfr1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro sa hsa hfra
    by_cases hstop_sa : SubroutineStop s0 sa
    · rcases hstop_sa with ⟨hpc_lr, _⟩ | hpan | ⟨_, hex⟩ | hoom
      · cases h1 with
        | @exec inst hr' hfm' =>
          rw [hsa, segc_stripS_pc, segc_stripS_mem] at hfm'
          unfold Program.fetchMem at hfm'
          cases he : P.externAt? sa.pc with
          | some f => simp [he] at hfm'
          | none =>
            simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
            by_cases hal : sa.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
              by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
              · have hx0 : ((stripExecOutside keep sa.mem).perm sa.pc).x = true := by
                  have h4 :
                      ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                      ((stripExecOutside keep sa.mem).allPerm (·.x) (sa.pc + 1#64) 3) = true := by
                    simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true] using hce'
                  exact h4.1
                have hkp := (strip_perm_x_imp hx0).2
                rw [hpc_lr, hlr_out] at hkp; cases hkp
              · simp [hce'] at hfm'
            · simp [hal] at hfm'
        | halt_unmapped _ _ _ => exact False.elim (hnhalt' (segc_steps_preserves_halted hrest rfl))
        | extern _ he _ _ =>
          rw [hsa, segc_stripS_pc] at he; exact False.elim ((hext_comm sa.pc _ he).1 hpc_lr)
        | extern_fault _ he _ =>
          rw [hsa, segc_stripS_pc] at he; exact False.elim ((hext_comm sa.pc _ he).1 hpc_lr)
      · have hr_sa : sa.status = .Running := by have h := segc_step_running h1; rwa [hsa, segc_stripS_status] at h
        rw [hpan] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by have h := segc_step_running h1; rwa [hsa, segc_stripS_status] at h
        rw [hex] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by have h := segc_step_running h1; rwa [hsa, segc_stripS_status] at h
        rw [hoom] at hr_sa; cases hr_sa
    · cases h1 with
      | halt_unmapped _ _ _ => exact False.elim (hnhalt' (segc_steps_preserves_halted hrest rfl))
      | @extern f hr' he' hkf' _ =>
        have hra : sa.status = .Running := by rw [hsa, segc_stripS_status] at hr'; exact hr'
        rw [hsa, segc_stripS_pc] at he'
        rw [hsa] at hkf'
        obtain ⟨_, hf_comm⟩ := hext_comm sa.pc f he'
        obtain ⟨hf_eq, hfr_f, hkf_f, hsym_f⟩ := hf_comm sa hfra hkf'
        have hstep_real : Step P sa (f sa) := Step.extern hra he' hkf_f hsym_f
        rw [hsa, hf_eq] at hrest ih
        obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ := ih hstop' hnhalt' (f sa) rfl hfr_f
        exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩
      | extern_fault _ _ _ =>
        have hsf_ex := segc_steps_preserves_exception hrest rfl
        rcases hstop' with ⟨_, _, hr_sf⟩ | hpan | ⟨_, hex⟩ | hoom
        · rw [hsf_ex] at hr_sf; cases hr_sf
        · rw [hsf_ex] at hpan; cases hpan
        · rw [hsf_ex] at hex; cases hex
        · rw [hsf_ex] at hoom; cases hoom
      | @exec inst hr' hfm' =>
        have hra : sa.status = .Running := by rw [hsa, segc_stripS_status] at hr'; exact hr'
        rw [hsa, segc_stripS_pc, segc_stripS_mem] at hfm'
        unfold Program.fetchMem at hfm'
        cases he_sub : P.externAt? sa.pc with
        | some f => simp [he_sub] at hfm'
        | none =>
          simp only [he_sub, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
          by_cases hal_pc : sa.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
            by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
            · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
              have hx4 :
                  ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 1#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 2#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 3#64)).x = true := by
                simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
              have hce : sa.mem.canExec sa.pc 4 = true := by
                simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc,
                  (strip_perm_x_imp hx4.1).1, (strip_perm_x_imp hx4.2.1).1,
                  (strip_perm_x_imp hx4.2.2.1).1, (strip_perm_x_imp hx4.2.2.2).1]
              have hr32 : (stripExecOutside keep sa.mem).read32 sa.pc = sa.mem.read32 sa.pc := by
                simp [Memory.read32, strip_read8]
              rw [hr32] at hfm'
              have hfm_real : P.fetchMem sa.mem sa.pc = some inst := by
                unfold Program.fetchMem; simp [he_sub, hal_pc, hce, hfm']
              by_cases hsvc0 : inst.isSvc0 = true
              · have hinst : inst = .system false 0#16 := by
                  cases inst <;> simp [Instr.isSvc0] at hsvc0
                  rcases hsvc0 with ⟨rfl, rfl⟩; rfl
                subst hinst
                obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keep) hfra
                have hev_strip : P.evalInst (.system false 0#16) (stripS keep sa) =
                    stripS keep (Arm64.Syscall.standard sa) := by
                  simp [Program.evalInst, execInstWithSvc, hsvc, hcomm]
                have hev_real : P.evalInst (.system false 0#16) sa = Arm64.Syscall.standard sa := by
                  simp [Program.evalInst, execInstWithSvc, hsvc]
                have hstep_real : Step P sa (Arm64.Syscall.standard sa) := hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                  ih hstop' hnhalt' (Arm64.Syscall.standard sa) rfl hfr_sb
                exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩
              · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
                have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
                have hfr_sb : ExecFrozen (execInst inst sa).mem :=
                  ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
                have hev_strip : P.evalInst inst (stripS keep sa) = stripS keep (execInst inst sa) := by
                  rw [ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0 P hnsvc0, execInst_stripS hnsvc0]
                have hev_real : P.evalInst inst sa = execInst inst sa :=
                  ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0 P hnsvc0 sa
                have hstep_real : Step P sa (execInst inst sa) := hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                  ih hstop' hnhalt' (execInst inst sa) rfl hfr_sb
                exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩
            · simp [hce'] at hfm'
          · simp [hal_pc] at hfm'

private theorem segc_strCloneProg_ext_comm (mpl : MultiPlacement)
    (_hmc : mpl.ρ "memcpy" = 0x469650#64)
    (_hhe : mpl.ρ f3HandleErrorSym = 0x468964#64)
    {s0 : State} (_hlr_out : hole2_keep (s0.readReg64 .lr) = false)
    (pc : BitVec 64) (f : State → State)
    (he : (hole2_strCloneProg mpl).externAt? pc = some f) :
    pc ≠ s0.readReg64 .lr ∧
    (∀ st : State, ExecFrozen st.mem →
      (stripExecOutside hole2_keep st.mem).KeepsFrozen (f (stripS hole2_keep st)).mem →
      f (stripS hole2_keep st) = stripS hole2_keep (f st) ∧
      ExecFrozen (f st).mem ∧
      st.mem.KeepsFrozen (f st).mem ∧
      (f st).symtab = st.symtab) := by
  cases he

private theorem segc_codeLoaded_of_keepsFrozen {P : Program} {m m' : Memory}
    (hcl : P.CodeLoaded m) (hkf : m.KeepsFrozen m') : P.CodeLoaded m' := by
  rw [Program.codeLoaded_iff] at hcl ⊢
  refine ⟨hcl.1, hcl.2.1, fun i hi => ?_⟩
  obtain ⟨hr, hp, hlz⟩ := hcl.2.2 i hi
  have hfz : m.Frozen (P.base + BitVec.ofNat 64 i) := by unfold Memory.Frozen; rw [hp]; rfl
  obtain ⟨hr', hp', hlz', _⟩ := hkf _ hfz
  exact ⟨hr'.trans hr, hp'.trans hp, hlz'.trans hlz⟩

private theorem segc_execFrozen_stripExecOutside (k : BitVec 64 → Bool) {m : Memory}
    (hfr : ExecFrozen m) : ExecFrozen (stripExecOutside k m) := by
  intro a hx
  obtain ⟨hx_m, hk⟩ := strip_perm_x_imp hx
  rw [strip_perm, hk]
  cases hp : m.perm a with
  | none => simp [hp] at hx_m
  | some p =>
    have h := hfr a hx_m
    simpa [hp, stripPerm] using h

private theorem segc_execFrozen_of_steps_str1Ext (mpl : MultiPlacement)
    {s1 s2 : State} (hsteps : Steps (segc_str1ExtProg mpl) s1 s2)
    (hfr1 : ExecFrozen s1.mem) : ExecFrozen s2.mem := by
  induction hsteps with
  | refl _ => exact hfr1
  | @step a b c h1 _ ih =>
    have hfr_b : ExecFrozen b.mem := by
      cases h1 with
      | @exec inst _ _ =>
        by_cases hsvc0 : inst.isSvc0 = true
        · have hinst : inst = .system false 0#16 := by
            cases inst <;> simp [Instr.isSvc0] at hsvc0; rcases hsvc0 with ⟨rfl, rfl⟩; rfl
          subst hinst
          have hev0 : (segc_str1ExtProg mpl).evalInst (.system false 0#16) a =
              Arm64.Syscall.standard a := by
            simp [Program.evalInst, execInstWithSvc, segc_str1ExtProg]
          rw [hev0]
          exact (standard_stripS (keep := hole2_keep) hfr1).2
        · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
          rw [ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0 (segc_str1ExtProg mpl) hnsvc0]
          have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 a
          exact ExecFrozen.of_perm_eq hfr1 (congrFun hpf.2.1)
      | halt_unmapped _ _ _ => exact hfr1
      | extern _ he _ _ => cases he
      | extern_fault _ _ _ => exact hfr1
    exact ih hfr_b

private theorem segc_rxProg_codeLoaded_keepSub {m : Memory}
    (hcl : f3TrialRxProg.CodeLoaded m) :
    f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub m) := by
  have hlen : f3TrialRxProg.code.length = 4 * f3RxWordCount := by
    rw [f3TrialRxWordTree_eq]
    exact ProofLib.ProgramReflection.WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size
  have hbase : f3TrialRxProg.base = 0x469000#64 := f3TrialRxProg_base
  rw [Program.codeLoaded_iff] at hcl ⊢
  refine ⟨hcl.1, hcl.2.1, fun i hi => ?_⟩
  obtain ⟨hr, hp, hlz⟩ := hcl.2.2 i hi
  have hk : hole2_keepSub (f3TrialRxProg.base + BitVec.ofNat 64 i) = true := by
    rw [hbase]
    have hi_lt : i < 24576 := by rw [hlen] at hi; exact hi
    unfold hole2_keepSub
    rw [decide_eq_true_eq]
    bv_omega
  refine ⟨by rw [strip_read8]; exact hr, ?_, by rw [strip_isLazyFree]; exact hlz⟩
  rw [strip_perm, hp, hk]; rfl

private theorem segc_str1ExtProg_no_ext_in_keepSub (mpl : MultiPlacement)
    (_hb : mpl.base 623 = 0x4686a0#64) (pc : BitVec 64) (_hk : hole2_keepSub pc = true) :
    (segc_str1ExtProg mpl).externAt? pc = none :=
  rfl

private theorem segc_spAligned_sub48 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem segc_stackFrameAt48_eq (sp : BitVec 64) :
    stackFrameAt sp 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem segc_pack_stack48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
     ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
     ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢ stackFrameAt sp 48 := by
  rw [segc_stackFrameAt48_eq sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

private theorem segc_sepWP_done_let {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running → SepWPp prog ret sm P Q Qp oom) :
    SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom :=
  SepWP.done hpc hrun (h s rfl hpc hrun)

private theorem segc_memRegion24_eq_exists_pts (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl,
      memRegion_split a 8 (8 + 8) (by decide),
      memRegion_split (a + 8#64) 8 8 (by decide),
      memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private theorem segc_vecGhostAt_bytes_lt_2pow63 {A : RustAlloc}
    {m : Memory} {g : VecGhost} {p : BitVec 64} {R : SepProp}
    (hm : m ⊨ vecGhostAt A g p ∗ R) :
    g.bytes.length < 2 ^ 63 := by
  unfold vecGhostAt vecU8At at hm
  have hPull :
      (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
        ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (if g.cap = 0 then SepProp.emp
         else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) ∗ R =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
          (if g.cap = 0 then SepProp.emp
           else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
             memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗ R) := by
    sep_ac_rfl
  rw [hPull, satisfies_pure_sepConj] at hm
  omega

private def segc_vecGhostPayload (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
  (if g.cap = 0 then SepProp.emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem segc_vecGhostAt_eq_header_payload (A : RustAlloc) (g : VecGhost) (p : BitVec 64) :
    vecGhostAt A g p =
      (((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)) ∗
        segc_vecGhostPayload A g) := by
  unfold vecGhostAt vecU8At vecHeader segc_vecGhostPayload; sep_ac_rfl

private def segc_vecGhostPayloadRest (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗ A.live g.ptr g.cap.toNat 1 ∗
  memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)

private theorem segc_vecGhostPayload_nonempty_entails (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    segc_vecGhostPayload A g ⊢ (g.ptr ↦ₛ g.bytes) ∗ segc_vecGhostPayloadRest A g := by
  unfold segc_vecGhostPayload segc_vecGhostPayloadRest
  refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
                                omega
  simp only [hcapNe, ↓reduceIte]
  have hEq :
      A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) =
      (g.ptr ↦ₛ g.bytes) ∗ (A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hEq]; exact sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl)))

private theorem segc_vecGhostPayload_nonempty_pack (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    ((g.ptr ↦ₛ g.bytes) ∗ segc_vecGhostPayloadRest A g) ⊢ segc_vecGhostPayload A g := by
  unfold segc_vecGhostPayloadRest segc_vecGhostPayload
  have hPull :
      (g.ptr ↦ₛ g.bytes) ∗ (⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        ((g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hPull]; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
                                omega
  simp only [hcapNe, ↓reduceIte]; exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem segc_vecU8_empty_pack (A : RustAlloc) (ret : BitVec 64) :
    ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A ret [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  have hZero : (0#64 : BitVec 64) = 0 := rfl
  simp only [hZero, ↓reduceIte, sepConj_emp, List.length_nil]
  refine Entails.trans (Entails.pure_right
    (φ := 0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0)
    (by decide) (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private theorem segc_vecU8_nonempty_pack {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ret newPtr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt63 : bs.length < 2 ^ 63) (hne0 : newPtr ≠ 0#64) :
    let lenBv := BitVec.ofNat 64 bs.length
    (((ret ↦₆₄ lenBv) ∗ ((ret + 8#64) ↦₆₄ newPtr) ∗ ((ret + 16#64) ↦₆₄ lenBv)) ∗
      A.live newPtr bs.length 1 ∗ (newPtr ↦ₛ bs)) ⊢ vecU8 A.repAlloc ret bs := by
  intro lenBv
  have hlenNat : lenBv.toNat = bs.length := by
    dsimp only [lenBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcapNe : lenBv ≠ 0 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hlenNat] at this; change bs.length = 0 at this; omega
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right lenBv (Entails.sepExists_right newPtr ?_)
  simp only [hcapNe, ↓reduceIte, hlenNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  have hLiveEq : A.repAlloc.live newPtr bs.length 1 = A.live newPtr bs.length 1 := rfl
  rw [hLiveEq]
  refine Entails.trans (Entails.pure_right (φ := bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ newPtr ≠ 0)
    ⟨Nat.le_refl _, hlt63, hne0⟩ (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private abbrev segc_savedStack48 (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private abbrev segc_vecHdrPts (p : BitVec 64) (g : VecGhost) : SepProp :=
  (p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)

private abbrev segc_retPts (ret r0 r1 r2 : BitVec 64) : SepProp :=
  (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2)

private abbrev segc_csUpperPreserved (s0 sm : State) : Prop :=
  ∀ r ∈ ([.x23, .x24, .x25, .x26, .x27, .x28] : List Reg), sm.readReg64 r = s0.readReg64 r

private theorem segc_csUpperPreserved_trans {s0 sm sf : State}
    (h1 : segc_csUpperPreserved s0 sm) (h2 : CalleeSavedPreserved sm sf) :
    segc_csUpperPreserved s0 sf := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2.readReg64_x23.trans (h1 .x23 (by simp))
  · exact h2.readReg64_x24.trans (h1 .x24 (by simp))
  · exact h2.readReg64_x25.trans (h1 .x25 (by simp))
  · exact h2.readReg64_x26.trans (h1 .x26 (by simp))
  · exact h2.readReg64_x27.trans (h1 .x27 (by simp))
  · exact h2.readReg64_x28.trans (h1 .x28 (by simp))

private abbrev segc_cloneFrame0 (s0 : State) : SepProp :=
  stackFrameAt (s0.sp - 48#64 - 4096#64) 12240

private abbrev segc_cloneNoOomPost [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ (segc_cloneFrame0 s0 ∗ R)) →
      sf.mem ⊨ (stringCloneNoOomSpec M A lim).post (p, ret, g, st) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev segc_cloneNoOomPanic : State → SepProp → Prop :=
  fun _ _ => False

private theorem segc_clone_empty_epilogue [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (p ret : BitVec 64) (g : VecGhost) (st : M.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm : State)
    (hg_empty : g.bytes = []) (hsp0 : s0.spAligned = true)
    (hpcm : sm.pc = fnAddr + 0x5c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 48#64) (hx19 : sm.readReg64 .x19 = 0#64)
    (hx20 : sm.readReg64 .x20 = ret) (hcsm : segc_csUpperPreserved s0 sm)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hpres : AllocCallPreserved s0 sm) (hpoolm : A.pool lim st sm = A.pool lim st s0) :
    SepWPp P (s0.readReg64 .lr) sm
      (segc_retPts ret r0 r1 r2 ∗ segc_savedStack48 s0 ∗
        (segc_vecHdrPts p g ∗ segc_vecGhostPayload A.repAlloc g) ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) allocHookStack)
      (segc_cloneNoOomPost A lim p ret g st R s0)
      segc_cloneNoOomPanic := by
  have hf23 := fetch_instr_at 23 hCode; have hf24 := fetch_instr_at 24 hCode
  have hf25 := fetch_instr_at 25 hCode; have hf26 := fetch_instr_at 26 hCode
  have hf27 := fetch_instr_at 27 hCode; have hf28 := fetch_instr_at 28 hCode
  have hf29 := fetch_instr_at 29 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide (sm.sp &&& 15#64 = 0#64) = true := by
    rw [hspm]; exact decide_eq_true (beq_iff_eq.mp (segc_spAligned_sub48 hspAl0))
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts]
  wp_step; segc_wp_stp64 hf24 m1 hm1; segc_wp_str64 hf25 m2 hm2
  wp_step; wp_step; wp_step; wp_step
  refine segc_sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrunm])
    fun sf hsf hpcf hrunf => ?_
  have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
  have hcsf : CalleeSavedPreserved s0 sf := by
    rw [hsf]
    refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hcsm .x23 (by simp), by simpa [arm64_norm] using hcsm .x24 (by simp),
      by simpa [arm64_norm] using hcsm .x25 (by simp), by simpa [arm64_norm] using hcsm .x26 (by simp),
      by simpa [arm64_norm] using hcsm .x27 (by simp), by simpa [arm64_norm] using hcsm .x28 (by simp),
      by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hvm⟩
  have hpresf : AllocCallPreserved s0 sf := by
    rw [hsf]; exact allocCallPreserved_trans hpres
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hm2_0 : m2.perm = sm.mem.perm := by
    try simp only [arm64_norm] at hm1 hm2
    exact hm2.trans hm1
  have hpoolf : A.pool lim st sf = A.pool lim st s0 := by
    rw [hsf, segc_pool_setMem_perm A lim st _ (by simpa [arm64_norm] using hm2_0)]
    simpa [arm64_norm] using hpoolm
  clear hsf
  refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
  have hevs : stringCloneEvents g = [] := by
    unfold stringCloneEvents; simp only [hg_empty, List.length_nil, ↓reduceIte]
  dsimp only [segc_cloneNoOomPost, segc_cloneFrame0, stringCloneNoOomSpec] at hmf ⊢
  rw [hevs, AllocCostModel.stepEvents_nil, hpoolf, extHookStack_split_48 s0.sp]
  have hx19' : sm.readReg64 (Reg.gpr 19#5) = 0#64 := hx19
  have hx20' : sm.readReg64 (Reg.gpr 20#5) = ret := hx20
  try simp only [hx19', hx20', BitVec.add_zero] at hmf
  have hVecEq : (segc_vecHdrPts p g ∗ segc_vecGhostPayload A.repAlloc g) = vecGhostAt A.repAlloc g p :=
    (segc_vecGhostAt_eq_header_payload A.repAlloc g p).symm
  have hmf1 : sf.mem ⊨
      (vecGhostAt A.repAlloc g p ∗
        (segc_retPts ret 0#64 1#64 0#64 ∗ A.pool lim st s0 ∗
          (segc_savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ segc_cloneFrame0 s0)))) ∗ R := by
    rw [← hVecEq]
    exact Satisfies.mono (Entails.of_eq (by
      dsimp only [segc_cloneFrame0, segc_savedStack48, segc_vecHdrPts, segc_retPts,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)) hmf
  rw [hg_empty]
  refine Satisfies.mono (sepConj_mono_left ?_) hmf1
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (segc_vecU8_empty_pack A.repAlloc ret)
        (sepConj_mono_right (sepConj_mono_left (segc_pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
  exact Entails.pure_right hpresf (Entails.of_eq (by sep_ac_rfl))

private theorem segc_clone_memcpy_epilogue [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {P : Program}
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hMemcpyRun : ∀ (x : BitVec 64 × BitVec 64 × List (BitVec 8)) (R' : SepProp) (s : State),
      s.pc = memcpyAddr → s.status = .Running → s.spAligned = true →
      (s.mem ⊨ allocMemcpyVmSpec.pre x s ∗ R') →
      f3TrialRxProg.CodeLoaded s.mem →
      ∃ sf : State, Steps P s sf ∧ SubroutineOutcome allocMemcpyVmSpec x R' s sf)
    (p ret newPtr : BitVec 64) (g : VecGhost) (st : M.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sf2 : State)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63)
    (hpNe0 : newPtr ≠ 0#64) (hsp0 : s0.spAligned = true)
    (hRx2 : f3TrialRxProg.CodeLoaded sf2.mem)
    (hpc2 : sf2.pc = fnAddr + 0x30#64) (hrun2 : sf2.status = .Running)
    (hsp2 : sf2.sp = s0.sp - 48#64)
    (hx0_2 : sf2.readReg64 .x0 = newPtr)
    (hx19_2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_2 : sf2.readReg64 .x20 = ret)
    (hx22_2 : sf2.readReg64 .x22 = g.ptr)
    (hcs2 : segc_csUpperPreserved s0 sf2)
    (hv2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hpres2 : AllocCallPreserved s0 sf2) :
    let st' := M.stepEvents (rustAllocEvents g.bytes.length 1) st
    SepWPp P (s0.readReg64 .lr) sf2
      (memRegion newPtr g.bytes.length ∗ segc_vecGhostPayload A.repAlloc g ∗
        A.live newPtr g.bytes.length 1 ∗ A.pool lim st' sf2 ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ segc_retPts ret r0 r1 r2 ∗
        segc_vecHdrPts p g ∗ segc_savedStack48 s0)
      (segc_cloneNoOomPost A lim p ret g st R s0)
      segc_cloneNoOomPanic := by
  intro st'
  have hf12 := fetch_instr_at 12 hCode; have hf13 := fetch_instr_at 13 hCode
  have hf14 := fetch_instr_at 14 hCode; have hf15 := fetch_instr_at 15 hCode
  have hf16 := fetch_instr_at 16 hCode; have hf17 := fetch_instr_at 17 hCode
  have hf18 := fetch_instr_at 18 hCode; have hf19 := fetch_instr_at 19 hCode
  have hf20 := fetch_instr_at 20 hCode; have hf21 := fetch_instr_at 21 hCode
  have hf22 := fetch_instr_at 22 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := segc_spAligned_sub48 hspAl0
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (segc_vecGhostPayload_nonempty_entails A.repAlloc g hpos))) ?_
  apply SepWPp.of_sepWP (mid := memcpyAddr)
  dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts]
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine segc_sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm3 hsm hpc3 hrun3 => ?_
  have hsp3 : sm3.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm, hsp2]
  have hlr3 : sm3.readReg64 .lr = fnAddr + 0x44#64 := by
    rw [hsm]; simp only [arm64_norm]; try bv_omega
  have hx0_3 : sm3.readReg64 .x0 = newPtr := by rw [hsm]; simpa [arm64_norm] using hx0_2
  have hx1_3 : sm3.readReg64 .x1 = g.ptr := by rw [hsm]; simp [arm64_norm]
  have hx2_3 : sm3.readReg64 .x2 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm]; simp [arm64_norm]
  have hx19_3 : sm3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm]; simpa [arm64_norm] using hx19_2
  have hx20_3 : sm3.readReg64 .x20 = ret := by rw [hsm]; simpa [arm64_norm] using hx20_2
  have hx21_3 : sm3.readReg64 .x21 = newPtr := by rw [hsm]; simp [arm64_norm]
  have hcs3 : segc_csUpperPreserved s0 sm3 := by
    rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs2 _ (by simp)
  have hv3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := by
    rw [hsm]; simpa [calleeSavedVRegs, arm64_norm] using hv2
  have hpres3 : AllocCallPreserved s0 sm3 := by
    rw [hsm]; exact allocCallPreserved_trans hpres2
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hpool3 : A.pool lim st' sm3 = A.pool lim st' sf2 := by rw [hsm]; simp [arm64_norm]
  have hRx3 : f3TrialRxProg.CodeLoaded sm3.mem := by rw [hsm]; simpa [arm64_norm] using hRx2
  clear hsm
  let FrameMc :=
    segc_vecGhostPayloadRest A.repAlloc g ∗ A.live newPtr g.bytes.length 1 ∗
    A.pool lim st' sf2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
    segc_retPts ret r0 r1 r2 ∗ segc_vecHdrPts p g ∗ segc_savedStack48 s0
  intro R' hm' hLP
  have hpre3 : sm3.mem ⊨ allocMemcpyVmSpec.pre (newPtr, g.ptr, g.bytes) sm3 ∗ (FrameMc ∗ R') := by
    dsimp only [allocMemcpyVmSpec, FrameMc]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_3, hx1_3, hx2_3, Nat.lt_trans hlt63 (by decide)⟩,
      Satisfies.mono (Entails.of_eq (by
        dsimp only [FrameMc, segc_savedStack48, segc_vecHdrPts, segc_retPts,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
        sep_ac_rfl)) hm'⟩
  obtain ⟨sf3, hsteps_mc, hout_mc⟩ :=
    hMemcpyRun (newPtr, g.ptr, g.bytes) (FrameMc ∗ R') sm3 hpc3 hrun3
      (by simpa [State.spAligned, hsp3] using hspAl48b) hpre3 hRx3
  have hLP_sf3 := hsteps_mc.codeLoaded hLP
  rcases hout_mc with ⟨⟨hpc_sf3, hsp_sf3, hrun_sf3⟩, ⟨_, hcs_sf3⟩, hpost_mc⟩ |
      ⟨_, hp⟩ | ⟨_, _, hex⟩ | ⟨_, ho⟩
  · rw [hlr3] at hpc_sf3
    dsimp only [allocMemcpyVmSpec] at hpost_mc
    rw [sepConj_assoc, ← sepConj_assoc ((newPtr ↦ₛ g.bytes) ∗ (g.ptr ↦ₛ g.bytes)),
      satisfies_pure_sepConj] at hpost_mc
    rcases hpost_mc with ⟨⟨_, hpres_mc, hvm_mc⟩, hpost_mc_mem⟩
    suffices hcont : SepWPp P (s0.readReg64 .lr) sf3
        (((newPtr ↦ₛ g.bytes) ∗ (g.ptr ↦ₛ g.bytes)) ∗ FrameMc)
        (segc_cloneNoOomPost A lim p ret g st R s0)
        segc_cloneNoOomPanic by
      obtain ⟨sf, hsteps_end, hout_end⟩ := hcont R' hpost_mc_mem hLP_sf3
      exact ⟨sf, hsteps_mc.trans hsteps_end, hout_end⟩
    dsimp only [FrameMc]
    have hpool_sf3 : A.pool lim st' sf3 = A.pool lim st' sf2 :=
      (A.pool_transport lim st' sm3 sf3 hvm_mc).trans hpool3
    have hsp3' : sf3.sp = s0.sp - 48#64 := hsp_sf3.trans hsp3
    have hspAl48 : decide (sf3.sp &&& 15#64 = 0#64) = true := by
      rw [hsp3']; exact decide_eq_true (beq_iff_eq.mp hspAl48b)
    have hx19_sf3 : sf3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf3.readReg64_x19.trans hx19_3
    have hx20_sf3 : sf3.readReg64 .x20 = ret := hcs_sf3.readReg64_x20.trans hx20_3
    have hx21_sf3 : sf3.readReg64 .x21 = newPtr := hcs_sf3.readReg64_x21.trans hx21_3
    have hcs_sf3_s0 : segc_csUpperPreserved s0 sf3 := segc_csUpperPreserved_trans hcs3 hcs_sf3
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts]
    segc_wp_stp64 hf17 m1 hm1; segc_wp_str64 hf18 m2 hm2
    wp_step; wp_step; wp_step; wp_step
    refine segc_sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrun_sf3])
      fun sf hsf hpcf hrunf => ?_
    have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
    have hcsf : CalleeSavedPreserved s0 sf := by
      rw [hsf]
      refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simpa [arm64_norm] using hcs_sf3_s0 .x23 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x24 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x25 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x26 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x27 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x28 (by simp),
        by simp [arm64_norm],
        by simpa [calleeSavedVRegs, arm64_norm] using hcs_sf3.vregs.trans hv3⟩
    have hpresf : AllocCallPreserved s0 sf := by
      rw [hsf]; exact allocCallPreserved_trans (allocCallPreserved_trans hpres3 hpres_mc)
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
    have hm2_0 : m2.perm = sf3.mem.perm := by
      try simp only [arm64_norm] at hm1 hm2
      exact hm2.trans hm1
    have hpoolf : A.pool lim st' sf = A.pool lim st' sf2 := by
      rw [hsf, segc_pool_setMem_perm A lim st' _ (by simpa [arm64_norm] using hm2_0)]
      simpa [arm64_norm] using hpool_sf3
    clear hsf
    refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
    have hevs : stringCloneEvents g = rustAllocEvents g.bytes.length 1 := by
      unfold stringCloneEvents; simp only [Nat.ne_of_gt hpos, ↓reduceIte]
    dsimp only [segc_cloneNoOomPost, segc_cloneFrame0, stringCloneNoOomSpec] at hmf ⊢
    rw [hevs]
    change sf.mem ⊨
      (⌜AllocCallPreserved s0 sf⌝ ∗ vecGhostAt A.repAlloc g p ∗
        vecU8 A.repAlloc ret g.bytes ∗ A.pool lim st' sf ∗
        stackAt s0.sp extHookStack) ∗ R
    rw [hpoolf, extHookStack_split_48 s0.sp]
    have hx19' : sf3.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 g.bytes.length := hx19_sf3
    have hx20' : sf3.readReg64 (Reg.gpr 20#5) = ret := hx20_sf3
    have hx21' : sf3.readReg64 (Reg.gpr 21#5) = newPtr := hx21_sf3
    try simp only [hx19', hx20', hx21', BitVec.add_zero] at hmf
    let lenBv := BitVec.ofNat 64 g.bytes.length
    have hmf1 : sf.mem ⊨
        ((segc_vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ segc_vecGhostPayloadRest A.repAlloc g)) ∗
          ((segc_retPts ret lenBv newPtr lenBv ∗
            A.live newPtr g.bytes.length 1 ∗ (newPtr ↦ₛ g.bytes)) ∗
           A.pool lim st' sf2 ∗
           (segc_savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) allocHookStack ∗ segc_cloneFrame0 s0)))) ∗ R :=
      Satisfies.mono (Entails.of_eq (by
        dsimp only [lenBv, segc_cloneFrame0, segc_savedStack48, segc_vecHdrPts, segc_retPts,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
        sep_ac_rfl)) hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmf1
    have hGhostEnt :
        (segc_vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ segc_vecGhostPayloadRest A.repAlloc g)) ⊢
        vecGhostAt A.repAlloc g p := by
      rw [segc_vecGhostAt_eq_header_payload A.repAlloc g p]
      exact sepConj_mono_right (segc_vecGhostPayload_nonempty_pack A.repAlloc g hpos)
    refine Entails.trans
      (sepConj_mono hGhostEnt
        (sepConj_mono (segc_vecU8_nonempty_pack A ret newPtr g.bytes hpos hlt63 hpNe0)
          (sepConj_mono_right (sepConj_mono_left (segc_pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
    exact Entails.pure_right hpresf (Entails.of_eq (by sep_ac_rfl))
  · dsimp only [allocMemcpyVmSpec] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [allocMemcpyVmSpec] at hex; exact False.elim (not_satisfies_false_sepConj hex)
  · dsimp only [allocMemcpyVmSpec] at ho; exact False.elim (not_satisfies_false_sepConj ho)

private theorem segc_keepMallocngFull (mmpl : MultiPlacement)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) (a : BitVec 64)
    (hsome : (mallocngLib.findCodeBlock mmpl a).isSome = true) :
    hole2_keep a = true := by
  have hsub := hole2_keepMallocng mmpl hMm a hsome
  unfold hole2_keepSub at hsub
  unfold hole2_keep
  rw [decide_eq_true_eq] at hsub ⊢
  exact Or.inr hsub

private theorem segc_sepWP_done_inv {mpl : MultiPlacement} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running →
      ExecFrozen sm.mem → f3TrialRxProg.CodeLoaded sm.mem →
      SepWPp (segc_str1ExtProg mpl) ret sm P Q Qp) :
    SepWP (segc_str1ExtProg mpl) mid s P
      (fun sm Pm => ExecFrozen sm.mem → f3TrialRxProg.CodeLoaded sm.mem →
        SepWPp (segc_str1ExtProg mpl) ret sm Pm Q Qp)
      (fun _ => ⌜False⌝) :=
  SepWP.done hpc hrun (h s rfl hpc hrun)

private theorem segc_seq_inv {mpl : MultiPlacement} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hFr : ExecFrozen s.mem) (hRx : f3TrialRxProg.CodeLoaded s.mem)
    (h : SepWP (segc_str1ExtProg mpl) mid s P
      (fun sm Pm => ExecFrozen sm.mem → f3TrialRxProg.CodeLoaded sm.mem →
        SepWPp (segc_str1ExtProg mpl) ret sm Pm Q Qp)
      (fun _ => ⌜False⌝)) :
    SepWPp (segc_str1ExtProg mpl) ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont (segc_execFrozen_of_steps_str1Ext mpl hsteps hFr)
        (segc_codeLoaded_of_keepsFrozen hRx hsteps.keepsFrozen)
        R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem segc_call_rx_shim (mpl : MultiPlacement)
    (hb : mpl.base 623 = 0x4686a0#64) {sm1 : State}
    (hFr0 : ExecFrozen sm1.mem)
    (hRx0 : f3TrialRxProg.CodeLoaded sm1.mem)
    (hpc1 : sm1.pc = 0x469640#64)
    (hrun1 : sm1.status = .Running)
    (hlr1 : sm1.readReg64 .lr = 0x4686c4#64) :
    ∃ sf1 : State,
      Steps (segc_str1ExtProg mpl) sm1 sf1 ∧
      ExecFrozen sf1.mem ∧
      f3TrialRxProg.CodeLoaded sf1.mem ∧
      sf1.pc = 0x4686c4#64 ∧
      sf1.status = .Running ∧
      sf1.sp = sm1.sp ∧
      CalleeSavedPreserved sm1 sf1 ∧
      AllocCallPreserved sm1 sf1 ∧
      VmPreserved sm1 sf1 ∧
      sf1.mem = sm1.mem := by
  have hfetch_rx : f3TrialRxProg.fetch 0x469640#64 = some (.ret .x30) :=
    fetch_instr_at0 f3Trial_seg5ShimBundle.noAllocShimV2
  have hfm_rx : f3TrialRxProg.fetchMem sm1.mem 0x469640#64 = some (.ret .x30) :=
    Program.fetchMem_of_fetch hRx0 hfetch_rx
  have hfm_real : (segc_str1ExtProg mpl).fetchMem sm1.mem sm1.pc = some (.ret .x30) := by
    rw [hpc1]
    unfold Program.fetchMem at hfm_rx ⊢
    rw [f3TrialRxProg_no_ext 0x469640#64] at hfm_rx
    rw [segc_str1ExtProg_no_ext_in_keepSub mpl hb 0x469640#64 (by decide)]
    exact hfm_rx
  have hev : (segc_str1ExtProg mpl).evalInst (.ret .x30) sm1 = sm1.setPC 0x4686c4#64 := by
    simp [Program.evalInst, execInstWithSvc, hlr1]
  have hstep : Step (segc_str1ExtProg mpl) sm1 (sm1.setPC 0x4686c4#64) :=
    hev ▸ Step.exec hrun1 hfm_real
  refine ⟨sm1.setPC 0x4686c4#64, Steps.step hstep (Steps.refl _), hFr0, hRx0,
    by cases sm1; rfl, by cases sm1; exact hrun1, by cases sm1; rfl,
    by cases sm1; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    by cases sm1; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    by cases sm1; exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩,
    by cases sm1; rfl⟩

private theorem hpeers_specStripSInvariant_fine_allocBase
    {keep : BitVec 64 → Bool}
    (γ : GhostName) (mmpl : MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) (zeroed : Bool) :
    LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.SpecStripSInvariant keep
      (rustCliAllocBudgetSpecBase fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        lim zeroed) where
  pre_eq := by
    rintro ⟨sz, al, st⟩ s
    dsimp only [rustCliAllocBudgetSpecBase]
    rw [LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.fineHookRustCliAllocBudget_pool_stripS
      γ mmpl tp brkStart hKeepMallocng lim st s]
    cases s; rfl
  post_eq := by
    rintro ⟨sz, al, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpecBase]
    rw [LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.fineHookRustCliAllocBudget_pool_stripS
      γ mmpl tp brkStart hKeepMallocng lim _ sf]
    cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := by
    rintro ⟨sz, al, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpecBase]
    cases s0; cases sf; rfl

private theorem hpeers_specPreservesFsTrace_allocBase {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (zeroed : Bool) :
    LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.SpecPreservesFsTrace
      (rustCliAllocBudgetSpecBase M A lim zeroed) := by
  intro x R s0 sf hout
  obtain ⟨hfs, htr⟩ :=
    LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.specPreservesFsTraceExact_allocBase
      A lim zeroed x R s0 sf hout
  exact ⟨hfs, FsTraced.of_eq htr (congrArg Arm64.FsState.files hfs)⟩

private theorem segc_clone_nonempty_body [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (_hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64)
    (hb : mpl.base 623 = 0x4686a0#64)
    (hCode : hasInstrs (segc_str1ExtProg mpl) 0x4686a0#64
      (rustStringCloneInstrs 0x4686a0#64 0x469640#64 0x469630#64 0x469650#64 0x468964#64))
    (p ret : BitVec 64) (g : VecGhost) (st : fineCostModel.σ)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm0 : State)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63)
    (hFits : FitsEvents fineCostModel cliBudgetLimits st (stringCloneEvents g))
    (hsp0 : s0.spAligned = true)
    (hFr_m0 : ExecFrozen sm0.mem) (hRx_m0 : f3TrialRxProg.CodeLoaded sm0.mem)
    (hpcm0 : sm0.pc = 0x4686a0#64 + 0x1c#64) (hrunm0 : sm0.status = .Running)
    (hspm0 : sm0.sp = s0.sp - 48#64) (hx0_m0 : sm0.readReg64 .x0 = p)
    (hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_m0 : sm0.readReg64 .x20 = ret) (hcsm0 : segc_csUpperPreserved s0 sm0)
    (hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0)
    (hpres0 : AllocCallPreserved s0 sm0)
    (hpool0 : (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).pool cliBudgetLimits st sm0 =
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).pool cliBudgetLimits st s0) :
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    SepWPp (segc_str1ExtProg mpl) (s0.readReg64 .lr) sm0
      (segc_vecHdrPts p g ∗ segc_vecGhostPayload A.repAlloc g ∗ A.pool cliBudgetLimits st s0 ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ segc_retPts ret r0 r1 r2 ∗ segc_savedStack48 s0)
      (segc_cloneNoOomPost A cliBudgetLimits p ret g st R s0)
      segc_cloneNoOomPanic := by
  intro A
  have hf7 := fetch_instr_at 7 hCode; change (segc_str1ExtProg mpl).fetch 0x4686bc#64 = _ at hf7
  have hf8 := fetch_instr_at 8 hCode; change (segc_str1ExtProg mpl).fetch 0x4686c0#64 = _ at hf8
  have hf9 := fetch_instr_at 9 hCode; change (segc_str1ExtProg mpl).fetch 0x4686c4#64 = _ at hf9
  have hf10 := fetch_instr_at 10 hCode; change (segc_str1ExtProg mpl).fetch 0x4686c8#64 = _ at hf10
  have hf11 := fetch_instr_at 11 hCode; change (segc_str1ExtProg mpl).fetch 0x4686cc#64 = _ at hf11
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := segc_spAligned_sub48 hspAl0
  -- Step `+0x1c .. +0x20` (`bl 0x469640`)
  apply segc_seq_inv (mid := 0x469640#64) hFr_m0 hRx_m0
  dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts]
  wp_step; wp_step
  refine segc_sepWP_done_inv rfl
    (by first | rfl | simp [arm64_norm, hrunm0]) fun sm1 hsm1 hpc1 hrun1 hFr1 hRx1 => ?_
  have hsp1 : sm1.sp = s0.sp - 48#64 := by rw [hsm1]; simp [arm64_norm, hspm0]
  have hlr1 : sm1.readReg64 .lr = 0x4686c4#64 := by
    rw [hsm1]; simp only [arm64_norm]; try bv_omega
  have hx19_1 : sm1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm1]; simp [arm64_norm, hx19_m0]
  have hx20_1 : sm1.readReg64 .x20 = ret := by rw [hsm1]; simp [arm64_norm, hx20_m0]
  have hx22_1 : sm1.readReg64 .x22 = g.ptr := by rw [hsm1]; simp [arm64_norm]
  have hcs1 : segc_csUpperPreserved s0 sm1 := by
    rw [hsm1]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcsm0 _ (by simp)
  have hv1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    rw [hsm1]; simpa [calleeSavedVRegs, arm64_norm] using hvm0
  have hpres1 : AllocCallPreserved s0 sm1 := by
    rw [hsm1]; exact allocCallPreserved_trans hpres0
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hpool1 : A.pool cliBudgetLimits st sm1 = A.pool cliBudgetLimits st s0 := by
    rw [hsm1]; simpa [arm64_norm] using hpool0
  clear hsm1
  intro RFr hm1 hL1
  obtain ⟨sf1, hsteps1, hFr_sf1, hRx_sf1, hpc_sf1, hrun_sf1, hsp_sf1, hcs_sf1, hpres_sh, hvm_sh, hmem_sf1⟩ :=
    segc_call_rx_shim mpl hb hFr1 hRx1 hpc1 hrun1 hlr1
  have hpool_sf1 : A.pool cliBudgetLimits st sf1 = A.pool cliBudgetLimits st s0 :=
    (A.pool_transport cliBudgetLimits st sm1 sf1 hvm_sh).trans hpool1
  have hsp_sf1' : sf1.sp = s0.sp - 48#64 := hsp_sf1.trans hsp1
  have hx19_sf1 : sf1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
    hcs_sf1.readReg64_x19.trans hx19_1
  have hx20_sf1 : sf1.readReg64 .x20 = ret := hcs_sf1.readReg64_x20.trans hx20_1
  have hx22_sf1 : sf1.readReg64 .x22 = g.ptr := hcs_sf1.readReg64_x22.trans hx22_1
  have hcs_sf1_s0 : segc_csUpperPreserved s0 sf1 := segc_csUpperPreserved_trans hcs1 hcs_sf1
  have hpres_s0_sf1 : AllocCallPreserved s0 sf1 := allocCallPreserved_trans hpres1 hpres_sh
  have hm_sf1 : sf1.mem ⊨
      (segc_vecHdrPts p g ∗ segc_vecGhostPayload A.repAlloc g ∗ A.pool cliBudgetLimits st s0 ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ segc_retPts ret r0 r1 r2 ∗ segc_savedStack48 s0) ∗ RFr := by
    dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts]
    rw [hmem_sf1]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
  have hL_sf1 := hsteps1.codeLoaded hL1
  suffices hwp_sf1 : SepWPp (segc_str1ExtProg mpl) (s0.readReg64 .lr) sf1
      (segc_vecHdrPts p g ∗ segc_vecGhostPayload A.repAlloc g ∗ A.pool cliBudgetLimits st s0 ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗ segc_retPts ret r0 r1 r2 ∗ segc_savedStack48 s0)
      (segc_cloneNoOomPost A cliBudgetLimits p ret g st R s0)
      segc_cloneNoOomPanic by
    obtain ⟨sf, hsteps_rest, hout_rest⟩ := hwp_sf1 RFr hm_sf1 hL_sf1
    exact ⟨sf, hsteps1.trans hsteps_rest, hout_rest⟩
  -- Step `+0x24 .. +0x2c` (`bl 0x469630`, `___rust_alloc` -> `__rdl_alloc`)
  apply segc_seq_inv (mid := 0x469630#64) hFr_sf1 hRx_sf1
  wp_step; wp_step; wp_step
  refine segc_sepWP_done_inv rfl
    (by first | rfl | simp [arm64_norm, hrun_sf1]) fun sm2 hsm2 hpc2 hrun2 hFr2 hRx2 => ?_
  have hsp2 : sm2.sp = s0.sp - 48#64 := by rw [hsm2]; simp [arm64_norm, hsp_sf1']
  have hlr2 : sm2.readReg64 .lr = 0x4686a0#64 + 0x30#64 := by
    rw [hsm2]; simp only [arm64_norm]; try bv_omega
  have hx0_2 : sm2.readReg64 .x0 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm]
  have hx1_2 : sm2.readReg64 .x1 = 1#64 := by rw [hsm2]; simp [arm64_norm]
  have hx19_2 : sm2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm, hx19_sf1]
  have hx20_2 : sm2.readReg64 .x20 = ret := by rw [hsm2]; simp [arm64_norm, hx20_sf1]
  have hx22_2 : sm2.readReg64 .x22 = g.ptr := by rw [hsm2]; simp [arm64_norm, hx22_sf1]
  have hcs2 : segc_csUpperPreserved s0 sm2 := by
    rw [hsm2]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs_sf1_s0 _ (by simp)
  have hv2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    rw [hsm2]; simpa [calleeSavedVRegs, arm64_norm] using hcs_sf1.vregs.trans hv1
  have hpres2 : AllocCallPreserved s0 sm2 := by
    rw [hsm2]; exact allocCallPreserved_trans hpres_s0_sf1
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  have hpool2 : A.pool cliBudgetLimits st sm2 = A.pool cliBudgetLimits st s0 := by
    rw [hsm2]; simpa [arm64_norm] using hpool_sf1
  clear hsm2
  intro RFr2 hm2 hL2
  let FrameAl :=
    segc_vecHdrPts p g ∗ segc_vecGhostPayload A.repAlloc g ∗ segc_retPts ret r0 r1 r2 ∗ segc_savedStack48 s0
  have hx0_nat : (sm2.readReg64 .x0).toNat = g.bytes.length := by
    rw [hx0_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx1_nat : (sm2.readReg64 .x1).toNat = 1 := by rw [hx1_2]; rfl
  have hLay : RustLayoutOk g.bytes.length 1 := ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hPreAl : sm2.mem ⊨
      (rustCliAllocBudgetSpecBase fineCostModel A cliBudgetLimits false).pre (g.bytes.length, 1, st) sm2 ∗
        (FrameAl ∗ RFr2) := by
    dsimp only [rustCliAllocBudgetSpecBase, FrameAl]
    rw [hsp2, hpool2, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_nat, hx1_nat, hLay⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2⟩
  have hSp2_al : sm2.spAligned = true := by simpa [State.spAligned, hsp2] using hspAl48b
  have hlr2_out : hole2_keepSub (sm2.readReg64 .lr) = false := by rw [hlr2]; decide
  have hRx2_sub : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keepSub sm2.mem) :=
    segc_rxProg_codeLoaded_keepSub hRx2
  obtain ⟨sf2, huntil2, _, hout2, _, _, _⟩ :=
    real_subroutine_run_of_stripS
      (keep := hole2_keepSub) (P_real := segc_str1ExtProg mpl) (P_sub := f3TrialRxProg)
      (entryTarget := 0x469630#64)
      rfl f3TrialRxProg_svc (segc_str1ExtProg_no_ext_in_keepSub mpl hb) f3TrialRxProg_no_ext
      ((hole2_stubEntries mmpl hMm γ tp).alloc cliBudgetLimits)
      (hpeers_specStripSInvariant_fine_allocBase γ mmpl tp cliElfImage.brkStart
        (hole2_keepMallocng mmpl hMm) cliBudgetLimits false)
      (hpeers_specPreservesFsTrace_allocBase _ cliBudgetLimits false)
      (fun _ s _ => by cases s; rfl)
      (fun _ _ s0' _ _ => by cases s0'; exact id)
      hrun2 hSp2_al hPreAl hFr2 hlr2_out hRx2_sub
  have hsm2_pc : sm2.setPC 0x469630#64 = sm2 := by
    cases sm2; simp [State.setPC] at hpc2 ⊢; exact hpc2.symm
  have hsteps2 : Steps (segc_str1ExtProg mpl) sm2 sf2 := hsm2_pc ▸ huntil2.toSteps
  have hL_sf2 := hsteps2.codeLoaded hL2
  have hRx_sf2 : f3TrialRxProg.CodeLoaded sf2.mem :=
    segc_codeLoaded_of_keepsFrozen hRx2 hsteps2.keepsFrozen
  have hevs_al : stringCloneEvents g = rustAllocEvents g.bytes.length 1 := by
    unfold stringCloneEvents; simp only [Nat.ne_of_gt hpos, ↓reduceIte]
  have hFits_al : FitsEvents fineCostModel cliBudgetLimits st (rustAllocEvents g.bytes.length 1) :=
    hevs_al ▸ hFits
  rcases hout2 with ⟨⟨hpc_sf2, hsp_sf2, hrun_sf2⟩, ⟨_, hcs_sf2⟩, hpost2⟩ | ⟨_, hp2⟩ | ⟨_, _, hex2⟩ | ⟨_, ho2⟩
  · rw [hlr2] at hpc_sf2
    dsimp only [rustCliAllocBudgetSpecBase] at hpost2
    rw [hsp2, sepConj_assoc, satisfies_pure_sepConj] at hpost2
    rcases hpost2 with ⟨hpres_al, hpost2_mem⟩
    have hpres_s0_sf2 : AllocCallPreserved s0 sf2 := allocCallPreserved_trans hpres2 hpres_al
    have hsp_sf2' : sf2.sp = s0.sp - 48#64 := hsp_sf2.trans hsp2
    have hx19_sf2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf2.readReg64_x19.trans hx19_2
    have hx20_sf2 : sf2.readReg64 .x20 = ret := hcs_sf2.readReg64_x20.trans hx20_2
    have hx22_sf2 : sf2.readReg64 .x22 = g.ptr := hcs_sf2.readReg64_x22.trans hx22_2
    have hcs_s0_sf2 : segc_csUpperPreserved s0 sf2 := segc_csUpperPreserved_trans hcs2 hcs_sf2
    have hv_s0_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := hcs_sf2.vregs.trans hv2
    by_cases hnull : sf2.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost2_mem
      have hPullNull :
          (A.pool cliBudgetLimits st sf2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
            ⌜NullAllowed g.bytes.length 1⌝) ∗ (FrameAl ∗ RFr2) =
          ⌜NullAllowed g.bytes.length 1⌝ ∗
            (A.pool cliBudgetLimits st sf2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗ (FrameAl ∗ RFr2)) := by
        sep_ac_rfl
      rw [hPullNull, satisfies_pure_sepConj] at hpost2_mem
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hLay hFits_al hpost2_mem.1)
    · simp only [hnull, Bool.false_eq_true, ↓reduceIte] at hpost2_mem
      let newPtr := sf2.readReg64 .x0
      have hpNe0 : newPtr ≠ 0#64 := hnull
      let st' := fineCostModel.stepEvents (rustAllocEvents g.bytes.length 1) st
      have hPullOk :
          (A.pool cliBudgetLimits st' sf2 ∗
            stackAt (s0.sp - 48#64) allocHookStack ∗
            (⌜newPtr.toNat % 1 = 0⌝ ∗ A.live newPtr g.bytes.length 1 ∗
              memRegion newPtr g.bytes.length)) ∗ (FrameAl ∗ RFr2) =
          ⌜newPtr.toNat % 1 = 0⌝ ∗
            ((memRegion newPtr g.bytes.length ∗ segc_vecGhostPayload A.repAlloc g ∗
              A.live newPtr g.bytes.length 1 ∗ A.pool cliBudgetLimits st' sf2 ∗
              stackAt (s0.sp - 48#64) allocHookStack ∗ segc_retPts ret r0 r1 r2 ∗
              segc_vecHdrPts p g ∗ segc_savedStack48 s0) ∗ RFr2) := by
        dsimp only [FrameAl, newPtr, st']; sep_ac_rfl
      rw [hPullOk, satisfies_pure_sepConj] at hpost2_mem
      have hep := segc_clone_memcpy_epilogue A cliBudgetLimits hCode
        (segc_rx_memcpy_run mpl) p ret newPtr g st r0 r1 r2 R s0 sf2
        hpos hlt63 hpNe0 hsp0 hRx_sf2 hpc_sf2 hrun_sf2 hsp_sf2' rfl hx19_sf2 hx20_sf2 hx22_sf2
        hcs_s0_sf2 hv_s0_sf2 hpres_s0_sf2
      obtain ⟨sf, hsteps3, hout3⟩ := hep RFr2 hpost2_mem.2 hL_sf2
      exact ⟨sf, hsteps2.trans hsteps3, hout3⟩
  · dsimp only [rustCliAllocBudgetSpecBase] at hp2; exact False.elim (not_satisfies_false_sepConj hp2)
  · dsimp only [rustCliAllocBudgetSpecBase] at hex2; exact False.elim (not_satisfies_false_sepConj hex2)
  · dsimp only [rustCliAllocBudgetSpecBase] at ho2
    rw [satisfies_pure_sepConj] at ho2
    exact False.elim (ho2.1.1 hFits_al)

private theorem segc_strClone_real_steps [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64)
    {x : BitVec 64 × BitVec 64 × VecGhost × fineCostModel.σ}
    {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (stringCloneNoOomSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits).pre x s0 ∗ R)
    (hReal : hole2_ActiveStrCloneRun mpl s0) :
    ∃ sf : State,
      StepsUntil (hole2_strCloneProg mpl) (SubroutineStop s0) (s0.setPC (mpl.base 623)) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome
        (stringCloneNoOomSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)
        x R s0 sf := by
  obtain ⟨hb, _, _, hmc, hhe, _⟩ := segc_mpl_pins mpl hLs
  have hCode := segc_clone_hasInstrs mpl hLs
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let s1 := s0.setPC (mpl.base 623)
  let s1' := stripS hole2_keep s1
  have hs1_pre : s1.mem ⊨ (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x s1 ∗ R := by
    change s0.mem ⊨ (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x (s0.setPC (mpl.base 623)) ∗ R
    have hpre_eq : (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x (s0.setPC (mpl.base 623)) =
        (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x s0 := by
      cases s0; rfl
    rwa [hpre_eq]
  have hInv := specStripSInvariant_fine_stringCloneNoOom γ mmpl tp cliElfImage.brkStart
    (segc_keepMallocngFull mmpl hMm) cliBudgetLimits
  have hs1'_pre : s1'.mem ⊨ (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside hole2_keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  rcases x with ⟨p, ret, g, st⟩
  have hpc1' : s1'.pc = 0x4686a0#64 := hb
  have hrun1' : s1'.status = .Running := hrun
  have hsp1' : s1'.spAligned = true := hsp0
  have hFr1' : ExecFrozen s1'.mem := segc_execFrozen_stripExecOutside hole2_keep hReal.1
  have hL1' : (segc_str1ExtProg mpl).CodeLoaded s1'.mem :=
    (segc_str1ExtProg_codeLoaded_iff mpl _).mpr hReal.2.2.1
  have hRx1' : f3TrialRxProg.CodeLoaded s1'.mem := hReal.2.2.2.1
  dsimp only [stringCloneNoOomSpec] at hs1'_pre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hs1'_pre
  rcases hs1'_pre with ⟨⟨hx0, hx8, hFits, _⟩, hrest⟩
  have hlt63 : g.bytes.length < 2 ^ 63 := by
    refine segc_vecGhostAt_bytes_lt_2pow63 (A := A.repAlloc) (m := s1'.mem) (p := p)
      (R := memRegion ret 24 ∗ (A.pool cliBudgetLimits st s1' ∗ (stackAt s1'.sp extHookStack ∗ R))) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  let P0 :=
    stackFrameAt s1'.sp 48 ∗ memRegion ret 24 ∗ vecGhostAt A.repAlloc g p ∗
    A.pool cliBudgetLimits st s1' ∗ stackAt (s1'.sp - 48#64) allocHookStack
  have hm0 : s1'.mem ⊨ P0 ∗ (segc_cloneFrame0 s1' ∗ R) := by
    dsimp only [P0, segc_cloneFrame0]
    rw [extHookStack_split_48 s1'.sp] at hrest
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  have hwp : SepWPp (segc_str1ExtProg mpl) (s1'.readReg64 .lr) s1' P0
      (segc_cloneNoOomPost A cliBudgetLimits p ret g st R s1')
      segc_cloneNoOomPanic := by
    dsimp only [P0]
    rw [segc_stackFrameAt48_eq s1'.sp, segc_memRegion24_eq_exists_pts ret,
        segc_vecGhostAt_eq_header_payload A.repAlloc g p]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
      SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun st0 =>
      SepWPp.exists_elim fun st1 => SepWPp.exists_elim fun st2 =>
      SepWPp.exists_elim fun st3 => SepWPp.exists_elim fun st4 =>
      SepWPp.exists_elim fun st5 => ?_
    have hf0 := fetch_instr_at0 hCode
    have hf1 := fetch_instr_at 1 hCode; change (segc_str1ExtProg mpl).fetch 0x4686a4#64 = _ at hf1
    have hf2 := fetch_instr_at 2 hCode; change (segc_str1ExtProg mpl).fetch 0x4686a8#64 = _ at hf2
    have hf3 := fetch_instr_at 3 hCode; change (segc_str1ExtProg mpl).fetch 0x4686ac#64 = _ at hf3
    have hf4 := fetch_instr_at 4 hCode; change (segc_str1ExtProg mpl).fetch 0x4686b0#64 = _ at hf4
    have hf5 := fetch_instr_at 5 hCode; change (segc_str1ExtProg mpl).fetch 0x4686b4#64 = _ at hf5
    have hf6 := fetch_instr_at 6 hCode; change (segc_str1ExtProg mpl).fetch 0x4686b8#64 = _ at hf6
    have hspAl0 : (s1'.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp1'
    have hspAl48 : decide ((s1'.sp - 48#64) &&& 15#64 = 0#64) = true :=
      decide_eq_true (beq_iff_eq.mp (segc_spAligned_sub48 hspAl0))
    by_cases hbs : g.bytes = []
    · have hlen0 : BitVec.ofNat 64 g.bytes.length = 0#64 := by simp [hbs]
      apply SepWPp.of_sepWP (mid := 0x4686a0#64 + 0x5c#64)
      segc_wp_stp64 hf0 m1 hm1; segc_wp_stp64 hf1 m2 hm2; segc_wp_stp64 hf2 m3 hm3
      wp_step; wp_step; wp_step; wp_step
      refine segc_sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
        (by simp [arm64_norm, hrun1']) fun sm hsm hpcm hrunm => ?_
      have hspm : sm.sp = s1'.sp - 48#64 := by rw [hsm]; simp [arm64_norm]
      have hx19m : sm.readReg64 .x19 = 0#64 := by rw [hsm]; simp [arm64_norm]
      have hx20m : sm.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm]
      have hcsm : segc_csUpperPreserved s1' sm := by
        rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
      have hvm : calleeSavedVRegs sm = calleeSavedVRegs s1' := by
        rw [hsm]; simp [calleeSavedVRegs, arm64_norm]
      have hpresm : AllocCallPreserved s1' sm := by
        rw [hsm]; exact
          ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
           by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
      have hm3_0 : m3.perm = s1'.mem.perm := by
        try simp only [arm64_norm] at hm1 hm2 hm3
        exact hm3.trans (hm2.trans hm1)
      have hpoolm : A.pool cliBudgetLimits st sm = A.pool cliBudgetLimits st s1' := by
        rw [hsm, segc_pool_setMem_perm A cliBudgetLimits st _ (by simpa [arm64_norm] using hm3_0)]
        simp [arm64_norm]
      clear hsm
      refine SepWPp.weaken_pre ?_ (segc_clone_empty_epilogue A cliBudgetLimits hCode p ret g st
        r0 r1 r2 R s1' sm hbs hsp1' hpcm hrunm hspm hx19m hx20m hcsm hvm hpresm hpoolm)
      exact Entails.of_eq (by
        dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
        sep_ac_rfl)
    · have hpos : 0 < g.bytes.length := List.length_pos_iff.mpr hbs
      have hlenNe0 : BitVec.ofNat 64 g.bytes.length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change g.bytes.length = 0 at this; omega
      apply segc_seq_inv (mid := 0x4686a0#64 + 0x1c#64) hFr1' hRx1'
      segc_wp_stp64 hf0 m1 hm1; segc_wp_stp64 hf1 m2 hm2; segc_wp_stp64 hf2 m3 hm3
      wp_step; wp_step; wp_step; wp_step
      refine segc_sepWP_done_inv (by first | rfl | (simp [arm64_norm, beq_false_of_ne hlenNe0]; try bv_omega))
        (by first | rfl | simp [arm64_norm, hrun1']) fun sm0 hsm0 hpcm0 hrunm0 hFr_m0 hRx_m0 => ?_
      have hspm0 : sm0.sp = s1'.sp - 48#64 := by rw [hsm0]; simp [arm64_norm]
      have hx0_m0 : sm0.readReg64 .x0 = p := by rw [hsm0]; simp [arm64_norm, hx0]
      have hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
        rw [hsm0]; simp [arm64_norm]
      have hx20_m0 : sm0.readReg64 .x20 = ret := by rw [hsm0]; simp [arm64_norm]
      have hcsm0 : segc_csUpperPreserved s1' sm0 := by
        rw [hsm0]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
      have hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s1' := by
        rw [hsm0]; simp [calleeSavedVRegs, arm64_norm]
      have hpres0 : AllocCallPreserved s1' sm0 := by
        rw [hsm0]; exact
          ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
           by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
      have hm3_0 : m3.perm = s1'.mem.perm := by
        try simp only [arm64_norm] at hm1 hm2 hm3
        exact hm3.trans (hm2.trans hm1)
      have hpool0 : A.pool cliBudgetLimits st sm0 = A.pool cliBudgetLimits st s1' := by
        rw [hsm0, segc_pool_setMem_perm A cliBudgetLimits st _ (by simpa [arm64_norm] using hm3_0)]
        simp [arm64_norm]
      clear hsm0
      refine SepWPp.weaken_pre ?_
        (segc_clone_nonempty_body mpl mmpl hLs hMm γ tp hb hCode p ret g st r0 r1 r2 R s1' sm0
          hpos hlt63 hFits hsp1' hFr_m0 hRx_m0 hpcm0 hrunm0 hspm0 hx0_m0 hx19_m0 hx20_m0
          hcsm0 hvm0 hpres0 hpool0)
      exact Entails.of_eq (by
        dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
        sep_ac_rfl)
  obtain ⟨sf', hsteps_ext', hout_wp⟩ := hwp (segc_cloneFrame0 s1' ∗ R) hm0 hL1'
  rcases hout_wp with ⟨hpcf', hrunf', P_f, hmf', hq', hspf', hcsf'⟩ | ⟨_, _, _, hqp'⟩ | ⟨_, hmo'⟩
  · have hout1' : SubroutineOutcome (stringCloneNoOomSpec fineCostModel A cliBudgetLimits)
        (p, ret, g, st) R s1' sf' :=
      Or.inl ⟨⟨hpcf', hspf', hrunf'⟩, ⟨hspf', hcsf'⟩, hq' hmf'⟩
    have hstop1' : SubroutineStop s1' sf' := segc_subroutineOutcome_to_stop hout1'
    have hstop0' : SubroutineStop s0 sf' := hstop1'
    have hnhalt' : sf'.status ≠ .Halted := segc_subroutineOutcome_not_halted hout1'
    have hsteps_sc' : Steps (hole2_strCloneProg mpl) s1' sf' :=
      segc_steps_to_strClone mpl hb hmc hhe hsteps_ext'
    obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
      segc_stepsUntil_of_stripS_sameProg (keep := hole2_keep) (P := hole2_strCloneProg mpl)
        (s0 := s0) rfl (segc_strCloneProg_ext_comm mpl hmc hhe hReal.2.1) hReal.2.1
        hsteps_sc' hstop0' hnhalt' s1 rfl hReal.1
    rw [hsf_eq] at hout1'
    have hout1 : SubroutineOutcome (stringCloneNoOomSpec fineCostModel A cliBudgetLimits)
        (p, ret, g, st) R s1 sf := by
      rcases hout1' with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, hc', hex'⟩ | ⟨ho', hoom'⟩
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · exact ⟨by simpa [s1', segc_stripS_pc, segc_stripS_r64] using hret'.1,
                 by simpa [s1'] using hret'.2.1,
                 by simpa [s1', segc_stripS_status] using hret'.2.2⟩
        · dsimp only [s1'] at hcc'
          exact ⟨by simpa using hcc'.1,
                 segc_calleeSavedPreserved_stripS hcc'.2⟩
        · dsimp only [s1'] at hpost'
          rw [hInv.post_eq (p, ret, g, st) s1 sf] at hpost'
          exact satisfies_of_stripExecOutside hfr_sf hpost'
      · dsimp only [s1'] at hp' hpan'
        refine Or.inr (Or.inl ⟨by simpa [segc_stripS_status] using hp', ?_⟩)
        rw [hInv.onPanic_eq (p, ret, g, st) s1 sf] at hpan'
        exact satisfies_of_stripExecOutside hfr_sf hpan'
      · dsimp only [s1'] at hc' hex'
        refine Or.inr (Or.inr (Or.inl ⟨c, by simpa [segc_stripS_status] using hc', ?_⟩))
        rw [hInv.onExit_eq (p, ret, g, st) c s1 sf] at hex'
        exact satisfies_of_stripExecOutside hfr_sf hex'
      · dsimp only [s1'] at ho' hoom'
        refine Or.inr (Or.inr (Or.inr ⟨by simpa [segc_stripS_status] using ho', ?_⟩))
        rw [hInv.onOom_eq (p, ret, g, st) s1 sf] at hoom'
        exact satisfies_of_stripExecOutside hfr_sf hoom'
    have hout0 : SubroutineOutcome (stringCloneNoOomSpec fineCostModel A cliBudgetLimits)
        (p, ret, g, st) R s0 sf := by
      change SubroutineOutcome (stringCloneNoOomSpec fineCostModel A cliBudgetLimits)
        (p, ret, g, st) R (s0.setPC (mpl.base 623)) sf at hout1
      cases s0; exact hout1
    exact ⟨sf, huntil, hstop_sf, hout0⟩
  · exact False.elim hqp'
  · exact False.elim (not_satisfies_false_sepConj hmo')

private theorem segc_strCloneGhostHook_fsT [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    HookFsTraced IsFsC (hole2_strCloneGhostHook mpl mmpl) := by
  classical
  intro s0
  unfold hole2_strCloneGhostHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.1
    · exact keepFsTrace_fsT _ s0
  · exact FsTraced.of_eq rfl rfl

private theorem segc_strCloneGhostHook_ok [LibsignalPlacement]
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64) :
    HookOk (hole2_strCloneGhostHook mpl mmpl)
      (stringCloneBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) := by
  apply hookOk_stringCloneBudget_of_noOom
  classical
  intro x R s0 hrun hpre hsp
  let specOf := fun γ' tp' => stringCloneNoOomSpec fineCostModel
    (fineHookRustCliAllocBudget γ' mmpl tp' cliElfImage.brkStart) cliBudgetLimits
  have hActPre : ActiveF3CallPre specOf s0 := ⟨hrun, hsp, γ, tp, x, R, hpre⟩
  have hEq : hole2_strCloneGhostHook mpl mmpl s0 =
      (if hReal : hole2_ActiveStrCloneRun mpl s0 then Classical.choose hReal.2.2.2.2
       else keepFsTrace (f3StringCloneFallback mmpl) s0) := by
    unfold hole2_strCloneGhostHook
    exact dite_eq_left_of_eq_true (eq_true hActPre)
  rw [hEq]
  by_cases hReal : hole2_ActiveStrCloneRun mpl s0
  · rw [dite_eq_left_of_eq_true (eq_true hReal)]
    obtain ⟨sf, huntil, hstop, hout⟩ :=
      segc_strClone_real_steps mpl mmpl hLs hMm γ tp hrun hsp hpre hReal
    have hchoose := Classical.choose_spec hReal.2.2.2.2
    have hdet : Classical.choose hReal.2.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · rw [dite_eq_right_of_eq_false (eq_false hReal)]
    have hFbOk : HookOk (keepFsTrace (f3StringCloneFallback mmpl)) (specOf γ tp) := by
      have hidem : keepFsTrace (f3StringCloneFallback mmpl) = f3StringCloneFallback mmpl :=
        funext fun _ => rfl
      rw [hidem]
      exact f3StringCloneFallback_ok_noOom_fine cliElfImage.brkStart cliBudgetLimits
        (hole2_hPl_mng mmpl hMm) γ tp
    exact hFbOk x R s0 hrun hpre hsp

private theorem g1fr_strCloneProg_ext_keep (mpl : MultiPlacement)
    (_hmc : mpl.ρ "memcpy" = 0x469650#64)
    (_hhe : mpl.ρ f3HandleErrorSym = 0x468964#64)
    (pc : BitVec 64) (f : State → State)
    (he : (hole2_strCloneProg mpl).externAt? pc = some f) :
    hole2_keep pc = true := by
  unfold Program.externAt? Program.hookAtOff? hole2_strCloneProg at he
  dsimp only [List.findSome?, Option.or] at he
  cases he

private theorem g1fr_stepsUntil_of_stripS_sameProg_keep
    {keep : BitVec 64 → Bool} {P : Program} {s0 : State}
    (hsvc : P.svc = Arm64.Syscall.standard)
    (hext_comm : ∀ (pc : BitVec 64) (f : State → State),
      P.externAt? pc = some f →
      pc ≠ s0.readReg64 .lr ∧
      (∀ st : State, ExecFrozen st.mem →
        (stripExecOutside keep st.mem).KeepsFrozen (f (stripS keep st)).mem →
        f (stripS keep st) = stripS keep (f st) ∧
        ExecFrozen (f st).mem ∧
        st.mem.KeepsFrozen (f st).mem ∧
        (f st).symtab = st.symtab))
    (hext_keep : ∀ (pc : BitVec 64) (f : State → State),
      P.externAt? pc = some f → keep pc = true)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    {s1' sf' : State}
    (hsteps : Steps P s1' sf')
    (hstop' : SubroutineStop s0 sf')
    (hnhalt' : sf'.status ≠ .Halted) :
    ∀ s1 : State,
      s1' = stripS keep s1 →
      ExecFrozen s1.mem →
      ∃ sf : State,
        StepsUntil P (SubroutineStop s0) s1 sf ∧
        StepsUntil P (fun st => SubroutineStop s0 st ∨ keep st.pc = false) s1 sf ∧
        SubroutineStop s0 sf ∧
        sf' = stripS keep sf ∧
        ExecFrozen sf.mem := by
  induction hsteps with
  | refl s' =>
    intro s1 hs1 hfr1
    exact ⟨s1, StepsUntil.refl s1, StepsUntil.refl s1,
      segc_subroutineStop_stripS_iff.mp (hs1 ▸ hstop'), hs1, hfr1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro sa hsa hfra
    by_cases hstop_sa : SubroutineStop s0 sa
    · rcases hstop_sa with ⟨hpc_lr, _⟩ | hpan | ⟨_, hex⟩ | hoom
      · cases h1 with
        | @exec inst hr' hfm' =>
          rw [hsa, segc_stripS_pc, segc_stripS_mem] at hfm'
          unfold Program.fetchMem at hfm'
          cases he : P.externAt? sa.pc with
          | some f => simp [he] at hfm'
          | none =>
            simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
            by_cases hal : sa.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
              by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
              · have hx0 : ((stripExecOutside keep sa.mem).perm sa.pc).x = true := by
                  have h4 :
                      ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                      ((stripExecOutside keep sa.mem).allPerm (·.x) (sa.pc + 1#64) 3) = true := by
                    simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true] using hce'
                  exact h4.1
                have hkp := (strip_perm_x_imp hx0).2
                rw [hpc_lr, hlr_out] at hkp; cases hkp
              · simp [hce'] at hfm'
            · simp [hal] at hfm'
        | halt_unmapped _ _ _ => exact False.elim (hnhalt' (segc_steps_preserves_halted hrest rfl))
        | extern _ he _ _ =>
          rw [hsa, segc_stripS_pc] at he; exact False.elim ((hext_comm sa.pc _ he).1 hpc_lr)
        | extern_fault _ he _ =>
          rw [hsa, segc_stripS_pc] at he; exact False.elim ((hext_comm sa.pc _ he).1 hpc_lr)
      · have hr_sa : sa.status = .Running := by have h := segc_step_running h1; rwa [hsa, segc_stripS_status] at h
        rw [hpan] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by have h := segc_step_running h1; rwa [hsa, segc_stripS_status] at h
        rw [hex] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by have h := segc_step_running h1; rwa [hsa, segc_stripS_status] at h
        rw [hoom] at hr_sa; cases hr_sa
    · cases h1 with
      | halt_unmapped _ _ _ => exact False.elim (hnhalt' (segc_steps_preserves_halted hrest rfl))
      | @extern f hr' he' hkf' _ =>
        have hra : sa.status = .Running := by rw [hsa, segc_stripS_status] at hr'; exact hr'
        rw [hsa, segc_stripS_pc] at he'
        rw [hsa] at hkf'
        obtain ⟨_, hf_comm⟩ := hext_comm sa.pc f he'
        obtain ⟨hf_eq, hfr_f, hkf_f, hsym_f⟩ := hf_comm sa hfra hkf'
        have hstep_real : Step P sa (f sa) := Step.extern hra he' hkf_f hsym_f
        have hkp_sa : keep sa.pc = true := hext_keep sa.pc f he'
        have hstop_kp : ¬ (SubroutineStop s0 sa ∨ keep sa.pc = false) := by
          rintro (hst | hkpf)
          · exact hstop_sa hst
          · rw [hkp_sa] at hkpf; cases hkpf
        rw [hsa, hf_eq] at hrest ih
        obtain ⟨sf, huntil_rest, huntil_kp_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
          ih hstop' hnhalt' (f sa) rfl hfr_f
        exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
          StepsUntil.step hstop_kp hstep_real huntil_kp_rest, hstop_sf, hsf_eq, hfr_sf⟩
      | extern_fault _ _ _ =>
        have hsf_ex := segc_steps_preserves_exception hrest rfl
        rcases hstop' with ⟨_, _, hr_sf⟩ | hpan | ⟨_, hex⟩ | hoom
        · rw [hsf_ex] at hr_sf; cases hr_sf
        · rw [hsf_ex] at hpan; cases hpan
        · rw [hsf_ex] at hex; cases hex
        · rw [hsf_ex] at hoom; cases hoom
      | @exec inst hr' hfm' =>
        have hra : sa.status = .Running := by rw [hsa, segc_stripS_status] at hr'; exact hr'
        rw [hsa, segc_stripS_pc, segc_stripS_mem] at hfm'
        unfold Program.fetchMem at hfm'
        cases he_sub : P.externAt? sa.pc with
        | some f => simp [he_sub] at hfm'
        | none =>
          simp only [he_sub, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
          by_cases hal_pc : sa.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
            by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
            · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
              have hx4 :
                  ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 1#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 2#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 3#64)).x = true := by
                simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
              have hkp_sa : keep sa.pc = true := (strip_perm_x_imp hx4.1).2
              have hstop_kp : ¬ (SubroutineStop s0 sa ∨ keep sa.pc = false) := by
                rintro (hst | hkpf)
                · exact hstop_sa hst
                · rw [hkp_sa] at hkpf; cases hkpf
              have hce : sa.mem.canExec sa.pc 4 = true := by
                simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc,
                  (strip_perm_x_imp hx4.1).1, (strip_perm_x_imp hx4.2.1).1,
                  (strip_perm_x_imp hx4.2.2.1).1, (strip_perm_x_imp hx4.2.2.2).1]
              have hr32 : (stripExecOutside keep sa.mem).read32 sa.pc = sa.mem.read32 sa.pc := by
                simp [Memory.read32, strip_read8]
              rw [hr32] at hfm'
              have hfm_real : P.fetchMem sa.mem sa.pc = some inst := by
                unfold Program.fetchMem; simp [he_sub, hal_pc, hce, hfm']
              by_cases hsvc0 : inst.isSvc0 = true
              · have hinst : inst = .system false 0#16 := by
                  cases inst <;> simp [Instr.isSvc0] at hsvc0
                  rcases hsvc0 with ⟨rfl, rfl⟩; rfl
                subst hinst
                obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keep) hfra
                have hev_strip : P.evalInst (.system false 0#16) (stripS keep sa) =
                    stripS keep (Arm64.Syscall.standard sa) := by
                  simp [Program.evalInst, execInstWithSvc, hsvc, hcomm]
                have hev_real : P.evalInst (.system false 0#16) sa = Arm64.Syscall.standard sa := by
                  simp [Program.evalInst, execInstWithSvc, hsvc]
                have hstep_real : Step P sa (Arm64.Syscall.standard sa) := hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, huntil_kp_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                  ih hstop' hnhalt' (Arm64.Syscall.standard sa) rfl hfr_sb
                exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
                  StepsUntil.step hstop_kp hstep_real huntil_kp_rest, hstop_sf, hsf_eq, hfr_sf⟩
              · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
                have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 sa
                have hfr_sb : ExecFrozen (execInst inst sa).mem :=
                  ExecFrozen.of_perm_eq hfra (congrFun hpf.2.1)
                have hev_strip : P.evalInst inst (stripS keep sa) = stripS keep (execInst inst sa) := by
                  rw [ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0 P hnsvc0, execInst_stripS hnsvc0]
                have hev_real : P.evalInst inst sa = execInst inst sa :=
                  ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0 P hnsvc0 sa
                have hstep_real : Step P sa (execInst inst sa) := hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, huntil_kp_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                  ih hstop' hnhalt' (execInst inst sa) rfl hfr_sb
                exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
                  StepsUntil.step hstop_kp hstep_real huntil_kp_rest, hstop_sf, hsf_eq, hfr_sf⟩
            · simp [hce'] at hfm'
          · simp [hal_pc] at hfm'

private theorem g1fr_strClone_real_steps_core
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64)
    {x : BitVec 64 × BitVec 64 × VecGhost × fineCostModel.σ}
    {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hpre :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      s0.mem ⊨
        (stringCloneNoOomSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits).pre x s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr : hole2_keep (s0.readReg64 .lr) = false)
    (hCodeStr1 : (hole2_str1Prog mpl).CodeLoaded (stripExecOutside hole2_keep s0.mem))
    (hCodeRx : f3TrialRxProg.CodeLoaded (stripExecOutside hole2_keep s0.mem)) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∃ sf : State,
      StepsUntil (hole2_strCloneProg mpl) (SubroutineStop s0) (s0.setPC (mpl.base 623)) sf ∧
      StepsUntil (hole2_strCloneProg mpl)
        (fun st => SubroutineStop s0 st ∨ hole2_keep st.pc = false)
        (s0.setPC (mpl.base 623)) sf ∧
      Steps (hole2_strCloneProg mpl)
        (stripS hole2_keep (s0.setPC (mpl.base 623))) (stripS hole2_keep sf) ∧
      SubroutineStop s0 (stripS hole2_keep sf) ∧
      (stripS hole2_keep sf).status ≠ .Halted ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome
        (stringCloneNoOomSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)
        x R s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  obtain ⟨hb, _, _, hmc, hhe, _⟩ := segc_mpl_pins mpl hLs
  have hCode := segc_clone_hasInstrs mpl hLs
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let s1 := s0.setPC (mpl.base 623)
  let s1' := stripS hole2_keep s1
  have hs1_pre : s1.mem ⊨ (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x s1 ∗ R := by
    change s0.mem ⊨ (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x (s0.setPC (mpl.base 623)) ∗ R
    have hpre_eq : (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x (s0.setPC (mpl.base 623)) =
        (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x s0 := by
      cases s0; rfl
    rwa [hpre_eq]
  have hInv := specStripSInvariant_fine_stringCloneNoOom γ mmpl tp cliElfImage.brkStart
    (segc_keepMallocngFull mmpl hMm) cliBudgetLimits
  have hs1'_pre : s1'.mem ⊨ (stringCloneNoOomSpec fineCostModel A cliBudgetLimits).pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside hole2_keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  rcases x with ⟨p, ret, g, st⟩
  have hpc1' : s1'.pc = 0x4686a0#64 := hb
  have hrun1' : s1'.status = .Running := hrun
  have hsp1' : s1'.spAligned = true := hsp0
  have hFr1' : ExecFrozen s1'.mem := segc_execFrozen_stripExecOutside hole2_keep hFr
  have hL1' : (segc_str1ExtProg mpl).CodeLoaded s1'.mem :=
    (segc_str1ExtProg_codeLoaded_iff mpl _).mpr hCodeStr1
  have hRx1' : f3TrialRxProg.CodeLoaded s1'.mem := hCodeRx
  dsimp only [stringCloneNoOomSpec] at hs1'_pre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hs1'_pre
  rcases hs1'_pre with ⟨⟨hx0, hx8, hFits, _⟩, hrest⟩
  have hlt63 : g.bytes.length < 2 ^ 63 := by
    refine segc_vecGhostAt_bytes_lt_2pow63 (A := A.repAlloc) (m := s1'.mem) (p := p)
      (R := memRegion ret 24 ∗ (A.pool cliBudgetLimits st s1' ∗ (stackAt s1'.sp extHookStack ∗ R))) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  let P0 :=
    stackFrameAt s1'.sp 48 ∗ memRegion ret 24 ∗ vecGhostAt A.repAlloc g p ∗
    A.pool cliBudgetLimits st s1' ∗ stackAt (s1'.sp - 48#64) allocHookStack
  have hm0 : s1'.mem ⊨ P0 ∗ (segc_cloneFrame0 s1' ∗ R) := by
    dsimp only [P0, segc_cloneFrame0]
    rw [extHookStack_split_48 s1'.sp] at hrest
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  have hwp : SepWPp (segc_str1ExtProg mpl) (s1'.readReg64 .lr) s1' P0
      (segc_cloneNoOomPost A cliBudgetLimits p ret g st R s1')
      segc_cloneNoOomPanic := by
    dsimp only [P0]
    rw [segc_stackFrameAt48_eq s1'.sp, segc_memRegion24_eq_exists_pts ret,
        segc_vecGhostAt_eq_header_payload A.repAlloc g p]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
      SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun st0 =>
      SepWPp.exists_elim fun st1 => SepWPp.exists_elim fun st2 =>
      SepWPp.exists_elim fun st3 => SepWPp.exists_elim fun st4 =>
      SepWPp.exists_elim fun st5 => ?_
    have hf0 := fetch_instr_at0 hCode
    have hf1 := fetch_instr_at 1 hCode; change (segc_str1ExtProg mpl).fetch 0x4686a4#64 = _ at hf1
    have hf2 := fetch_instr_at 2 hCode; change (segc_str1ExtProg mpl).fetch 0x4686a8#64 = _ at hf2
    have hf3 := fetch_instr_at 3 hCode; change (segc_str1ExtProg mpl).fetch 0x4686ac#64 = _ at hf3
    have hf4 := fetch_instr_at 4 hCode; change (segc_str1ExtProg mpl).fetch 0x4686b0#64 = _ at hf4
    have hf5 := fetch_instr_at 5 hCode; change (segc_str1ExtProg mpl).fetch 0x4686b4#64 = _ at hf5
    have hf6 := fetch_instr_at 6 hCode; change (segc_str1ExtProg mpl).fetch 0x4686b8#64 = _ at hf6
    have hspAl0 : (s1'.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp1'
    have hspAl48 : decide ((s1'.sp - 48#64) &&& 15#64 = 0#64) = true :=
      decide_eq_true (beq_iff_eq.mp (segc_spAligned_sub48 hspAl0))
    by_cases hbs : g.bytes = []
    · have hlen0 : BitVec.ofNat 64 g.bytes.length = 0#64 := by simp [hbs]
      apply SepWPp.of_sepWP (mid := 0x4686a0#64 + 0x5c#64)
      segc_wp_stp64 hf0 m1 hm1; segc_wp_stp64 hf1 m2 hm2; segc_wp_stp64 hf2 m3 hm3
      wp_step; wp_step; wp_step; wp_step
      refine segc_sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
        (by simp [arm64_norm, hrun1']) fun sm hsm hpcm hrunm => ?_
      have hspm : sm.sp = s1'.sp - 48#64 := by rw [hsm]; simp [arm64_norm]
      have hx19m : sm.readReg64 .x19 = 0#64 := by rw [hsm]; simp [arm64_norm]
      have hx20m : sm.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm]
      have hcsm : segc_csUpperPreserved s1' sm := by
        rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
      have hvm : calleeSavedVRegs sm = calleeSavedVRegs s1' := by
        rw [hsm]; simp [calleeSavedVRegs, arm64_norm]
      have hpresm : AllocCallPreserved s1' sm := by
        rw [hsm]; exact
          ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
           by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
      have hm3_0 : m3.perm = s1'.mem.perm := by
        try simp only [arm64_norm] at hm1 hm2 hm3
        exact hm3.trans (hm2.trans hm1)
      have hpoolm : A.pool cliBudgetLimits st sm = A.pool cliBudgetLimits st s1' := by
        rw [hsm, segc_pool_setMem_perm A cliBudgetLimits st _ (by simpa [arm64_norm] using hm3_0)]
        simp [arm64_norm]
      clear hsm
      refine SepWPp.weaken_pre ?_ (segc_clone_empty_epilogue A cliBudgetLimits hCode p ret g st
        r0 r1 r2 R s1' sm hbs hsp1' hpcm hrunm hspm hx19m hx20m hcsm hvm hpresm hpoolm)
      exact Entails.of_eq (by
        dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
        sep_ac_rfl)
    · have hpos : 0 < g.bytes.length := List.length_pos_iff.mpr hbs
      have hlenNe0 : BitVec.ofNat 64 g.bytes.length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change g.bytes.length = 0 at this; omega
      apply segc_seq_inv (mid := 0x4686a0#64 + 0x1c#64) hFr1' hRx1'
      segc_wp_stp64 hf0 m1 hm1; segc_wp_stp64 hf1 m2 hm2; segc_wp_stp64 hf2 m3 hm3
      wp_step; wp_step; wp_step; wp_step
      refine segc_sepWP_done_inv (by first | rfl | (simp [arm64_norm, beq_false_of_ne hlenNe0]; try bv_omega))
        (by first | rfl | simp [arm64_norm, hrun1']) fun sm0 hsm0 hpcm0 hrunm0 hFr_m0 hRx_m0 => ?_
      have hspm0 : sm0.sp = s1'.sp - 48#64 := by rw [hsm0]; simp [arm64_norm]
      have hx0_m0 : sm0.readReg64 .x0 = p := by rw [hsm0]; simp [arm64_norm, hx0]
      have hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
        rw [hsm0]; simp [arm64_norm]
      have hx20_m0 : sm0.readReg64 .x20 = ret := by rw [hsm0]; simp [arm64_norm]
      have hcsm0 : segc_csUpperPreserved s1' sm0 := by
        rw [hsm0]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
      have hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s1' := by
        rw [hsm0]; simp [calleeSavedVRegs, arm64_norm]
      have hpres0 : AllocCallPreserved s1' sm0 := by
        rw [hsm0]; exact
          ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
           by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
      have hm3_0 : m3.perm = s1'.mem.perm := by
        try simp only [arm64_norm] at hm1 hm2 hm3
        exact hm3.trans (hm2.trans hm1)
      have hpool0 : A.pool cliBudgetLimits st sm0 = A.pool cliBudgetLimits st s1' := by
        rw [hsm0, segc_pool_setMem_perm A cliBudgetLimits st _ (by simpa [arm64_norm] using hm3_0)]
        simp [arm64_norm]
      clear hsm0
      refine SepWPp.weaken_pre ?_
        (segc_clone_nonempty_body mpl mmpl hLs hMm γ tp hb hCode p ret g st r0 r1 r2 R s1' sm0
          hpos hlt63 hFits hsp1' hFr_m0 hRx_m0 hpcm0 hrunm0 hspm0 hx0_m0 hx19_m0 hx20_m0
          hcsm0 hvm0 hpres0 hpool0)
      exact Entails.of_eq (by
        dsimp only [segc_retPts, segc_savedStack48, segc_vecHdrPts,
          Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
        sep_ac_rfl)
  obtain ⟨sf', hsteps_ext', hout_wp⟩ := hwp (segc_cloneFrame0 s1' ∗ R) hm0 hL1'
  rcases hout_wp with ⟨hpcf', hrunf', P_f, hmf', hq', hspf', hcsf'⟩ | ⟨_, _, _, hqp'⟩ | ⟨_, hmo'⟩
  · have hout1' : SubroutineOutcome (stringCloneNoOomSpec fineCostModel A cliBudgetLimits)
        (p, ret, g, st) R s1' sf' :=
      Or.inl ⟨⟨hpcf', hspf', hrunf'⟩, ⟨hspf', hcsf'⟩, hq' hmf'⟩
    have hstop1' : SubroutineStop s1' sf' := segc_subroutineOutcome_to_stop hout1'
    have hstop0' : SubroutineStop s0 sf' := hstop1'
    have hnhalt' : sf'.status ≠ .Halted := segc_subroutineOutcome_not_halted hout1'
    have hsteps_sc' : Steps (hole2_strCloneProg mpl) s1' sf' :=
      segc_steps_to_strClone mpl hb hmc hhe hsteps_ext'
    obtain ⟨sf, huntil, huntil_kp, hstop_sf, hsf_eq, hfr_sf⟩ :=
      g1fr_stepsUntil_of_stripS_sameProg_keep (keep := hole2_keep) (P := hole2_strCloneProg mpl)
        (s0 := s0) rfl (segc_strCloneProg_ext_comm mpl hmc hhe hlr)
        (g1fr_strCloneProg_ext_keep mpl hmc hhe) hlr
        hsteps_sc' hstop0' hnhalt' s1 rfl hFr
    have hsteps_strip :
        Steps (hole2_strCloneProg mpl)
          (stripS hole2_keep (s0.setPC (mpl.base 623))) (stripS hole2_keep sf) := by
      simpa [s1', s1, hsf_eq] using hsteps_sc'
    have hstop_strip : SubroutineStop s0 (stripS hole2_keep sf) := hsf_eq ▸ hstop0'
    have hnhalt_strip : (stripS hole2_keep sf).status ≠ .Halted := hsf_eq ▸ hnhalt'
    rw [hsf_eq] at hout1'
    have hout1 : SubroutineOutcome (stringCloneNoOomSpec fineCostModel A cliBudgetLimits)
        (p, ret, g, st) R s1 sf := by
      rcases hout1' with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, hc', hex'⟩ | ⟨ho', hoom'⟩
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · exact ⟨by simpa [s1', segc_stripS_pc, segc_stripS_r64] using hret'.1,
                 by simpa [s1'] using hret'.2.1,
                 by simpa [s1', segc_stripS_status] using hret'.2.2⟩
        · dsimp only [s1'] at hcc'
          exact ⟨by simpa using hcc'.1,
                 segc_calleeSavedPreserved_stripS hcc'.2⟩
        · dsimp only [s1'] at hpost'
          rw [hInv.post_eq (p, ret, g, st) s1 sf] at hpost'
          exact satisfies_of_stripExecOutside hfr_sf hpost'
      · dsimp only [s1'] at hp' hpan'
        refine Or.inr (Or.inl ⟨by simpa [segc_stripS_status] using hp', ?_⟩)
        rw [hInv.onPanic_eq (p, ret, g, st) s1 sf] at hpan'
        exact satisfies_of_stripExecOutside hfr_sf hpan'
      · dsimp only [s1'] at hc' hex'
        refine Or.inr (Or.inr (Or.inl ⟨c, by simpa [segc_stripS_status] using hc', ?_⟩))
        rw [hInv.onExit_eq (p, ret, g, st) c s1 sf] at hex'
        exact satisfies_of_stripExecOutside hfr_sf hex'
      · dsimp only [s1'] at ho' hoom'
        refine Or.inr (Or.inr (Or.inr ⟨by simpa [segc_stripS_status] using ho', ?_⟩))
        rw [hInv.onOom_eq (p, ret, g, st) s1 sf] at hoom'
        exact satisfies_of_stripExecOutside hfr_sf hoom'
    have hout0 : SubroutineOutcome (stringCloneNoOomSpec fineCostModel A cliBudgetLimits)
        (p, ret, g, st) R s0 sf := by
      change SubroutineOutcome (stringCloneNoOomSpec fineCostModel A cliBudgetLimits)
        (p, ret, g, st) R (s0.setPC (mpl.base 623)) sf at hout1
      cases s0; exact hout1
    obtain ⟨hfs, hfst⟩ :=
      specPreservesFsTrace_stringCloneNoOom A cliBudgetLimits (p, ret, g, st) R s0 sf hout0
    exact ⟨sf, huntil, huntil_kp, hsteps_strip, hstop_strip, hnhalt_strip,
      hstop_sf, hout0, hfs, hfst, hfr_sf⟩
  · exact False.elim hqp'
  · exact False.elim (not_satisfies_false_sepConj hmo')

end SegcHooksBundleHelpers

theorem g1fr_strClone_real_run_outcome
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64)
    (x : BitVec 64 × BitVec 64 × CryptoVerification.LibsignalSessionRepr.VecGhost ×
      (fineCostModel : LibsignalBinary.Heap.AllocCostModel).σ)
    (R : Arm64.SepProp) (s0 : Arm64.State)
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      Arm64.Satisfies (Arm64.SepProp.sepConj
        ((LibsignalBinary.Heap.RustStdAllocBudgetBridge.stringCloneNoOomSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits).pre x s0) R)
        s0.mem)
    (hFr : LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ExecFrozen s0.mem)
    (hlr : hole2_keep (s0.readReg64 .lr) = false)
    (hCodeStr1 : (hole2_str1Prog mpl).CodeLoaded (ProofLib.stripExecOutside hole2_keep s0.mem))
    (hCodeRx : LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg.CodeLoaded
      (ProofLib.stripExecOutside hole2_keep s0.mem)) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∃ sf : Arm64.State,
      Arm64.StepsUntil (hole2_strCloneProg mpl) (Arm64.SubroutineStop s0)
        (s0.setPC (mpl.base 623)) sf ∧
      Arm64.SubroutineStop s0 sf ∧
      Arm64.SubroutineOutcome
        (LibsignalBinary.Heap.RustStdAllocBudgetBridge.stringCloneNoOomSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)
        x R s0 sf ∧
      sf.fs = s0.fs ∧
      Arm64.FsTraced CryptoVerification.SignalSession.Cli.RunGlue.IsFsC s0 sf ∧
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ExecFrozen sf.mem := by
  obtain ⟨sf, huntil, _, _, _, _, hstop, hout, hfs, hfst, hfr_sf⟩ :=
    g1fr_strClone_real_steps_core mpl mmpl hLs hMm γ tp hRun hSp hPre hFr hlr hCodeStr1 hCodeRx
  exact ⟨sf, huntil, hstop, hout, hfs, hfst, hfr_sf⟩

/-- Strengthens `g1fr_strClone_real_run_outcome` with a `StepsUntil` visited-PC witness in
`hole2_keep` and a `stripS hole2_keep` trace. -/
theorem g1fr_strClone_real_run_outcome_stripS
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (γ : GhostName) (tp : BitVec 64)
    (x : BitVec 64 × BitVec 64 × CryptoVerification.LibsignalSessionRepr.VecGhost ×
      (fineCostModel : LibsignalBinary.Heap.AllocCostModel).σ)
    (R : Arm64.SepProp) (s0 : Arm64.State)
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      Arm64.Satisfies (Arm64.SepProp.sepConj
        ((LibsignalBinary.Heap.RustStdAllocBudgetBridge.stringCloneNoOomSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits).pre x s0) R)
        s0.mem)
    (hFr : LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ExecFrozen s0.mem)
    (hlr : hole2_keep (s0.readReg64 .lr) = false)
    (hCodeStr1 : (hole2_str1Prog mpl).CodeLoaded (ProofLib.stripExecOutside hole2_keep s0.mem))
    (hCodeRx : LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg.CodeLoaded
      (ProofLib.stripExecOutside hole2_keep s0.mem)) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∃ sf : Arm64.State,
      Arm64.StepsUntil (hole2_strCloneProg mpl) (Arm64.SubroutineStop s0)
        (s0.setPC (mpl.base 623)) sf ∧
      Arm64.StepsUntil (hole2_strCloneProg mpl)
        (fun st => Arm64.SubroutineStop s0 st ∨ hole2_keep st.pc = false)
        (s0.setPC (mpl.base 623)) sf ∧
      Arm64.Steps (hole2_strCloneProg mpl)
        (ProofLib.stripS hole2_keep (s0.setPC (mpl.base 623)))
        (ProofLib.stripS hole2_keep sf) ∧
      Arm64.SubroutineStop s0 (ProofLib.stripS hole2_keep sf) ∧
      (ProofLib.stripS hole2_keep sf).status ≠ .Halted ∧
      Arm64.SubroutineStop s0 sf ∧
      Arm64.SubroutineOutcome
        (LibsignalBinary.Heap.RustStdAllocBudgetBridge.stringCloneNoOomSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits)
        x R s0 sf ∧
      sf.fs = s0.fs ∧
      Arm64.FsTraced CryptoVerification.SignalSession.Cli.RunGlue.IsFsC s0 sf ∧
      LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ExecFrozen sf.mem :=
  g1fr_strClone_real_steps_core mpl mmpl hLs hMm γ tp hRun hSp hPre hFr hlr hCodeStr1 hCodeRx

/-- Constructs a real first-stop `<String as Clone>::clone` execution (`hole2_ActiveStrCloneRun`)
from `ActiveF3CallPre` for `stringCloneNoOomSpec`, `ExecFrozen`, `hole2_keep lr = false`,
and `CodeLoaded` on `stripExecOutside hole2_keep`. -/
theorem g1fr_activeStrCloneRun_of_activeF3CallPre
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (s0 : Arm64.State)
    (hPre :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks.ActiveF3CallPre
        (fun γ tp => LibsignalBinary.Heap.RustStdAllocBudgetBridge.stringCloneNoOomSpec fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) s0)
    (hFr : LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.ExecFrozen s0.mem)
    (hlr : hole2_keep (s0.readReg64 .lr) = false)
    (hCodeStr1 : (hole2_str1Prog mpl).CodeLoaded (ProofLib.stripExecOutside hole2_keep s0.mem))
    (hCodeRx : LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg.CodeLoaded
      (ProofLib.stripExecOutside hole2_keep s0.mem)) :
    hole2_ActiveStrCloneRun mpl s0 := by
  obtain ⟨hRun, hSp, γ, tp, x, R, hSat⟩ := hPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    g1fr_strClone_real_run_outcome mpl mmpl hLs hMm γ tp x R s0
      hRun hSp hSat hFr hlr hCodeStr1 hCodeRx
  exact ⟨hFr, hlr, hCodeStr1, hCodeRx, sf, huntil, hstop, hfs, hfst, hfr_sf⟩

theorem hole2_hHooksBundle
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        mmpl (hole2_ghFixed mpl mmpl) W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd) := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  intro W γ tp
  let P_sub := LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg
  have hPl : mallocngLib.Placeable mmpl := hole2_hPl_mng mmpl hMm
  have hKeep : ∀ a : BitVec 64,
      (mallocngLib.findCodeBlock mmpl a).isSome = true → hole2_keepSub a = true :=
    hole2_keepMallocng mmpl hMm
  have hReadSat : HookSat (cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W))
      lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits hole2_hookStack (ReadFileRuleEnvFixed cliIo.rd)) :=
    ⟨LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFine
      hole2_keepSub hole2_emptyProg P_sub (hole2_targets mpl).readFile mmpl
      cliElfImage.brkStart cliBudgetLimits hole2_hookStack,
     CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_readFile_some
      (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) rfl,
     LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.F3ReadFileGhostHook.f3ReadFileFixedGhostHookFine_ok_placed
      rfl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_svc
      (fun _ _ => rfl)
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie.f3TrialRxProg_no_ext
      hPl hKeep (Nat.le_refl _) (hole2_readFileCond_ok mmpl hMm) γ tp⟩
  have hStrSat : HookSat (cliGhostExterns (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W))
      CryptoVerification.SignalSession.lsStringCloneSym
      (LibsignalBinary.Heap.RustStdAllocBudgetBridge.stringCloneBudgetSpec fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits) :=
    ⟨hole2_strCloneGhostHook mpl mmpl,
     CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_stringClone_some
      (hole2_ghFixed mpl mmpl) (cliExternsPlaced mmpl W) rfl,
     segc_strCloneGhostHook_ok mpl mmpl hLs hMm γ tp⟩
  have hStrFsT : ∀ f, (hole2_ghFixed mpl mmpl).stringClone = some f →
      Arm64.HookFsTraced CryptoVerification.SignalSession.Cli.RunGlue.IsFsC f := by
    intro f hf
    change some (hole2_strCloneGhostHook mpl mmpl) = some f at hf
    cases hf
    exact segc_strCloneGhostHook_fsT mpl mmpl
  have hRunHooks :=
    LibsignalBinary.Proofs.PeakBudget.RealCliDecPkSlotOk.cliRunHooksPlaced_of_ghost
      mmpl (hole2_ghFixed mpl mmpl) W (hole2_hGSpqr mpl mmpl hLs hMm γ tp) hStrFsT hStrSat
  exact
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget.cliRunHooksBundle_of_hookSat_mono_stk
      mmpl (hole2_ghFixed mpl mmpl) W (by decide) (by decide) hRunHooks hReadSat

/-- Constructs `Nonempty (F3CliElfGhostWitness mpl mmpl)` on `cliElfBytes` under `CliElfHole2Assumption`. -/
theorem hole_gap1_f3GhostWitness
    (hA : CliElfHole2Assumption)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m) :
    Nonempty (F3CliElfGhostWitness mpl mmpl) :=
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  ⟨{ ghFixed := hole2_ghFixed mpl mmpl
     hookStack := hole2_hookStack
     hblk := hole2_hblk mpl hLs
     hext_nodup := hole2_hext_nodup mpl hLs
     hPl_mng := hole2_hPl_mng mmpl hMm
     hMainStk := hole2_hMainStk
     hTrFrozen := hole2_hTrFrozen hA mpl mmpl hLs hMm hF3Frozen
     hGSpqr := hole2_hGSpqr mpl mmpl hLs hMm
     hFs := hole2_hFs mpl mmpl hLs hMm
     hReadSat := hole2_hReadSat mpl mmpl hLs hMm
     hghNoAlloc := hole2_hghNoAlloc mpl mmpl hLs hMm
     hioOf := hole2_hioOf mpl mmpl hLs hMm
     hHooksBundle := hole2_hHooksBundle mpl mmpl hLs hMm }⟩

/-- Establishes `SpqrV1PlacedSeamsOfEnv` at the tight SPQR initial, recv, and send envelopes on `cliGhostExterns`. -/
theorem hole_m24slot_spqrSeams_tight
    {mpl mmpl : MultiPlacement}
    (_hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {brkStart : BitVec 64}
    (gh : CliGhostHooks) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits gh) :
    @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      mmpl gh W
      (InitialStateEnv W.C.F)
      (CliSpqrRecvTightLinkedEnv W)
      (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K) := by
  exact
    @LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst.hpt_spqrV1PlacedSeams_tightLinked
      (libsignalPlacementOf mpl hblk hext_nodup) γ mmpl tp brkStart cliBudgetLimits gh W
      hPl_mng hGSpqr

/-- Constructs a `LibsignalFullPlacement` witness from `LinkedAt cliElfBytes mpl` with underlying `libsignalPlacementOf mpl hblk hext_nodup`. -/
theorem hole_g1_fullPlacement_of_linkedAt
    {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) :
    ∃ fp : LibsignalFullPlacement,
      fp.toLibsignalPlacement = libsignalPlacementOf mpl hblk hext_nodup := by
  let ⟨_, _, hpl, _⟩ := hLs
  exact ⟨{ toLibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup, placeable := hpl }, rfl⟩

/-- Supplies block-518 `dpPollProgPlaced` `subroutine_ok` witnesses for `readFileSpecPlaced` and `sessDeserializeSpecPlaced`. -/
theorem hole_g2_poll_readFile_and_sessDeser_of_hooks
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {brkStart : BitVec 64}
    (ghFixed : CliGhostHooks)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)) ∧
    subroutine_ok (dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (mpl.base 46)
      (sessDeserializeSpecPlaced scopeKit
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        SessDeserializeCancelEnv) := by
  have _ := And.intro hLs hHooks
  let _ : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  exact
    ⟨LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced.hRead_of_hookSat
        (callerProg := dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        hsat,
     CryptoVerification.SignalSession.Cli.Store.PlacedCommon.ls_transfer_lscro
        (callerProg := dpPollProgPlaced (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.sessDeserialize_cli_dcan_placed_ok
          mmpl ghFixed W hG (fun _ hr => hr))⟩

theorem hole_g3_cliRunBudgets_eq_placed :
    cliRunBudgets = cliRunBudgets_placed := by
  rfl

/-- Reduces `DecPkD3UntypedEnvOf` over `ReadFileRuleEnvFixed cliIo.rd` to `DecPkD3UntypedEnv` on `CliPqOrD3RecvInputs`. -/
theorem hole_g4_decPkD3UntypedEnvOf_fixed_sub_plain
    [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks)
    (call : RunCall) (meV peerV : AddrV) (pm : PreKeySignalMessage)
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ call.i)
    (evs : List AllocEvent)
    (hevs : DecPkD3UntypedEnvOf (A := A) cliRunBudgets_placed
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv
      (r3bDecPkGhost call meV peerV pm) evs) :
    DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost call meV peerV pm) evs := by
  let g := r3bDecPkGhost call meV peerV pm
  have ⟨i₀, hi₀, hF⟩ : ∃ i₀, CryptoVerification.SignalSession.CliPqxdhInputs ⟨W.C, W.Q⟩ i₀ ∧
      g.F = CryptoVerification.SignalSession.Cli.RunCompose.runFiles i₀ := by
    rcases hi with hi_pq | ⟨st, ct, rc, hwf, hgi⟩
    · exact ⟨call.i, hi_pq, rfl⟩
    · refine ⟨CryptoVerification.SignalSession.pqRecvInputs ⟨W.C, W.Q⟩ st [] rc,
        LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3.cliPqxdhInputs_pqRecvInputs_nil
          hwf rc, ?_⟩
      show CryptoVerification.SignalSession.Cli.RunCompose.runFiles call.i = _
      rw [hgi]
      rfl
  let B := cliRunBudgets
  let RF := ReadFileRuleEnvFixed cliIo.rd
  let RP := LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd
  have hsess :
      LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.LoadStepEnv
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSessKitPlaced A g.F scopeKit
          g.peer (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
          A g.F g.peer B RF SessDeserializeCancelEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions g.peer.val =
      LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.LoadStepEnv
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSessKitPlaced A g.F scopeKit
          g.peer (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
          A g.F g.peer B RP SessDeserializeCancelEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions g.peer.val := by
    unfold LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.LoadStepEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitDefaultBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitLoadPollEnv
    dsimp only [RF, RP]
    rw [hF, LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.dirGetEnv_fixed_eq_of_not_overCap
      (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.not_overCapFile_runFiles_sessions hi₀ _)]
  have htrust :
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollIdKitPlaced A g.F g.peer
          (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv
          A g.F g.peer B RF)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity g.peer.val
        g.msg.identityKey .receiving =
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollIdKitPlaced A g.F g.peer
          (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv
          A g.F g.peer B RP)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity g.peer.val
        g.msg.identityKey .receiving := by
    unfold LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliIdStoreFullBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitDefaultBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitTrustPollEnv
    dsimp only [RF, RP]
    rw [hF, LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.dirGetEnv_fixed_eq_of_not_overCap
      (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.not_overCapFile_runFiles_identities hi₀ _)]
  have hspk : ∀ spkId,
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollSpkFullBudgetEnv
        A g.F spkId (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B) RF).getPollEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed spkId =
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollSpkFullBudgetEnv
        A g.F spkId (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B) RP).getPollEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed spkId := by
    intro spkId
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollSpkFullBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollSpkGetPollEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget.CliSpkGetPollEnv
    dsimp only [RF, RP]
    rw [hF, LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.dirGetEnv_fixed_eq_of_not_overCap
      (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.not_overCapFile_runFiles_signed hi₀ _)]
  have hkpk : ∀ kpkId spkId kbk,
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollKpkFullBudgetEnv
        A g.F kpkId spkId kbk (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B) RF).getPollEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber kpkId =
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollKpkFullBudgetEnv
        A g.F kpkId spkId kbk (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B) RP).getPollEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber kpkId := by
    intro kpkId spkId kbk
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollKpkFullBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollKpkGetPollEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.CliKpkGetPollEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
    dsimp only [RF, RP]
    rw [hF,
      LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.dirGetEnv_fixed_eq_of_not_overCap
        (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.not_overCapFile_runFiles_kyberOneTime hi₀ _),
      LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.dirGetEnv_fixed_eq_of_not_overCap
        (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.not_overCapFile_runFiles_kyberLastResort_keyName hi₀ kpkId)]
  have hpk : ∀ opkWord,
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollPkFullBudgetEnv
        A g.F opkWord (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B) RF).getPollEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime =
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollPkFullBudgetEnv
        A g.F opkWord (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B) RP).getPollEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime := by
    intro opkWord; funext id
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollPkFullBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux.cliPollPkGetPollEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget.CliPkGetPollEnv
    dsimp only [RF, RP]
    rw [hF, LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.dirGetEnv_fixed_eq_of_not_overCap
      (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.not_overCapFile_runFiles_oneTime hi₀ _)]
  have hselfKp :
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget.cliPollSelfBudgetEnv
        A g.F g.peer (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B) RF).kpPollEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity =
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget.cliPollSelfBudgetEnv
        A g.F g.peer (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B) RP).kpPollEnv
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget.cliPollSelfBudgetEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget.cliPollSelfKpPollEnv
    dsimp only [RF, RP]
    rw [hF, LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.dirGetEnv_fixed_eq_of_not_overCap
      (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.not_overCapFile_runFiles_own_ikp hi₀)]
  have hp2 : ∀ opt,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget.StageP2UntypedRejectEnv
        (A := A) B RF PqxdhAcceptBadKemErrEnv g opt =
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget.StageP2UntypedRejectEnv
        (A := A) B RP PqxdhAcceptBadKemErrEnv g opt := by
    intro opt; funext e
    unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget.StageP2UntypedRejectEnv
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget.StageP2BadKemRejectEnv
    dsimp only [RF, RP]
    rw [hspk, hkpk, hpk, hselfKp]
  have hp1u :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.CliDpPollUntrustedEnv
        (A := A) B RF SessDeserializeCancelEnv g =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.CliDpPollUntrustedEnv
        (A := A) B RP SessDeserializeCancelEnv g := by
    funext e
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.CliDpPollUntrustedEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget.StageP1UntrustedEnv
    dsimp only [RF, RP]
    rw [hsess, htrust]
  have hp1ok :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget.StageP1OkEnv
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSessKitPlaced A g.F scopeKit
          g.peer (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
          A g.F g.peer B RF SessDeserializeCancelEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollIdKitPlaced A g.F g.peer
          (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv
          A g.F g.peer B RF)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity g.peer.val
        g.msg.identityKey =
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget.StageP1OkEnv
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSessKitPlaced A g.F scopeKit
          g.peer (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
          A g.F g.peer B RP SessDeserializeCancelEnv)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollIdKitPlaced A g.F g.peer
          (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKitStk B))
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv
          A g.F g.peer B RP)
        CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity g.peer.val
        g.msg.identityKey := by
    funext e
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget.StageP1OkEnv
    dsimp only [RF, RP]
    rw [hsess, htrust]
  change DecPkD3UntypedEnvOf (A := A) B RF SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv g evs at hevs
  change DecPkD3UntypedEnvOf (A := A) B RP SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv g evs
  rcases hevs with hu | ⟨opt, hseq⟩
  · exact Or.inl (hp1u ▸ hu)
  · rw [hp1ok, hp2 opt] at hseq
    exact Or.inr ⟨opt, hseq⟩

section H8fG5Helpers

open Arm64.Process (bytesOfString)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (IdentityKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi
  (SessionRecord StoreCall fullTrace messageDecryptSignal_trace_prefix)
open CryptoVerification.E2E
  (PEParams partyAddressName pqxdhSpqrModel recvPrekeyState wirePrekey wireWhisper)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchetRepr (serviceIdParse)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs PqParty PqxdhPartyInSpecDomain baseKeysFile identityFile
   oneTimeKyberPreKeyFile oneTimePreKeyFile partyAddress pqRecvInputs sessionFile stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdGhost KyberGhost StoresGhost addressText baseKeysName keyName pathOf removePreKey
   utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (CallV DirWrOk StoreCallPeerPlaced StoresWrOk addrParse coinsOf inputOf keyName_length
   messageDecryptSignal_calls_peer_placed namedWrites namedWrites_ascii okPeerPath parseArgs
   saveUpd_own saveUpd_peers_path)
open CryptoVerification.SignalSession.Cli.RunCompose
  (RunSem SlotAns finish readBundleV runAns runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs
  (SessMatchesPm cliAnswers cliFinal cliStep decPkDef decPkDefD2c
   decPkDefD2c_eq_decPkDef_of_match decPkDefD2c_eq_decPkDef_of_noCurrent
   decPkDefD2c_eq_decPkDef_of_untrusted decPkDefD2c_namedWrites_sub decSigDef decSigKey
   encDef initDef initParty pkRecvCoins pkStoreKeys pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine
  (addrValE parseArgs_recv runAns_pqRecvBad runAns_pqRecvPrekey_eq runAns_pqRecvWhisper_eq)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn)
open LibsignalBinary.Heap (FitsEnv SeqEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf RunArmBinaryEnv preEnv_sub_r0BinaryEnv
   r3aRecvWEnv_sub_r3aBinaryEnv r3bRecvPEnv_sub_r3bEnv runEnv_to_cliRunBinaryEnv_of_slots)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed
  (mkD3BinaryKitCalleeEnvsWithDecPk realCliMainD3RecvWithDecPk_fitsEnv_cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
  (mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits pqRunAns_namedWrites_bounds
   stdin_le_msgCapBytes_of_pqInputs_and_inputOf stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (dirGetEnv_fixed_eq_of_not_overCap not_overCapFile_runFiles_own_address)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (cliPqxdhInputs_pqRecvInputs_nil d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive
   d3RecvW4ExtMaxReq d3RecvW4ExtPeak)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot (w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live w4RecvPrekeyReal1MiB_i_MaxReq
   w4RecvPrekeyReal1MiB_i_Peak)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
  (decPkD3UntypedCum decPkD3UntypedEnv_r3b_singleSlotFineSpec decPkD3UntypedGrpS
   decPkD3UntypedLive decPkD3UntypedMaxReq decPkD3UntypedPeak decPkD3Untyped_caps_le_1MiB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (defaultExtrasF3)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (domScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmAtMeEnv RunArmEnvs RunCoreEnv RunDispatchEnv RunInit2ChainEnv RunInit3Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

private theorem h8f_exists_cliPqxdhInputs_same_argv_runFiles
    {P : PEParams}
    {g : RunCall}
    (hi : CliPqOrD3RecvInputs P g.i) :
    ∃ g₀ : RunCall,
      CliPqxdhInputs P g₀.i ∧ g₀.c = g.c ∧
        g₀.i.argv = g.i.argv ∧
        runFiles g₀.i = runFiles g.i := by
  rcases hi with hi_pq | ⟨st, _ct, rc, hwf, hgi⟩
  · exact ⟨g, hi_pq, rfl, rfl, rfl⟩
  · exact ⟨{ g with i := pqRecvInputs P st [] rc },
      cliPqxdhInputs_pqRecvInputs_nil hwf rc,
      rfl, by rw [hgi]; rfl, by rw [hgi]; rfl⟩

private theorem h8f_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private def h8f_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem h8f_utf8_eq (s : String) : utf8 s = h8f_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, h8f_kutf8, List.utf8Encode, h8f_byteArray_toList_eq_data]

private theorem h8f_utf8_append (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  rw [h8f_utf8_eq, h8f_utf8_eq, h8f_utf8_eq]
  simp [h8f_kutf8, String.toList_append, List.flatMap_append]

private theorem h8f_toString_one : toString (1 : Nat) = "1" := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  exact String.toList_inj.mp (by rw [ht1, hd1, String.toList_singleton]; rfl)

private theorem h8f_sessionFile_partyAddress_eq (P : Party) :
    sessionFile (partyAddress P) = "sessions/" ++ partyAddressName P ++ "." ++ "1" := by
  simp only [sessionFile, partyAddress, CryptoVerification.SignalSession.Address.text,
    h8f_toString_one, String.append_assoc]

private theorem h8f_okPeerPath_id (P : Party) :
    okPeerPath P (pathOf (utf8 "identities") (addrValE P).name) := by
  have hpath : pathOf (utf8 "identities") (addrValE P).name =
      utf8 (identityFile (partyAddressName P)) := by
    have hne : utf8 "identities" ≠ [] := by rw [h8f_utf8_eq]; decide
    simp only [pathOf, hne, ↓reduceIte, addrValE, identityFile]
    rw [← h8f_utf8_append, ← h8f_utf8_append]
    rfl
  rw [hpath]
  refine ⟨?_, .inl ?_⟩
  · rw [h8f_utf8_eq]
    intro b hb
    have hall :
        (h8f_kutf8 (identityFile (partyAddressName P))).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [h8f_utf8_eq]
    cases P <;> decide

private theorem h8f_okPeerPath_sess (P : Party) :
    okPeerPath P (pathOf (utf8 "sessions") (addressText (addrValE P))) := by
  have hpath : pathOf (utf8 "sessions") (addressText (addrValE P)) =
      utf8 (sessionFile (partyAddress P)) := by
    have hne : utf8 "sessions" ≠ [] := by rw [h8f_utf8_eq]; decide
    have had : addressText (addrValE P) = utf8 (partyAddress P).text := by
      have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
      simp only [addressText, addrValE, CryptoVerification.SignalSession.Cli.decimalText, h1,
        CryptoVerification.SignalSession.Address.text, partyAddress]
      rw [← h8f_utf8_append, ← h8f_utf8_append]
    rw [had]
    simp only [pathOf, hne, ↓reduceIte, sessionFile]
    rw [← h8f_utf8_append, ← h8f_utf8_append]
    rfl
  rw [hpath]
  refine ⟨?_, .inr ?_⟩
  · rw [h8f_utf8_eq, h8f_sessionFile_partyAddress_eq]
    intro b hb
    have hall :
        (h8f_kutf8 ("sessions/" ++ partyAddressName P ++ "." ++ "1")).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [h8f_utf8_eq, h8f_sessionFile_partyAddress_eq]
    cases P <;> decide

private theorem h8f_list_length_le_flatMap_utf8EncodeChar :
    ∀ l : List Char, l.length ≤ (l.flatMap String.utf8EncodeChar).length
  | [] => Nat.le_refl 0
  | c :: cs => by
    have hc : 1 ≤ (String.utf8EncodeChar c).length := by
      unfold String.utf8EncodeChar; dsimp only
      by_cases h1 : c.val.toNat ≤ 127
      · simp only [h1, ↓reduceIte, List.length_cons, List.length_nil]; omega
      · by_cases h2 : c.val.toNat ≤ 2047
        · simp only [h1, h2, ↓reduceIte, List.length_cons, List.length_nil]; omega
        · by_cases h3 : c.val.toNat ≤ 65535
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
    have ih := h8f_list_length_le_flatMap_utf8EncodeChar cs
    simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega

private theorem h8f_string_length_le_utf8_length (s : String) : s.length ≤ (utf8 s).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  rw [String.length_ofList]
  have hutf : (utf8 (String.ofList l)).length = (l.flatMap String.utf8EncodeChar).length := by
    simp [utf8, List.utf8Encode, h8f_byteArray_toList_eq_data]
  rw [hutf]
  exact h8f_list_length_le_flatMap_utf8EncodeChar l

private theorem h8f_u32_toString_len_le_10 (id : BitVec 32) :
    (toString id.toNat).length ≤ 10 :=
  Nat.le_trans (h8f_string_length_le_utf8_length (toString id.toNat)) (keyName_length id)

private theorem h8f_identityFile_len_le_64 (P : Party) :
    (identityFile (partyAddressName P)).length ≤ 64 := by
  cases P <;> decide

private theorem h8f_sessionFile_len_le_64 (P : Party) :
    (sessionFile (partyAddress P)).length ≤ 64 := by
  rw [h8f_sessionFile_partyAddress_eq]
  cases P <;> decide

private theorem h8f_oneTimeKyberPreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimeKyberPreKeyFile id).length ≤ 64 := by
  have h := h8f_u32_toString_len_le_10 id
  unfold oneTimeKyberPreKeyFile; rw [String.length_append]
  have hp : ("one-time-kyber-pre-keys/").length = 24 := by decide
  omega

private theorem h8f_baseKeysFile_len_le_64 (id : BitVec 32) :
    (baseKeysFile id).length ≤ 64 := by
  have h := h8f_u32_toString_len_le_10 id
  unfold baseKeysFile; simp only [String.length_append]
  have hp1 : ("last-resort-kyber-pre-keys/").length = 27 := by decide
  have hp2 : (".base-keys").length = 10 := by decide
  omega

private theorem h8f_oneTimePreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimePreKeyFile id).length ≤ 64 := by
  have h := h8f_u32_toString_len_le_10 id
  unfold oneTimePreKeyFile; rw [String.length_append]
  have hp : ("one-time-pre-keys/").length = 18 := by decide
  omega

private theorem h8f_setOrPush_length_le_succ
    (xs : List (List (BitVec 8) × List (BitVec 8))) (k v : List (BitVec 8)) :
    (DirGhost.setOrPush k v xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [DirGhost.setOrPush]
  | cons _ _ ih =>
    unfold DirGhost.setOrPush
    split <;> [simp; (simp only [List.length_cons]; omega)]

private theorem h8f_dirPut_writes_length_le_succ (d : DirGhost) (k v : List (BitVec 8)) :
    (d.put k v).writes.length ≤ d.writes.length + 1 := by
  simp only [DirGhost.writes, DirGhost.put, List.length_map]
  exact h8f_setOrPush_length_le_succ d.changed k v

private theorem h8f_saveUpd_peers_writes_length_le_succ (F : FsFiles)
    (idG : IdGhost) (rem : AddrVal) (k : IdentityKey) :
    (idG.saveUpd cliIo.rd F rem k).peers.writes.length ≤ idG.peers.writes.length + 1 ∧
      (idG.saveUpd cliIo.rd F rem k).own = idG.own := by
  refine ⟨?_, saveUpd_own cliIo.rd F idG rem k⟩
  unfold IdGhost.saveUpd
  split
  · exact h8f_dirPut_writes_length_le_succ idG.peers rem.name k.serialize
  · exact Nat.le_succ _

private theorem h8f_foldl_cliStep_writes_length_le (F : FsFiles) :
    ∀ (calls : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (calls.foldl (cliStep F) g).writes.length ≤ g.writes.length + calls.length
  | [], g => by simp
  | c :: cs, g => by
    have h1 : (cliStep F g c).writes.length ≤ g.writes.length + 1 := by
      cases c with
      | loadSession _ | isTrustedIdentity _ _ _ => exact Nat.le_succ _
      | saveIdentity rem k =>
        obtain ⟨hp, ho⟩ := h8f_saveUpd_peers_writes_length_le_succ F g.identity rem k
        dsimp only [cliStep, StoresGhost.writes]; rw [ho]; simp only [List.length_append]; omega
      | storeSession rem r =>
        dsimp only [cliStep, StoresGhost.writes]
        have hs := h8f_dirPut_writes_length_le_succ g.sessions (addressText rem)
          (CryptoVerification.E2E.Record.encodeRecord r)
        simp only [List.length_append]; omega
    have h2 := h8f_foldl_cliStep_writes_length_le F cs (cliStep F g c)
    dsimp only [List.foldl, List.length_cons]; omega

private theorem h8f_storesWrOk_foldl (F : FsFiles) (P : Party) :
    ∀ (cs : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (∀ c ∈ cs, StoreCallPeerPlaced (addrValE P) c) →
      StoresWrOk (okPeerPath P) g →
      g.identity.peers.path = utf8 "identities" →
      g.sessions.path = utf8 "sessions" →
      StoresWrOk (okPeerPath P) (cs.foldl (cliStep F) g) := by
  intro cs
  induction cs with
  | nil => intro g _ hg0 _ _; exact hg0
  | cons c cs' ih =>
    intro g hcs hg0 hp hs
    have hc1 := hcs c List.mem_cons_self
    cases c with
    | loadSession _ | isTrustedIdentity _ _ _ =>
      exact ih g (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hg0 hp hs
    | saveIdentity rem k =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with
          own := by rw [saveUpd_own]; exact hg0.own
          peers := DirWrOk.saveUpd hg0.peers (hp ▸ h8f_okPeerPath_id P) }
        (by rw [saveUpd_peers_path, hp]) hs
    | storeSession rem r0 =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with sessions := hg0.sessions.put (hs ▸ h8f_okPeerPath_sess P) _ } hp hs

private theorem h8f_decPkDef_writes_len_le_4 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F (addrValE P) me pm coins = some (some (g', pt))) :
    g'.writes.length ≤ 4 := by
  unfold decPkDef at h
  dsimp only at h
  cases hload : loadRec Scope F (addrValE P) with
  | error _ => rw [hload] at h; cases h
  | ok r =>
    rw [hload] at h; dsimp only at h
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F (addrValE P) pm.identityKey with
    | error _ => rw [htr] at h; cases h
    | ok tb =>
      cases tb with
      | false => rw [htr] at h; cases h
      | true =>
        rw [htr] at h; dsimp only at h
        cases hcur : r.bind (·.currentSession) with
        | some s =>
          rw [hcur] at h; dsimp only at h
          split at h
          · split at h
            · cases h
            · cases hdec : SessionState.tryDecryptFromRecord W.C
                  (CryptoVerification.E2E.pqxdhSpqrSession W)
                  ((CryptoVerification.E2E.pqxdhSessionParams W).expectedAddrs
                    (initParty (addrValE P)))
                  pm.message .preKey (pkRecvCoins coins) s.state with
              | mk res st1 =>
                rw [hdec] at h
                cases res with
                | ok _ =>
                  dsimp only at h
                  injection h with h1; injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  obtain ⟨hp, ho⟩ := h8f_saveUpd_peers_writes_length_le_succ F
                    StoresGhost.opened.identity (addrValE P) pm.identityKey
                  have hs := h8f_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                    (addressText (addrValE P))
                    (CryptoVerification.E2E.Record.encodeRecord
                      { currentSession := some
                          { state := st1, pendingPreKey := none, pendingKyberPreKey := none,
                            localRegistrationId := s.localRegistrationId,
                            remoteRegistrationId := s.remoteRegistrationId,
                            aliceBaseKey := s.aliceBaseKey } })
                  have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                  have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                  have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                  have h0_kot : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                  have h0_klr : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                  have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                  have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                  have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                  dsimp only [StoresGhost.writes]; rw [ho]
                  simp only [List.length_append, h0_own, h0_signed, h0_kot, h0_klr, h0_ot, h0_pub]
                  omega
                | error err => cases err <;> cases h
          · cases h
        | none =>
          rw [hcur] at h; dsimp only at h
          cases hpk : pkToE? pm with
          | none => rw [hpk] at h; cases h
          | some m =>
            rw [hpk] at h; dsimp only at h
            cases hsk : pkStoreKeys F m with
            | none => rw [hsk] at h; cases h
            | some k =>
              rw [hsk] at h
              cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd F with
              | error _ => rw [hkp] at h; cases h
              | ok kp =>
                rw [hkp] at h
                cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
                | error _ => rw [hreg] at h; cases h
                | ok reg =>
                  rw [hreg] at h; dsimp only at h
                  cases hrecv : recvPrekeyState X W
                      (initParty (addrValE P)) ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
                  | none => rw [hrecv] at h; cases h
                  | some o =>
                    rw [hrecv] at h
                    cases o with
                    | none => cases h
                    | some triple =>
                      rcases triple with ⟨x, gs, _⟩
                      dsimp only at h
                      cases hkm : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId
                          pm.signedPreKeyId pm.baseKey with
                      | mk kres kyber' =>
                        rw [hkm] at h
                        cases kres with
                        | error _ => cases h
                        | ok u =>
                          cases u; dsimp only at h
                          injection h with h1; injection h1 with h2
                          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                          have hkyb : kyber'.oneTime.writes.length + kyber'.lastResort.writes.length ≤ 1 := by
                            unfold KyberGhost.mark at hkm
                            cases hot : StoresGhost.opened.kyber.oneTime.get cliIo.rd F
                                (keyName m.kpkId) with
                            | error _ => rw [hot] at hkm; cases hkm
                            | ok bs =>
                              rw [hot] at hkm
                              cases bs with
                              | cons _ _ =>
                                dsimp only at hkm; injection hkm with _ hk; subst hk; dsimp only
                                have h1 := h8f_dirPut_writes_length_le_succ
                                  StoresGhost.opened.kyber.oneTime (keyName m.kpkId) []
                                have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                                have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                                omega
                              | nil =>
                                dsimp only at hkm
                                cases hlr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F
                                    (baseKeysName m.kpkId) with
                                | error _ => rw [hlr] at hkm; cases hkm
                                | ok seen =>
                                  rw [hlr] at hkm; dsimp only at hkm
                                  split at hkm
                                  · cases hkm
                                  · split at hkm
                                    · cases hkm
                                    · injection hkm with _ hk; subst hk; dsimp only
                                      have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                                      have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                                      rw [h0a, Nat.zero_add]
                                      exact Nat.le_trans (h8f_dirPut_writes_length_le_succ _ _ _)
                                        (by rw [h0b])
                          obtain ⟨hp_le, ho⟩ := h8f_saveUpd_peers_writes_length_le_succ F
                            StoresGhost.opened.identity (addrValE P) pm.identityKey
                          have hs_le := h8f_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                            (addressText (addrValE P))
                            (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)
                          have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                          have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                          have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                          have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                          have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                          unfold StoresGhost.writes; dsimp only; rw [ho]
                          simp only [List.length_append, h0_own, h0_signed, h0_pub]
                          cases pm.preKeyId with
                          | none =>
                            dsimp only
                            have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                            omega
                          | some j =>
                            dsimp only; unfold removePreKey
                            cases StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
                            | error _ =>
                              dsimp only
                              have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                              omega
                            | ok bs =>
                              cases bs with
                              | nil =>
                                dsimp only
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega
                              | cons _ _ =>
                                dsimp only
                                have hot_put := h8f_dirPut_writes_length_le_succ
                                  StoresGhost.opened.oneTime (keyName j) []
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega

private theorem h8f_decPkDef_some_some_eq_d2c {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F peer me pm coins = some (some (g', pt))) :
    decPkDefD2c X W Scope F peer me pm coins = some (some (g', pt)) := by
  by_cases htr : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true
  · cases hload : loadRec Scope F peer with
    | error _ =>
      unfold decPkDef at h; simp [hload] at h
    | ok opt =>
      cases opt with
      | none =>
        rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F peer me pm coins
          (fun _ hl => by rw [hload] at hl; cases hl)]
        exact h
      | some r =>
        cases hcur : r.currentSession with
        | none =>
          rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F peer me pm coins
            (fun _ hl => by
              rw [hload] at hl; injection hl with hr; injection hr with hr; subst hr; exact hcur)]
          exact h
        | some s =>
          by_cases hm : SessMatchesPm s pm
          · rw [decPkDefD2c_eq_decPkDef_of_match X W Scope F peer me pm coins hload hcur hm]
            exact h
          · unfold decPkDef at h
            simp [hload, htr, hcur, hm] at h
  · rw [decPkDefD2c_eq_decPkDef_of_untrusted X W Scope F peer me pm coins htr]
    exact h

private theorem h8f_finish_inv {α : Type} {ans : SlotAns α}
    {outFn : α → List (BitVec 8)} {ws : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : finish ans outFn = some (some (ws, out))) :
    ∃ g' v, ans = some (some (g', v)) ∧ ws = namedWrites g'.writes ∧ out = outFn v := by
  cases ans with
  | none => cases h
  | some o =>
    cases o with
    | none => cases h
    | some gv =>
      rcases gv with ⟨g', v⟩
      dsimp only [finish] at h
      injection h with h1; injection h1 with h2
      obtain ⟨hw, ho⟩ := Prod.mk.inj h2
      exact ⟨g', v, rfl, hw.symm, ho.symm⟩

private theorem h8f_runAns_some_some_to_d2c
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {S : RunSem}
    (hinit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (henc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecSig : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hpksm : S.pksmParse = pksmParse)
    {i : Inputs} {nw : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (ha : runAns S i = some (some (nw, out))) :
    runAns (cliRunSemD2c_placed X W) i = some (some (nw, out)) := by
  unfold runAns at ha ⊢
  cases hp : parseArgs uuidTryParse (i.argv.map bytesOfString) with
  | none => rw [hp] at ha; cases ha
  | some c =>
    rw [hp] at ha; dsimp only at ha ⊢
    cases hown : StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") with
    | error _ => rw [hown] at ha; cases ha
    | ok ownB =>
      rw [hown] at ha; dsimp only at ha ⊢
      cases had : addrParse uuidTryParse ownB with
      | none => rw [had] at ha; cases ha
      | some meV =>
        rw [had] at ha; dsimp only at ha ⊢
        cases c with
        | keygen _ _ => cases ha
        | init peerV dir =>
          dsimp only at ha ⊢
          cases hbv : readBundleV (runFiles i) dir peerV.device with
          | none => rw [hbv] at ha; cases ha
          | some b =>
            rw [hbv] at ha; dsimp only at ha ⊢
            have hd2c_in : (cliRunSemD2c_placed X W).initiate = initDef X ⟨W.C, W.Q⟩ := rfl
            rw [hinit] at ha; rw [hd2c_in]; exact ha
        | send peerV =>
          dsimp only at ha ⊢
          rw [henc] at ha; exact ha
        | recv peerV =>
          dsimp only at ha ⊢
          cases hst : i.stdin with
          | nil => rw [hst] at ha; cases ha
          | cons t rest =>
            rw [hst] at ha; dsimp only at ha ⊢
            by_cases ht2 : t = 2#8
            · simp only [ht2, ↓reduceIte] at ha ⊢
              rw [hdecSig] at ha; exact ha
            · simp only [ht2, ↓reduceIte] at ha ⊢
              by_cases ht3 : t = 3#8
              · simp only [ht3, ↓reduceIte] at ha ⊢
                have hd2c_pk : (cliRunSemD2c_placed X W).pksmParse = pksmParse := rfl
                have hd2c_dp : (cliRunSemD2c_placed X W).decryptPrekey =
                    decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn := rfl
                rw [hpksm] at ha; rw [hd2c_pk, hd2c_dp]
                cases hpm : pksmParse rest with
                | none => rw [hpm] at ha; cases ha
                | some pm =>
                  rw [hpm] at ha; dsimp only at ha ⊢
                  rw [hdecPk] at ha
                  obtain ⟨g', v, hg, hnw, hout⟩ := h8f_finish_inv ha
                  rw [h8f_decPkDef_some_some_eq_d2c hg]
                  simp [finish, hnw, hout]
              · simp only [ht3, ↓reduceIte] at ha; cases ha

private theorem h8f_decSigDef_writes_bounds {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    g'.writes.length ≤ 4 := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    obtain ⟨k, r, -, hpref⟩ :=
      messageDecryptSignal_trace_prefix W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
        msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hpref
    have hclen : calls.length ≤ 4 := Nat.le_trans hpref.length_le (by simp [fullTrace])
    have hf := h8f_foldl_cliStep_writes_length_le F calls StoresGhost.opened
    have h0 : StoresGhost.opened.writes.length = 0 := rfl
    dsimp only [cliFinal]; omega
  · cases h
  · cases h

private theorem h8f_storesWrOk_decSigDef {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    have hc := messageDecryptSignal_calls_peer_placed
      W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
      msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hc
    exact h8f_storesWrOk_foldl F P calls StoresGhost.opened hc (StoresWrOk.opened _) rfl rfl
  · cases h
  · cases h

theorem h8f_nwDom_pqD3Recv
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {S : RunSem}
    (hinit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (henc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecSig : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hpksm : S.pksmParse = pksmParse)
    (i : Inputs)
    (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i)
    (ha : runAns S i = some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 := by
  have ha_d2c := h8f_runAns_some_some_to_d2c hinit henc hdecSig hdecPk hpksm ha
  rcases hi with hi_pq | ⟨st, ct, rc, _hwf, rfl⟩
  · exact pqRunAns_namedWrites_bounds hi_pq ha_d2c
  · cases ct with
    | nil =>
      rw [runAns_pqRecvBad S ⟨W.C, W.Q⟩ st [] rc (by decide) (by decide)] at ha; cases ha
    | cons t rest =>
      by_cases ht2 : t = wireWhisper
      · subst ht2
        rw [runAns_pqRecvWhisper_eq S ⟨W.C, W.Q⟩ st rest rc, hdecSig] at ha
        cases hsm : SignalMessage.tryFrom protoSignalCodec rest with
        | error _ => rw [hsm] at ha; cases ha
        | ok msg =>
          rw [hsm] at ha; dsimp only at ha
          obtain ⟨g', v, hg, rfl, _⟩ := h8f_finish_inv ha
          have hlen4 : g'.writes.length ≤ 4 := h8f_decSigDef_writes_bounds hg
          have hwr : StoresWrOk (okPeerPath st.party.other) g' := h8f_storesWrOk_decSigDef hg
          refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
          have hasc : ∀ w ∈ g'.writes, ∀ b ∈ w.1, b.toNat < 128 :=
            fun w hw => (hwr.writes w hw).1
          rw [namedWrites_ascii g'.writes hasc] at hq
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
          rcases (hwr.writes w hw).2 with hp | hp <;> rw [hp]
          · exact h8f_identityFile_len_le_64 st.party.other
          · exact h8f_sessionFile_len_le_64 st.party.other
      · by_cases ht3 : t = wirePrekey
        · subst ht3
          rw [runAns_pqRecvPrekey_eq S ⟨W.C, W.Q⟩ st rest rc, hpksm, hdecPk] at ha
          cases hpm : pksmParse rest with
          | none => rw [hpm] at ha; cases ha
          | some pm =>
            rw [hpm] at ha; dsimp only at ha
            obtain ⟨g', v, hg, rfl, _⟩ := h8f_finish_inv ha
            have hg_d2c := h8f_decPkDef_some_some_eq_d2c hg
            obtain ⟨kpkId, opkId, hsub⟩ := decPkDefD2c_namedWrites_sub hg_d2c
            have hlen4 := h8f_decPkDef_writes_len_le_4 hg
            refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
            rcases hsub q hq with h | h | h | h | h <;> rw [h]
            · exact h8f_identityFile_len_le_64 st.party.other
            · exact h8f_sessionFile_len_le_64 st.party.other
            · exact h8f_oneTimeKyberPreKeyFile_len_le_64 kpkId
            · exact h8f_baseKeysFile_len_le_64 kpkId
            · exact h8f_oneTimePreKeyFile_len_le_64 opkId
        · rw [runAns_pqRecvBad S ⟨W.C, W.Q⟩ st (t :: rest) rc
            (fun h => ht2 (Option.some.inj h)) (fun h => ht3 (Option.some.inj h))] at ha
          cases ha

private theorem h8f_parseArgs_pqRecvInputs_is_recv {P : PEParams} {st : PqParty}
    {ct : List (BitVec 8)} {rc : BitVec 256} {c : CallV}
    (hp : parseArgs uuidTryParse ((pqRecvInputs P st ct rc).argv.map bytesOfString) = some c) :
    ∃ peerV : AddrV, c = .recv peerV := by
  have ha : (pqRecvInputs P st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  rw [ha, parseArgs_recv] at hp
  injection hp with hc
  exact ⟨_, hc.symm⟩

/-- Every `CliPqOrD3RecvInputs` call within `stdinCapBytes` outside prekey `recv` (`3#8 :: _`) belongs to `CliPqxdhInputs`. -/
theorem h8f_cliPqxdhInputs_of_pqOrD3Recv_nonPrekey
    {WP : PEParams} {i : Inputs} {c : CallV}
    (hi : CliPqOrD3RecvInputs WP i)
    (hp : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hin : (inputOf i c).length ≤ stdinCapBytes)
    (hnp : ∀ (peerV : AddrV) (rest : List (BitVec 8)),
      c = .recv peerV → i.stdin ≠ 3#8 :: rest) :
    CliPqxdhInputs WP i := by
  rcases hi with hi_pq | ⟨st, ct, rc, hst, rfl⟩
  · exact hi_pq
  · obtain ⟨peerV, rfl⟩ := h8f_parseArgs_pqRecvInputs_is_recv hp
    have hct_le : (pqRecvInputs WP st ct rc).stdin.length ≤ msgCapBytes :=
      stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf hp hin
    have hct_lt : ct.length < 2 ^ 32 :=
      Nat.lt_of_le_of_lt hct_le (by decide : msgCapBytes < 2 ^ 32)
    cases ct with
    | nil =>
      exact ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨[], rc, by decide, by decide, by decide, rfl⟩)))⟩
    | cons b rest =>
      by_cases hb2 : b = wireWhisper
      · subst hb2
        exact ⟨st, hst, Or.inr (Or.inr (Or.inl
          ⟨rest, rc, Nat.lt_of_succ_lt hct_lt, rfl⟩))⟩
      · have hb3 : b ≠ wirePrekey := fun h =>
          hnp peerV rest rfl (by rw [h]; rfl)
        exact ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr
          ⟨b :: rest, rc, hct_lt,
            fun h => hb2 (Option.some.inj h),
            fun h => hb3 (Option.some.inj h), rfl⟩)))⟩

def h8f_untypedDecPkCallEnv [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (g : RunCall) (evs : List AllocEvent) : Prop :=
  match g.c, g.i.stdin with
  | .recv peerV, b :: rest =>
    if b = 3#8 then
      match pksmParse rest with
      | some pm => ∃ meV : AddrV, DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost g meV peerV pm) evs
      | none => False
    else False
  | _, _ => False

def h8f_falseSlotSpec {P : List AllocEvent → Prop}
    (hfalse : ∀ evs, P evs → False) :
    { S : SingleSlotFineSpec P //
      S.cum ≤ d3RecvW4ExtCum ∧ S.live ≤ d3RecvW4ExtLive ∧
      S.peak ≤ d3RecvW4ExtPeak ∧ S.maxReq ≤ d3RecvW4ExtMaxReq ∧
      S.grpS ≤ d3RecvW4ExtGrpS } :=
  ⟨{ cum := 0
     live := 0
     peak := 0
     maxReq := 0
     grpS := 0
     credit :=
       { req_align := fun evs hP => False.elim (hfalse evs hP)
         credit_le := fun _ {evs} hP => False.elim (hfalse evs hP) }
     live_le_peak := Nat.le_refl 0
     groups := { groups_le := fun _ {evs} hP => False.elim (hfalse evs hP) } },
   ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩⟩

theorem h8f_untypedDecPkCallEnv_caps_le :
    decPkD3UntypedCum ≤ d3RecvW4ExtCum ∧
    decPkD3UntypedLive ≤ d3RecvW4ExtLive ∧
    decPkD3UntypedPeak ≤ d3RecvW4ExtPeak ∧
    decPkD3UntypedMaxReq ≤ d3RecvW4ExtMaxReq ∧
    decPkD3UntypedGrpS ≤ d3RecvW4ExtGrpS := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := decPkD3Untyped_caps_le_1MiB
  exact
    ⟨Nat.le_trans h1 (by decide : w4RecvPrekeyReal1MiB_i_Cum ≤ d3RecvW4ExtCum),
     Nat.le_trans h2 (by decide : w4RecvPrekeyReal1MiB_i_Live ≤ d3RecvW4ExtLive),
     Nat.le_trans h3 (by decide : w4RecvPrekeyReal1MiB_i_Peak ≤ d3RecvW4ExtPeak),
     Nat.le_trans h4 (by decide : w4RecvPrekeyReal1MiB_i_MaxReq ≤ d3RecvW4ExtMaxReq),
     Nat.le_trans h5 (by decide : w4RecvPrekeyRealGrpS ≤ d3RecvW4ExtGrpS)⟩

def h8f_untypedDecPkCallEnv_slotSpecWithCaps [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (g : RunCall)
    (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (_hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    { S : SingleSlotFineSpec (h8f_untypedDecPkCallEnv A W g) //
      S.cum ≤ d3RecvW4ExtCum ∧ S.live ≤ d3RecvW4ExtLive ∧
      S.peak ≤ d3RecvW4ExtPeak ∧ S.maxReq ≤ d3RecvW4ExtMaxReq ∧
      S.grpS ≤ d3RecvW4ExtGrpS } := by
  cases hc : g.c with
  | keygen _ _ =>
    exact h8f_falseSlotSpec (by intro evs hP; unfold h8f_untypedDecPkCallEnv at hP; simp [hc] at hP)
  | init _ _ =>
    exact h8f_falseSlotSpec (by intro evs hP; unfold h8f_untypedDecPkCallEnv at hP; simp [hc] at hP)
  | send _ =>
    exact h8f_falseSlotSpec (by intro evs hP; unfold h8f_untypedDecPkCallEnv at hP; simp [hc] at hP)
  | recv peerV =>
    cases hst : g.i.stdin with
    | nil =>
      exact h8f_falseSlotSpec (by
        intro evs hP; unfold h8f_untypedDecPkCallEnv at hP; simp [hc, hst] at hP)
    | cons b rest =>
      by_cases hb : b = 3#8
      · cases hpk : pksmParse rest with
        | none =>
          exact h8f_falseSlotSpec (by
            intro evs hP; unfold h8f_untypedDecPkCallEnv at hP; simp [hc, hst, hb, hpk] at hP)
        | some pm =>
          have hparse_recv :
              parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hc ▸ hparse
          refine ⟨{ cum := decPkD3UntypedCum
                    live := decPkD3UntypedLive
                    peak := decPkD3UntypedPeak
                    maxReq := decPkD3UntypedMaxReq
                    grpS := decPkD3UntypedGrpS
                    credit :=
                      { req_align := fun evs hP ev hev => by
                          have hex : ∃ meV : AddrV,
                              DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost g meV peerV pm) evs := by
                            unfold h8f_untypedDecPkCallEnv at hP
                            simpa [hc, hst, hb, hpk] using hP
                          obtain ⟨meV, hmeV⟩ := hex
                          exact
                            (decPkD3UntypedEnv_r3b_singleSlotFineSpec A W cliRunBudgets g meV peerV pm
                              hi_g hparse_recv).credit.req_align evs hmeV ev hev
                        credit_le := fun st0 {evs} hP => by
                          have hex : ∃ meV : AddrV,
                              DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost g meV peerV pm) evs := by
                            unfold h8f_untypedDecPkCallEnv at hP
                            simpa [hc, hst, hb, hpk] using hP
                          obtain ⟨meV, hmeV⟩ := hex
                          exact
                            (decPkD3UntypedEnv_r3b_singleSlotFineSpec A W cliRunBudgets g meV peerV pm
                              hi_g hparse_recv).credit.credit_le st0 hmeV }
                    live_le_peak :=
                      (decPkD3UntypedEnv_r3b_singleSlotFineSpec A W cliRunBudgets g peerV peerV pm
                        hi_g hparse_recv).live_le_peak
                    groups :=
                      { groups_le := fun st0 {evs} hP => by
                          have hex : ∃ meV : AddrV,
                              DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost g meV peerV pm) evs := by
                            unfold h8f_untypedDecPkCallEnv at hP
                            simpa [hc, hst, hb, hpk] using hP
                          obtain ⟨meV, hmeV⟩ := hex
                          exact
                            (decPkD3UntypedEnv_r3b_singleSlotFineSpec A W cliRunBudgets g meV peerV pm
                              hi_g hparse_recv).groups.groups_le st0 hmeV } },
                  h8f_untypedDecPkCallEnv_caps_le⟩
      · exact h8f_falseSlotSpec (by
          intro evs hP; unfold h8f_untypedDecPkCallEnv at hP; simp [hc, hst, hb] at hP)

/-- Prekey `recv` (`3#8 :: _`) sub-domain of `CliPqOrD3RecvInputs`. -/
def h8f_DomPrekey (WP : PEParams) (i : Inputs) : Prop :=
  CliPqOrD3RecvInputs WP i ∧
    ∃ (peerV : AddrV) (rest : List (BitVec 8)),
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV) ∧
      i.stdin = 3#8 :: rest

/-- `MainEntryBudgetFitsCapOf` for prekey `recv` (`3#8 :: _`) calls in `CliPqOrD3RecvInputs`, depending only on `sEnvs.decryptPrekey`. -/
theorem h8f_d3Prekey_fitsCap [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel)
    (sEnvs : RunSlotEnvs)
    (hs_dp : sEnvs.decryptPrekey =
      DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
        (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
        PqxdhAcceptBadKemErrEnv := by rfl) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv (cliRunSemD3 W)))
      (domScopedRun (h8f_DomPrekey ⟨W.C, W.Q⟩) (runRel (cliRunSemD3 W))) := by
  let S := cliRunSemD3 W
  let X := defaultExtrasF3
  let decPkEnv := h8f_untypedDecPkCallEnv A.repAlloc W
  let E := mkD3BinaryKitCalleeEnvsWithDecPk (default : Image) S X W decPkEnv
  have hMain := realCliMainD3RecvWithDecPk_fitsEnv_cliBudgetLimits (default : Image) S X W decPkEnv
    (fun g hi hs hp => (h8f_untypedDecPkCallEnv_slotSpecWithCaps A.repAlloc W g hi hs hp).1)
    (fun g hi hs hp => (h8f_untypedDecPkCallEnv_slotSpecWithCaps A.repAlloc W g hi hs hp).2)
  exact mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
    boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
    (fun i ⟨hi, _⟩ => hMain i hi)
    (fun i c ⟨hi, _⟩ hp hin => by
      rcases hi with hi_pq | ⟨st, ct, rc, _, rfl⟩
      · exact stdin_le_msgCapBytes_of_pqInputs_and_inputOf hi_pq hp hin
      · exact stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf hp hin)
    (fun i nw out ⟨hi, _⟩ ha => h8f_nwDom_pqD3Recv rfl rfl rfl rfl rfl i nw out hi ha)
    (fun g ⟨hi, peerV₀, rest₀, hp₀, hst₀⟩ hparse _hin _hrel evs hrun => by
      have hc₀ : g.c = .recv peerV₀ := Option.some.inj (hparse.symm.trans hp₀)
      obtain ⟨g₀, hi₀, _, _, hfiles₀⟩ := h8f_exists_cliPqxdhInputs_same_argv_runFiles hi
      have hpeq : PreEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g =
          PreEnv (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g := by
        funext e
        unfold PreEnv cliRunCalleesEnvs
        dsimp only
        rw [← hfiles₀, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_address hi₀)]
      exact runEnv_to_cliRunBinaryEnv_of_slots (E := E g)
        (fun _ hp =>
          preEnv_sub_r0BinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) rfl g
            (Eq.mp (congrFun hpeq _) hp))
        (fun _ _ _ _ hc => by rw [hc₀] at hc; cases hc)
        (fun _ _ _ _ hc => by rw [hc₀] at hc; cases hc)
        (fun _ _ _ _ hc => by rw [hc₀] at hc; cases hc)
        (fun _ _ _ hc => by rw [hc₀] at hc; cases hc)
        (fun _ _ _ _ _ hst _ => by rw [hst₀] at hst; cases hst)
        (fun _ peerV rest _ hc hst hrp =>
          r3bRecvPEnv_sub_r3bEnv
            (fun _ hpk => hpk)
            (fun meV _meG pm e _hme hp hd => by
              have hp' : pksmParse rest = some pm := hp
              rw [hs_dp] at hd
              have hd' : DecPkD3UntypedEnv A.repAlloc W cliRunBudgets
                  (r3bDecPkGhost g meV peerV pm) e :=
                hole_g4_decPkD3UntypedEnvOf_fixed_sub_plain A.repAlloc W g meV peerV pm hi e hd
              dsimp only [E, mkD3BinaryKitCalleeEnvsWithDecPk, decPkEnv, h8f_untypedDecPkCallEnv]
              simp only [hc, hst, ↓reduceIte, hp']
              exact ⟨meV, hd'⟩)
            hrp)
        evs hrun)

/-- Outside prekey `recv` (`3#8 :: _`), `RunEnv aEnvs g` is independent of `pksmTryFrom` and `recvP`. -/
theorem h8f_runEnv_armEnvs_nonPrekey_eq
    {aEnvs₁ aEnvs₂ : RunArmEnvs} {g : RunCall}
    (hpre : aEnvs₁.pre = aEnvs₂.pre)
    (hinit1 : aEnvs₁.init1 = aEnvs₂.init1)
    (hinit2 : aEnvs₁.init2 = aEnvs₂.init2)
    (hinit3 : aEnvs₁.init3 = aEnvs₂.init3)
    (hsend : aEnvs₁.send = aEnvs₂.send)
    (hrecvW : aEnvs₁.recvW = aEnvs₂.recvW)
    (hnp : ∀ (peerV : AddrV) (rest : List (BitVec 8)),
      g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) :
    RunEnv aEnvs₁ g = RunEnv aEnvs₂ g := by
  have hi3 : ∀ meV peerV dir,
      RunInit3Env aEnvs₁ g meV peerV dir = RunInit3Env aEnvs₂ g meV peerV dir := by
    intro meV peerV dir; funext evs; unfold RunInit3Env; rw [hinit3]
  have hi2 : ∀ meV peerV dir,
      RunInit2ChainEnv aEnvs₁ g meV peerV dir = RunInit2ChainEnv aEnvs₂ g meV peerV dir := by
    intro meV peerV dir; funext evs; unfold RunInit2ChainEnv; rw [hinit2, hi3]
  have harm : ∀ me, RunArmAtMeEnv aEnvs₁ g me = RunArmAtMeEnv aEnvs₂ g me := by
    intro me; funext evs; unfold RunArmAtMeEnv
    cases hc : g.c with
    | keygen _ _ => rfl
    | send peerV => rw [hsend]
    | init peerV dir => cases me <;> simp only [hinit1, hi2]
    | recv peerV =>
      cases hst : g.i.stdin with
      | nil => rfl
      | cons t rest =>
        by_cases ht2 : t = 2#8
        · simp only [ht2, ↓reduceIte, hrecvW]
        · by_cases ht3 : t = 3#8
          · exfalso; exact hnp peerV rest hc (ht3 ▸ hst)
          · simp only [ht2, ht3, ↓reduceIte]
  have hdisp : RunDispatchEnv aEnvs₁ g = RunDispatchEnv aEnvs₂ g := by
    funext evs; unfold RunDispatchEnv; simp only [harm]
  have hcore : RunCoreEnv aEnvs₁ g = RunCoreEnv aEnvs₂ g := by
    funext evs; unfold RunCoreEnv; rw [hpre, hdisp]
  funext evs; unfold RunEnv; rw [hcore]

/-- Reduces `MainEntryBudgetFitsCapOf` on `pqD3ScopedRun` for `DecPkD3UntypedEnvOf` slots to whole-`main` `FitsEnv` and non-prekey `RunEnv` inclusion on `CliPqxdhInputs`. -/
theorem h8f_untyped_fitsCap_of_exactKitFits [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel)
    (sEnvs : RunSlotEnvs)
    (hs_dp : sEnvs.decryptPrekey =
      DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
        (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
        PqxdhAcceptBadKemErrEnv)
    (E_pq : RunCall → CliRunCalleeEnvs)
    (hMainPq : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E_pq i))
    (hRunSubPq : ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) := by
  have hPre := h8f_d3Prekey_fitsCap W A sEnvs hs_dp
  let DomNP (i : Inputs) : Prop :=
    CliPqxdhInputs ⟨W.C, W.Q⟩ i ∧
      ¬ ∃ (peerV : AddrV) (rest : List (BitVec 8)),
          parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV) ∧
          i.stdin = 3#8 :: rest
  have hNP :
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
        (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
        (RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs PksmTryFromEnv (cliRunSemD3 W)))
        (domScopedRun DomNP (runRel (cliRunSemD3 W))) :=
    mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
      boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
      (fun i ⟨hi_pq, _⟩ => hMainPq i hi_pq)
      (fun i c ⟨hi_pq, _⟩ hp hin => stdin_le_msgCapBytes_of_pqInputs_and_inputOf hi_pq hp hin)
      (fun i nw out ⟨hi_pq, _⟩ ha =>
        h8f_nwDom_pqD3Recv rfl rfl rfl rfl rfl i nw out (Or.inl hi_pq) ha)
      (fun g ⟨hi_pq, hnp⟩ hparse hin _hrel evs hrun =>
        hRunSubPq g hi_pq hparse hin
          (fun peerV rest hc hst => hnp ⟨peerV, rest, hc ▸ hparse, hst⟩) evs hrun)
  intro i hok
  refine ⟨(hPre i hok).1, fun hne => ?_⟩
  refine ⟨((hPre i hok).2 hne).1, fun vcap evs_c c hc hv hp => ?_⟩
  have hm2_pre := ((hPre i hok).2 hne).2 vcap evs_c c hc hv hp
  have hm2_np := ((hNP i hok).2 hne).2 vcap evs_c c hc hv hp
  refine ⟨hm2_pre.1, fun evs_m3 hm3 => ?_⟩
  have hm3_pre := hm2_pre.2 evs_m3 hm3
  have hm3_np := hm2_np.2 evs_m3 hm3
  refine ⟨hm3_pre.1, fun hin a resP callP storesP inpP coinsP ⟨hi, hrel⟩ => ?_⟩
  by_cases hex : ∃ (peerV : AddrV) (rest : List (BitVec 8)),
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV) ∧
      i.stdin = 3#8 :: rest
  · exact hm3_pre.2 hin a resP callP storesP inpP coinsP ⟨⟨hi, hex⟩, hrel⟩
  · have hi_pq : CliPqxdhInputs ⟨W.C, W.Q⟩ i :=
      h8f_cliPqxdhInputs_of_pqOrD3Recv_nonPrekey hi hp hin
        (fun peerV rest hc hst => hex ⟨peerV, rest, hc ▸ hp, hst⟩)
    exact hm3_np.2 hin a resP callP storesP inpP coinsP ⟨⟨hi_pq, hex⟩, hrel⟩

end H8fG5Helpers

/-- `MainEntryBudgetFitsCapOf` at `binaryKitRunSlotEnvsExact` and `DecPkD3UntypedEnvOf` under `pqD3ScopedRun`. -/
theorem hole_g5a_untyped_fitsCap
    [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
              PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) := by
  exact ElfTopJoinG5A.hole_g5a_untyped_fitsCap_closed W A

/-- Block-579 `subroutine_ok` for `cliRunSemD3 W` under `LibsignalFrozen mpl` over `binaryKitRunSlotEnvsExact` and `DecPkD3UntypedEnvOf`. -/
theorem hole_g5b_hrun_untyped_binaryKit
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (hSlot520At :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits
        (binaryKitRunSlotEnvsExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
          (DecPkD3UntypedEnvOf
            (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
            cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
            SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
        (cliRunSemD3 W)
        (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hSpqrTightAt :
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced
        (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _ (LibsignalFrozen mpl)
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
         RunEnv
           (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
             (binaryKitRunSlotEnvsExact W
               (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
               cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
               (DecPkD3UntypedEnvOf
                 (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
                 cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
                 SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
             PksmTryFromEnv (cliRunSemD3 W)))
        uuidTryParse
        (runRel (cliRunSemD3 W))
        cliWrOk cliResStack) := by
  let _ := hSpqrTightAt
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5bCut.g5ba_hole_g5b_hrun_untyped_binaryKit
    hLs hblk hext_nodup ghFixed hPl_mng W γ tp hGSpqr hFs hsat hghNoAlloc hHooks h547 hSlot520At

/-- Block-520 `decryptPrekey.OkPlaced` witness for `cliRunSemD3 W` at `binaryKitRunSlotEnvsExact` and `DecPkD3UntypedEnvOf`. -/
theorem hole_gap4_untyped_slot520
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {brkStart : BitVec 64}
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostAllocHooks fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (h547 : mpl.base 547 ≠ 0#64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
      (binaryKitRunSlotEnvsExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf
          (A := (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc)
          cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
          SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      (cliRunSemD3 W)
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520) := by
  have _ := hPl_mng
  obtain ⟨hRead, hDeser⟩ :=
    hole_g2_poll_readFile_and_sessDeser_of_hooks hLs hblk hext_nodup ghFixed W γ tp hG hHooks hsat
  let _ : LibsignalFullPlacement :=
    ElfSlicesPqOomHole3Cut.libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let hh := hHooks.runHooks
  exact
    LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectPlacedBudget.decPkD3Untyped_slotOk_full_of_readEnv_placedBudget
      LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3.defaultExtrasF3
      mmpl ghFixed W h547 hG
      { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
        bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
        codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
        formatInner := hh.formatInner }
      hRead hDeser
      (cliRunSemD3 W)
      (binaryKitRunSlotEnvsExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
        (DecPkD3UntypedEnvOf
          (A := (fineHookRustCliAllocBudget γ mmpl tp brkStart).repAlloc)
          cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
          SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))
      (fun _ _ h => h) rfl rfl
      (fun _ _ _ _ h => ⟨⟨h.1.keyPairLt, h.1.preKeysWf, h.1.baseKeysLt⟩, h.2⟩)
      (by decide)

/-- `CliRunCalleeEnvs` bundle instantiating `mkBinaryKitRealCalleeEnvsSlotOf` at `cliEncryptBinaryKitSlotEnvExact` and `cliDecryptSignalBinaryKitSlotEnvExact`. -/
noncomputable abbrev mkBinaryKitRealCalleeEnvsExact [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : CliRunCalleeEnvs :=
  mkBinaryKitRealCalleeEnvsSlotOf
    (fun {_M} A B => cliEncryptBinaryKitSlotEnvExact W A B)
    (fun {_M} A B => cliDecryptSignalBinaryKitSlotEnvExact W A B)
    img S X W g

/-- Whole-`signal_session::run` binary-kit allocator trace predicate at `mkBinaryKitRealCalleeEnvsExact`. -/
noncomputable abbrev realCliRunBinaryKitEnvOfExact [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : List AllocEvent → Prop :=
  realCliRunBinaryKitEnvOfSlot
    (fun {_M} A B => cliEncryptBinaryKitSlotEnvExact W A B)
    (fun {_M} A B => cliDecryptSignalBinaryKitSlotEnvExact W A B)
    img S X W g

/-- Whole-`main` binary-kit allocator trace predicate at `mkBinaryKitRealCalleeEnvsExact`. -/
noncomputable abbrev realCliMainBinaryKitEnvOfExact [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) : List AllocEvent → Prop :=
  realCliMainBinaryKitEnvOfSlot
    (fun {_M} A B => cliEncryptBinaryKitSlotEnvExact W A B)
    (fun {_M} A B => cliDecryptSignalBinaryKitSlotEnvExact W A B)
    img S X W i

/-- Whole-`run` `RunEnv` inclusion into `realCliRunBinaryKitEnvOfExact` under `CliPqxdhInputs`. -/
theorem hole_hmain_runEnvExact_sub_binaryKit [LibsignalPlacement]
    {M : AllocCostModel}
    {FallbackEnv : PksmGhost → List AllocEvent → Prop}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A B (realCliInitBinarySlotEnvFixed W)
            (cliDecPkCanonSlotEnvExact X W))
          (CanonicalOrFallbackPksmEnv FallbackEnv)
          S)
        g evs →
      realCliRunBinaryKitEnvOfExact img S X W g evs :=
  hmx_runEnvExact_sub_runBinaryKitEnvOfSlot
    (fun {_M} A B => cliEncryptBinaryKitSlotEnvExact W A B)
    (fun {_M} A B => cliDecryptSignalBinaryKitSlotEnvExact W A B)
    img S X W A B hi hparse hin hS_enc hS_pksm

/-! ## `hmain` and D3 Arm Assemblies -/

/-- Proves `MainOkCliF3PqB2NeedLocksPlacedAt` on `cliElfBytes` under `CliElfHole2Assumption`. -/
theorem hmain_cliElf
    (hA : CliElfHole2Assumption)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  obtain ⟨w⟩ := hole_gap1_f3GhostWitness hA mpl mmpl hLs hMm
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
  refine mainOkCliF3Pq_of_block617TransferFixed w.hTrFrozen ?_
  refine (mainOkCliExtPqB2NeedLocksPlacedAt_iff mpl mmpl
    (fun W => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
    617 cliProcessInputs (LibsignalFrozen mpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits).mp ?_
  exact
    mainOkCliExtPqB2NeedLocksPlacedAt_cliGhostExterns_cliBudgetLimits_of_kitEnvFits_and_runTightOf
      w.hblk w.hext_nodup
      (@instLsCodeInvFrozen (libsignalPlacementOf mpl w.hblk w.hext_nodup))
      (fun _ => w.ghFixed)
      (fun X W => @fits2_mkBinaryKitRealCalleeEnvsDecPk
        (libsignalPlacementOf mpl w.hblk w.hext_nodup)
        (@cliDecPkCanonSlotEnvExact' (libsignalPlacementOf mpl w.hblk w.hext_nodup) X W)
        (default : Image) (cliRunSemD2c_placed X W) X W)
      (canonOrFallbackRunEnvExact' PksmTryFromEnv mpl mmpl cliElfImage.brkStart w.hblk w.hext_nodup)
      rfl
      (fun _ γ tp => w.hG γ tp)
      w.hioOf
      (fun files path _ h => boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files path h)
      w.hMainStk
      (fun _ X W i hi =>
        @ElfTopJoinKit.realCliMainBinaryKitEnvOfExact'_fitsEnv_cliBudgetLimits_closed
          (libsignalPlacementOf mpl w.hblk w.hext_nodup)
          (default : Image) (cliRunSemD2c_placed X W) X W i hi)
      (fun _ X W γ tp g hi hparse hin _ evs hevs =>
        @ElfTopJoinKit.hole_hmain_runEnvExact'_sub_binaryKit_closed
          (libsignalPlacementOf mpl w.hblk w.hext_nodup) _ PksmTryFromEnv
          (default : Image) (cliRunSemD2c_placed X W) X W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
          g hi hparse hin rfl rfl evs hevs)
      (fun h547 X W γ tp =>
        hole3_gap2_hrun_canonSlice' hLs w.hblk w.hext_nodup w.ghFixed w.hPl_mng X W γ tp
          (w.hGSpqr γ tp) w.hFs (w.hReadSat W γ tp) w.hghNoAlloc (w.hHooksBundle W γ tp) h547)

/-- Assembles `MainOkOverD3F3` on `cliElfBytes` from the ghost witness, `LibsignalFrozen`, and SPQR seams. -/
theorem hole_m24slot_overD3_assembly
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (w : F3CliElfGhostWitness mpl mmpl)
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hSpqr : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl w.hblk w.hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl w.ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    MainOkOverD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinOverD3.hole_m24slot_overD3_assembly_closed
    hLs w.ghFixed w.hookStack w.hblk w.hext_nodup w.hPl_mng w.hMainStk w.hTrFrozen
    w.hGSpqr w.hFs w.hReadSat w.hghNoAlloc w.hioOf w.hHooksBundle hF3Frozen hSpqr

/-- Assembles `MainOkUntypedD3F3` on `cliElfBytes` from `hole_g5a_untyped_fitsCap`, `hole_g5b_hrun_untyped_binaryKit`, and `hole_gap4_untyped_slot520`. -/
theorem hole_m24slot_untyped_assembly
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (w : F3CliElfGhostWitness mpl mmpl)
    (hSlot520 : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
        (slotsOfSigPkFrozenPlaced (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf
              (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
              cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
              SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
          (cliRunSemD3 W)
          (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets_placed))).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hSpqrTight : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl w.hblk w.hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl w.ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    MainOkUntypedD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  intro h547 W
  exact
    LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3.mainSubroutineD3F3_of_domScopedRunTight
      w.hblk w.hext_nodup w.ghFixed
      (@instLsCodeInvFrozen (libsignalPlacementOf mpl w.hblk w.hext_nodup))
      (RunEnvOf := fun γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
              cliRunBudgets_placed (realCliInitBinarySlotEnvFixed W)
              (DecPkD3UntypedEnvOf
                (A := (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart).repAlloc)
                cliRunBudgets_placed (ReadFileRuleEnvFixed cliIo.rd)
                SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv))
            PksmTryFromEnv (cliRunSemD3 W)))
      (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩)
      (cliRunSemD3 W)
      rfl w.hTrFrozen w.hG (w.hioOf W) w.hMainStk
      (fun γ tp =>
        @hole_g5a_untyped_fitsCap (libsignalPlacementOf mpl w.hblk w.hext_nodup) W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
      (fun γ tp =>
        hole_g5b_hrun_untyped_binaryKit hLs w.hblk w.hext_nodup w.ghFixed w.hPl_mng W γ tp
          (w.hGSpqr γ tp) w.hFs (w.hReadSat W γ tp) w.hghNoAlloc (w.hHooksBundle W γ tp)
          h547 (hSlot520 h547 W γ tp) (hSpqrTight W γ tp))

/-- Assembles `MainOkPathBD3F3` on `cliElfBytes`. -/
theorem hole_m24slot_pathB_assembly
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (w : F3CliElfGhostWitness mpl mmpl)
    (hSpqr : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl w.hblk w.hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl w.ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    MainOkPathBD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinPathB.hole_m24slot_pathB_assembly_closed
    hLs w.ghFixed w.hookStack w.hblk w.hext_nodup w.hPl_mng w.hMainStk w.hTrFrozen
    w.hGSpqr w.hFs w.hReadSat w.hghNoAlloc w.hioOf w.hHooksBundle hSpqr

/-- Assembles `MainOkValidMatchD3F3` on `cliElfBytes`. -/
theorem hole_m24slot_validMatch_assembly
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (w : F3CliElfGhostWitness mpl mmpl)
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hSpqr : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl w.hblk w.hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl w.ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    MainOkValidMatchD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinVm.hole_m24slot_validMatch_assembly_closed
    hLs w.ghFixed w.hookStack w.hblk w.hext_nodup w.hPl_mng w.hMainStk w.hTrFrozen
    w.hGSpqr w.hFs w.hReadSat w.hghNoAlloc w.hioOf w.hHooksBundle hF3Frozen hSpqr

section

open Arm64.Process (bytesOfString)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliDecPkBinaryWideSlotEnvFixed)
open CryptoGames (Party)
open CryptoVerification.E2E (partyAddressName)
open CryptoVerification.LibsignalTripleRatchetRepr (pniPrefix serviceIdParse)
open CryptoVerification.SignalSession (Address Cmd Inputs bundleDir partyAddress)
open CryptoVerification.SignalSession.Cli
  (IdGhost RunAnswer StoresGhost addressText decimalText pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall addrParse coinsOf namedWrites namedWrites_ascii parseArgs pathStr)
open CryptoVerification.SignalSession.Cli.RunCompose
  (PksmGhost RunSem addrValOf finish readBundleV runAns runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (initDef)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
  (mainSubroutineD3F3_of_domScopedRunTight)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (CliInitD3Inputs initRunSemOk_of_filesOk₀)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmAtMeEnv RunArmEnvs RunCoreEnv RunDispatchEnv RunInit2ChainEnv RunInit3Env)

private theorem hole11_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private def hole11_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem hole11_utf8_eq (s : String) : utf8 s = hole11_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, hole11_kutf8, List.utf8Encode, hole11_byteArray_toList_eq_data]

private theorem hole11_tri_utf8_eq (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = hole11_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, hole11_kutf8, List.utf8Encode,
    hole11_byteArray_toList_eq_data]

private theorem hole11_toString_one : toString (1 : Nat) = "1" := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  exact String.toList_inj.mp (by rw [ht1, hd1, String.toList_singleton]; rfl)

private def hole11_peerAddrV (P : Party) : AddrV :=
  ⟨utf8 (partyAddressName P), 1#8⟩

private theorem hole11_addrParse_bytesOfString (P : Party) :
    addrParse uuidTryParse (bytesOfString (partyAddress P).text) = some (hole11_peerAddrV P) := by
  have hpni : pniPrefix = [0x50#8, 0x4e#8, 0x49#8, 0x3a#8] := by
    unfold pniPrefix; rw [hole11_tri_utf8_eq]; rfl
  unfold bytesOfString addrParse serviceIdParse hole11_peerAddrV
  rw [hpni, hole11_utf8_eq]
  cases P <;>
    simp only [Address.text, partyAddress, partyAddressName, hole11_toString_one,
      String.toList_append] <;>
    rfl

private theorem hole11_parseArgs_init (P : Party) (dir : String) :
    parseArgs uuidTryParse ((Cmd.init (partyAddress P) dir).argv.map bytesOfString) =
      some (.init (hole11_peerAddrV P) (bytesOfString dir)) := by
  have hi : bytesOfString "init" = utf8 "init" := by
    unfold bytesOfString; rw [hole11_utf8_eq]; rfl
  have hk : utf8 "init" ≠ utf8 "keygen" := by
    rw [hole11_utf8_eq, hole11_utf8_eq]; decide
  have ha := hole11_addrParse_bytesOfString P
  simp only [Cmd.argv, List.map_cons, List.map_nil, parseArgs, hi, hk, ha, Option.map_some,
    ↓reduceIte]

private theorem hole11_pathStr_length (p : List (BitVec 8)) :
    (pathStr p).length = p.length := by
  unfold pathStr
  simp [String.length]

private theorem hole11_pId_ok (P : Party) :
    let p := pathOf (utf8 "identities") (addrValOf (hole11_peerAddrV P)).name
    (∀ b ∈ p, b.toNat < 128) ∧ p.length ≤ 64 := by
  dsimp only [addrValOf, hole11_peerAddrV, pathOf]
  simp only [hole11_utf8_eq]
  refine ⟨fun b hb => ?_, ?_⟩
  · have hall :
        ((if hole11_kutf8 "identities" = [] then hole11_kutf8 (partyAddressName P)
          else
            hole11_kutf8 "identities" ++ hole11_kutf8 "/" ++
              hole11_kutf8 (partyAddressName P)).all
          fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · cases P <;> decide

private theorem hole11_pSess_ok (P : Party) :
    let p := pathOf (utf8 "sessions") (addressText (addrValOf (hole11_peerAddrV P)))
    (∀ b ∈ p, b.toNat < 128) ∧ p.length ≤ 64 := by
  dsimp only [addrValOf, hole11_peerAddrV, addressText, decimalText, pathOf]
  rw [show (1#8 : BitVec 8).toNat = 1 from rfl, hole11_toString_one]
  simp only [hole11_utf8_eq]
  refine ⟨fun b hb => ?_, ?_⟩
  · have hall :
        ((if hole11_kutf8 "sessions" = [] then
            hole11_kutf8 (partyAddressName P) ++ hole11_kutf8 "." ++ hole11_kutf8 "1"
          else
            hole11_kutf8 "sessions" ++ hole11_kutf8 "/" ++
              (hole11_kutf8 (partyAddressName P) ++ hole11_kutf8 "." ++ hole11_kutf8 "1")).all
          fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · cases P <;> decide

private theorem hole11_namedWrites_pair_bounds
    {p1 v1 p2 v2 : List (BitVec 8)}
    (h1 : (∀ b ∈ p1, b.toNat < 128) ∧ p1.length ≤ 64)
    (h2 : (∀ b ∈ p2, b.toNat < 128) ∧ p2.length ≤ 64) :
    (namedWrites [(p1, v1), (p2, v2)]).length ≤ 4 ∧
      ∀ pw ∈ namedWrites [(p1, v1), (p2, v2)], pw.1.length ≤ 64 := by
  have hasc : ∀ w ∈ [(p1, v1), (p2, v2)], ∀ b ∈ w.1, b.toNat < 128 := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h1.1
    · exact h2.1
  rw [namedWrites_ascii _ hasc]
  refine ⟨by simp only [List.map, List.length_cons, List.length_nil]; omega, fun pw hpw => ?_⟩
  simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hpw
  rcases hpw with rfl | rfl
  · rw [hole11_pathStr_length]; exact h1.2
  · rw [hole11_pathStr_length]; exact h2.2

private theorem hole11_namedWrites_singleton_bounds
    {p1 v1 : List (BitVec 8)}
    (h1 : (∀ b ∈ p1, b.toNat < 128) ∧ p1.length ≤ 64) :
    (namedWrites [(p1, v1)]).length ≤ 4 ∧
      ∀ pw ∈ namedWrites [(p1, v1)], pw.1.length ≤ 64 := by
  have hasc : ∀ w ∈ [(p1, v1)], ∀ b ∈ w.1, b.toNat < 128 := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact h1.1
  rw [namedWrites_ascii _ hasc]
  refine ⟨by simp only [List.map, List.length_cons, List.length_nil]; omega, fun pw hpw => ?_⟩
  simp only [List.map, List.mem_singleton] at hpw
  subst hpw
  rw [hole11_pathStr_length]
  exact h1.2

private theorem hole11_initD3_nwDom
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (hi : CliInitD3Inputs ⟨W.C, W.Q⟩ i)
    (ha : runAns (cliRunSemD2c_placed X W) i = some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 := by
  rcases hi with ⟨st, files, t, -, -, -, heq⟩
  have hargv : i.argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := heq.1
  unfold runAns at ha
  rw [hargv, hole11_parseArgs_init st.party.other bundleDir] at ha
  dsimp only at ha
  rcases hown : StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") with
    _ | ownB
  · rw [hown] at ha; cases ha
  · rw [hown] at ha; dsimp only at ha
    rcases hme : addrParse uuidTryParse ownB with _ | meV
    · rw [hme] at ha; cases ha
    · rw [hme] at ha; dsimp only at ha
      rcases hbv : readBundleV (runFiles i) (bytesOfString bundleDir)
          (hole11_peerAddrV st.party.other).device with _ | bv
      · rw [hbv] at ha; cases ha
      · rw [hbv] at ha; dsimp only at ha
        change finish (initDef X ⟨W.C, W.Q⟩ (runFiles i)
            (addrValOf (hole11_peerAddrV st.party.other)) (addrValOf meV) bv (coinsOf i))
          (fun _ => []) = some (some (nw, out)) at ha
        rcases hinit : initDef X ⟨W.C, W.Q⟩ (runFiles i)
            (addrValOf (hole11_peerAddrV st.party.other)) (addrValOf meV) bv (coinsOf i) with
          _ | (_ | ⟨g', v⟩)
        · rw [hinit] at ha; cases ha
        · rw [hinit] at ha; cases ha
        · rw [hinit] at ha
          simp only [finish, Option.some.injEq, Prod.mk.injEq] at ha
          rcases ha with ⟨rfl, _⟩
          unfold initDef at hinit
          dsimp only at hinit
          split at hinit
          · cases hinit
          · split at hinit
            · cases hinit
            · cases hinit
            · split at hinit
              · split at hinit
                · cases hinit
                · next x gs _ =>
                  injection hinit with h1
                  injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  unfold IdGhost.saveUpd
                  split
                  · have hw :
                        ({ identity :=
                             { own := StoresGhost.opened.identity.own,
                               peers := StoresGhost.opened.identity.peers.put
                                 (addrValOf (hole11_peerAddrV st.party.other)).name
                                 bv.idKey.serialize },
                           signed := StoresGhost.opened.signed,
                           kyber := StoresGhost.opened.kyber,
                           oneTime := StoresGhost.opened.oneTime,
                           sessions := StoresGhost.opened.sessions.put
                             (addressText (addrValOf (hole11_peerAddrV st.party.other)))
                             (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs),
                           pub := StoresGhost.opened.pub } : StoresGhost).writes =
                        [(pathOf (utf8 "identities")
                            (addrValOf (hole11_peerAddrV st.party.other)).name,
                          bv.idKey.serialize),
                         (pathOf (utf8 "sessions")
                            (addressText (addrValOf (hole11_peerAddrV st.party.other))),
                          CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)] := rfl
                    rw [hw]
                    exact hole11_namedWrites_pair_bounds
                      (hole11_pId_ok st.party.other) (hole11_pSess_ok st.party.other)
                  · have hw :
                        ({ identity := StoresGhost.opened.identity,
                           signed := StoresGhost.opened.signed,
                           kyber := StoresGhost.opened.kyber,
                           oneTime := StoresGhost.opened.oneTime,
                           sessions := StoresGhost.opened.sessions.put
                             (addressText (addrValOf (hole11_peerAddrV st.party.other)))
                             (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs),
                           pub := StoresGhost.opened.pub } : StoresGhost).writes =
                        [(pathOf (utf8 "sessions")
                            (addressText (addrValOf (hole11_peerAddrV st.party.other))),
                          CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)] := rfl
                    rw [hw]
                    exact hole11_namedWrites_singleton_bounds (hole11_pSess_ok st.party.other)
              · cases hinit

private theorem hole11_runEnv_init_eq
    {a₁ a₂ : RunArmEnvs} {g : RunCall} {peerV : AddrV} {dir : List (BitVec 8)}
    (hpre : a₁.pre = a₂.pre)
    (hi1 : a₁.init1 = a₂.init1)
    (hi2 : a₁.init2 = a₂.init2)
    (hi3 : a₁.init3 = a₂.init3)
    (hc : g.c = .init peerV dir) :
    RunEnv a₁ g = RunEnv a₂ g := by
  have h3 : ∀ meV, RunInit3Env a₁ g meV peerV dir = RunInit3Env a₂ g meV peerV dir := fun meV => by
    funext evs; unfold RunInit3Env; rw [hi3]
  have h2 : ∀ meV, RunInit2ChainEnv a₁ g meV peerV dir = RunInit2ChainEnv a₂ g meV peerV dir :=
    fun meV => by
      funext evs; unfold RunInit2ChainEnv; rw [hi2, h3 meV]
  have harm : ∀ me, RunArmAtMeEnv a₁ g me = RunArmAtMeEnv a₂ g me := fun me => by
    funext evs; unfold RunArmAtMeEnv; rw [hc]; dsimp only
    cases me with
    | none => dsimp only; rw [hi1]
    | some meV meG => dsimp only; rw [hi1, h2 meV]
  have hdisp : RunDispatchEnv a₁ g = RunDispatchEnv a₂ g := by
    funext evs; unfold RunDispatchEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") with
    | error _ => rfl
    | ok ownB =>
      dsimp only
      cases addrParse uuidTryParse ownB with
      | none => dsimp only; rw [harm]
      | some meV => dsimp only; simp only [harm]
  unfold RunEnv RunCoreEnv
  rw [hpre, hdisp]

private theorem hole11_fitCap_initD3
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length →
      (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (pksmEnv : PksmGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (binaryKitRunSlotEnvsExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
          (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
        pksmEnv (cliRunSemD2c_placed X W)))
      (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD2c_placed X W))) := by
  let _ : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  have h0 :=
    mainEntryBudgetFitsCapOf_initD3ScopedRun_fixed
      (default : Image) (cliRunSemD2c_placed X W) X W
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
      cliRunBudgets
      (realCliDecPkBinaryWideSlotEnvFixed X W)
      (hole11_initD3_nwDom X W)
  intro i hok
  refine ⟨(h0 i hok).1, fun hne => ?_⟩
  refine ⟨((h0 i hok).2 hne).1, fun vcap evs_c c hc hv hp => ?_⟩
  have hm2 := ((h0 i hok).2 hne).2 vcap evs_c c hc hv hp
  refine ⟨hm2.1, fun evs_m3 hm3 => ?_⟩
  have hm3' := hm2.2 evs_m3 hm3
  refine ⟨hm3'.1, fun hin a resP callP storesP inpP coinsP hrun => ?_⟩
  rcases hrun.1 with ⟨st, files, t, -, -, -, heq⟩
  have hargv : i.argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := heq.1
  have hp' := hp
  rw [hargv, hole11_parseArgs_init st.party.other bundleDir] at hp'
  injection hp' with hc_eq
  let g : RunCall :=
    { i := i, c := c, a := a,
      res := resP, call := callP, stores := storesP, inp := inpP, coins := coinsP }
  have hEq :
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          pksmEnv (cliRunSemD2c_placed X W))
        g =
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (realCliDecPkBinaryWideSlotEnvFixed X W))
          PksmTryFromEnv (cliRunSemD2c_placed X W))
        g :=
    hole11_runEnv_init_eq rfl rfl rfl rfl hc_eq.symm
  have hgoal := hm3'.2 hin a resP callP storesP inpP coinsP hrun
  dsimp only at hgoal ⊢
  rwa [hEq]

/-- Assembles `MainInitSemF3` on `cliElfBytes`. -/
theorem hole_m24slot_initSem_assembly
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (w : F3CliElfGhostWitness mpl mmpl)
    (hSpqr : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl w.hblk w.hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl w.ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    MainInitSemF3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  have _ := hSpqr
  intro h547 X W
  refine ⟨cliRunSemD2c_placed X W, initRunSemOk_of_filesOk₀ rfl rfl rfl, ?_⟩
  exact mainSubroutineD3F3_of_domScopedRunTight w.hblk w.hext_nodup w.ghFixed
    (@instLsCodeInvFrozen (libsignalPlacementOf mpl w.hblk w.hext_nodup))
    (CliInitD3Inputs ⟨W.C, W.Q⟩) (cliRunSemD2c_placed X W)
    rfl w.hTrFrozen w.hG (w.hioOf W) w.hMainStk
    (fun γ tp => hole11_fitCap_initD3 w.hblk w.hext_nodup _ X W γ tp)
    (fun γ tp =>
      hole3_gap2_hrun_canonSlice' hLs w.hblk w.hext_nodup w.ghFixed w.hPl_mng X W γ tp
        (w.hGSpqr γ tp) w.hFs (w.hReadSat W γ tp) w.hghNoAlloc (w.hHooksBundle W γ tp) h547)

end

/-! ## Per-Arm `cliElfBytes` Wrappers and Top-Level Closure -/

theorem hoverD3_cliElf
    (hA : CliElfHole2Assumption)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkOverD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  obtain ⟨w⟩ := hole_gap1_f3GhostWitness hA mpl mmpl hLs hMm
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
  exact hole_m24slot_overD3_assembly hLs w
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
    (fun W γ tp =>
      hole_m24slot_spqrSeams_tight hLs w.hblk w.hext_nodup w.ghFixed W γ tp w.hPl_mng
        (w.hGSpqr γ tp))

theorem huntyped_cliElf
    (hA : CliElfHole2Assumption)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkUntypedD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  obtain ⟨w⟩ := hole_gap1_f3GhostWitness hA mpl mmpl hLs hMm
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
  exact hole_m24slot_untyped_assembly hLs w
    (fun h547 W γ tp =>
      hole_gap4_untyped_slot520 hLs w.hblk w.hext_nodup w.ghFixed w.hPl_mng W γ tp
        (w.hG γ tp) (w.hHooksBundle W γ tp) (w.hReadSat W γ tp) h547)
    (fun W γ tp =>
      hole_m24slot_spqrSeams_tight hLs w.hblk w.hext_nodup w.ghFixed W γ tp w.hPl_mng
        (w.hGSpqr γ tp))

theorem hpathB_cliElf
    (hA : CliElfHole2Assumption)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkPathBD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  obtain ⟨w⟩ := hole_gap1_f3GhostWitness hA mpl mmpl hLs hMm
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
  exact hole_m24slot_pathB_assembly hLs w
    (fun W γ tp =>
      hole_m24slot_spqrSeams_tight hLs w.hblk w.hext_nodup w.ghFixed W γ tp w.hPl_mng
        (w.hGSpqr γ tp))

theorem hvalidMatch_cliElf
    (hA : CliElfHole2Assumption)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainOkValidMatchD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  obtain ⟨w⟩ := hole_gap1_f3GhostWitness hA mpl mmpl hLs hMm
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
  exact hole_m24slot_validMatch_assembly hLs w
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
    (fun W γ tp =>
      hole_m24slot_spqrSeams_tight hLs w.hblk w.hext_nodup w.ghFixed W γ tp w.hPl_mng
        (w.hGSpqr γ tp))

theorem hinitSem_cliElf
    (hA : CliElfHole2Assumption)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    MainInitSemF3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  obtain ⟨w⟩ := hole_gap1_f3GhostWitness hA mpl mmpl hLs hMm
    (fun _m hCO => hole_gap3_f3CodeOk_to_libsignalFrozen hLs hCO)
  exact hole_m24slot_initSem_assembly hLs w
    (fun W γ tp =>
      hole_m24slot_spqrSeams_tight hLs w.hblk w.hext_nodup w.ghFixed W γ tp w.hPl_mng
        (w.hGSpqr γ tp))

/-- Top-level `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` theorem under `CliElfHole2Assumption`. -/
theorem cliPqBinaryV2OomF3BytesPlaced_cliElf
    (hA : CliElfHole2Assumption) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main
    cliElf_parse
    (fun _mpl _mmpl hLs hMm => cliElf_f3B2NeedLocksAssumptions hLs hMm)
    (hmain_cliElf hA)
    (hoverD3_cliElf hA)
    (huntyped_cliElf hA)
    (hpathB_cliElf hA)
    (hvalidMatch_cliElf hA)
    (hinitSem_cliElf hA)

theorem _root_.LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced.cliPqBinaryV2OomF3BytesPlaced_cliElf
    (hA : CliElfHole2Assumption) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst.cliPqBinaryV2OomF3BytesPlaced_cliElf hA

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst