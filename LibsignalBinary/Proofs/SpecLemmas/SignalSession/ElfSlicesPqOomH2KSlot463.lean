/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.CryptoHookFds
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv

/-!
# Spine-C Slot `463` (`decryptSignal`) Closure at `h2k_ghFixedK` (`ElfSlicesPqOomH2KSlot463`)

**Checked by Lean.**

Discharges `h2ki_DecryptSignalSlot463OkAtPreFd` and `h2ki_W2DecryptSignalSlot463OkK` on
`lsProg_579` calling `mpl.base 463` via `AllocWithFds.withFds`,
`ElfSlicesPqOomH2KStrCloneFds.h2kb_runHooksPlaced_withFds`, and the `{M} {A}`-generic
`h2k463_spqrSeams_topStateGuarded_of_hmac` discharger.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  libsignalMutatedBlocks libsignalSessionExterns lsmpl
)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives aesDecHookMallocng pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (signalMessageAt uuidTryParse)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.SignalSession (
  CliHooks cliBcmpHook cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym
)
open CryptoVerification.SignalSession.Cli (PathGhost StoresGhost cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliRunNeeds cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_589 lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecSigGhost RunSem idVtPlaced mkSlot sessVtPlaced withCodeOk
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_bcmp cliGhostExterns cliGhostExterns_bcmp
)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed cliDecryptSignalNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets pathNeed)
open CryptoVerification.SignalSession.Cli.Slots (
  encodeInjOn_deserializeScopeP_Q scopeIn scopeKit
)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (
  PeerSpqrStateTight640 peerSpqrStateTight640_of_cliSessionStoreSpec
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf (TryDecryptCliLinkedEnvOf)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (
  FromLoadPolledEnv FromRegionSomeEnv WithStoresDecEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed ReadFileRuleEnvFixed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  cliGhostAllocHooks_withFds cliGhostExterns_libcruxHmac_withFds_hookSat
  fineAesDec_budget_withFds_hookOk withFds withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (SessKitHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams (
  w2IdVt_placed_ok w2SessVt_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  decSigSlotSpecBasePlaced decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf slotFramePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlacedBudgetFd (
  subroutine_ok_dirGet_withFds w2_inner_binaryKitFixed_full_placed_ok_of_dirGet_ofEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget (
  InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget (
  CliDecryptSignalSlotEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudgetFd (
  decSigSlotSpecFrozenPlaced_withFds_to_preFd
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget (
  cliDecryptSignal_slot_full_placed decSigDef_eq_runProofs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_bcmp_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsFsPlaced dirGetSpecPlaced pathSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges (
  h2kb_hole2_hG h2kb_hole2_runHooksPlaced
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit (
  dirGet_placed_ok_of_h2k_fd h2k_hole2_hReadSatK_withFds
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (
  h2k_ghFixedK h2k_readFileSpecK
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces (
  h2ki_DecryptSignalSlot463OkAtPreFd h2ki_W2DecryptSignalSlot463OkK slotWithPreFdsGe3Closed
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds (
  h2kb_hole2_hGSpqr_withFds h2kb_runHooksPlaced_withFds
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness (
  F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2LsRetAddrKeep (
  h2lr_lsRetAddr624_keepSub_false
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut (
  cliDecryptSignalBinaryKitSlotEnvExact libsignalFullPlacementOf
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst (
  hole2_hblk hole2_hext_nodup hole2_keepSub
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2 (
  w4s2_SpqrRecvTopStateGuardedBytesEnv w4s2_TryDecryptTopStateGuardedEnv
  w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromVEnv RecordDecryptEnv recordTryDecryptEnvArgs
)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

/-! ## `pathSpecPlaced (withFds A)` to `withFdsGe3Closed (pathSpecPlaced A)` -/

/-- Convert `subroutine_ok` at `pathSpecPlaced (withFds A) lim PathEnv₀ stk` into
`withFdsGe3Closed (pathSpecPlaced A lim PathEnv₀ stk)` when `lim.enforced = true`. -/
theorem subroutine_ok_path_withFds_of_withFds [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    (A : RustCliAllocBudget M) {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {PathEnv₀ : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {stk : Nat}
    (hok : subroutine_ok prog entry (pathSpecPlaced (withFds A) lim PathEnv₀ stk)) :
    subroutine_ok prog entry (withFdsGe3Closed (pathSpecPlaced A lim PathEnv₀ stk)) := by
  refine subroutine_ok_mono hok (fun (x, st) R s0 hpre => ?_) (fun (x, st) R s0 sf hpost => ?_)
  · dsimp only [withFdsGe3Closed, pathSpecPlaced, withLsCodeRoLoaded, withCodeOk] at hpre ⊢
    rw [withFds_pool_enforced A henf]
    refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, pathSpecPlaced, withLsCodeRoLoaded,
      withFds_repAlloc] at hpost ⊢
    simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    rw [withFds_pool_enforced A henf (M.stepEvents evs st) sf] at hpost
    exact ⟨evs, Satisfies.of_eq hpost (by sep_ac_rfl)⟩

/-- Assemble `subroutine_ok (lsProg_589 H) (lsmpl.base 589) (dirGetSpecPlaced ... (withFds A) ...)`
on Block `589` at `H := cliGhostExterns gh (cliExternsPlaced mmpl W)` from `h2k_readFileSpecK` +
`hhWithFds` + `hAllocFs`. -/
theorem h2k463_dirGet_withFds_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hAllocFs : AllocContractsFsPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hhWithFds : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadSatFd : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsReadFileSym
      (withFdsGe3Closed
        (h2k_readFileSpecK cliIo.rd cliWrOk A lim cliRunBudgets.readFile
          (ReadFileRuleEnvFixed cliIo.rd)))) :
    subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) lim
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (RunBudgets.dirGetNeed ⟨cliRunBudgets.readFile⟩)) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hsh := SessKitHooksPlaced.of_runHooks hhWithFds
  have hbcmp : HookSat H "bcmp" (withVmPreserved cliBcmpSpec).keepsFs := by
    obtain ⟨f, hf_eq, hf_ok⟩ := cliExternsPlaced_bcmp_budget_sat mmpl W
    have hf : f = cliBcmpHook W.bcmp :=
      Option.some.inj (hf_eq.symm.trans (cliExternsPlaced_bcmp mmpl W))
    subst hf
    exact ⟨cliBcmpHook W.bcmp, cliGhostExterns_bcmp mmpl gh W, hf_ok.keepsFs (fun _ => rfl)⟩
  have hPathPool : subroutine_ok (lsProg_589 H) (lsmpl.base 596)
      (pathSpecPlaced (withFds A) lim PathEnv pathNeed) :=
    hsh.path (callerProg := lsProg_589 H) (i := 589) (Nat.le_refl pathNeed) (by decide)
  have hPathFd : subroutine_ok (lsProg_589 H) (lsmpl.base 596)
      (withFdsGe3Closed (pathSpecPlaced A lim PathEnv pathNeed)) :=
    subroutine_ok_path_withFds_of_withFds A henf hPathPool
  have hlr : hole2_keepSub ((blkPl_589).base + 336#64) = false :=
    h2lr_lsRetAddr624_keepSub_false hLs
      (lsRetAddr624_blockPlacement_base_add 589 336#64 (by decide) (by decide))
  have hGetFd : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (withFdsGe3Closed
        (dirGetSpecPlaced cliIo.rd cliWrOk A lim
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (RunBudgets.dirGetNeed ⟨cliRunBudgets.readFile⟩))) :=
    dirGet_placed_ok_of_h2k_fd
      (pathProg := lsProg_589 H) (jPath := 589)
      (fun _ hp => hp.2) hAllocFs hbcmp (by decide) (by decide)
      hPathFd hReadSatFd hlr (hhWithFds.fs (lsProg_589 H) 589)
      (Nat.le_refl (RunBudgets.dirGetNeed ⟨cliRunBudgets.readFile⟩))
      (fun _ _ _ _ h => h)
  exact subroutine_ok_dirGet_withFds henf hGetFd

/-! ## `PeerSpqrStateTight640` Guard Upgrade at Generic `A : RustCliAllocBudget M` -/

private theorem h2k463_not_fitsEnv_top {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    ¬ FitsEnv M lim st (fun _ => True) := fun h =>
  Nat.not_succ_le_self MallocngMaxAllocSize
    (h [AllocEvent.alloc (MallocngMaxAllocSize + 1)] trivial).1.1

private theorem h2k463_seqEnv_congr {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : E₁ = E₁') (h2 : E₂ = E₂') :
    SeqEnv E₁ E₂ = SeqEnv E₁' E₂' := by
  rw [h1, h2]

private theorem h2k463_or_congr {P P' Q Q' : Prop} (hp : P = P') (hq : Q = Q') :
    (P ∨ Q) = (P' ∨ Q') := by
  rw [hp, hq]

private theorem h2k463_and_congr {P P' Q Q' : Prop} (hp : P = P') (hq : Q = Q') :
    (P ∧ Q) = (P' ∧ Q') := by
  rw [hp, hq]

private theorem h2k463_exists_congr {α : Sort _} {P Q : α → Prop} (h : ∀ a, P a = Q a) :
    (∃ a, P a) = (∃ a, Q a) := by
  simp only [h]

private theorem h2k463_cliDecryptSignalSlotEnv_topStateGuarded_eq_linked_of_peer
    [LibsignalPlacement] {M : AllocCostModel} (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (x : DecSigGhost)
    (hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val) :
    CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w4s2_TryDecryptTopStateGuardedEnv W)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let z := toDecryptGhost x
  let kit := decSessKitPlaced A.repAlloc x.F x.peer B
  let ke := decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer
  let ikit := decIdKitPlaced A.repAlloc x.F x.peer B
  let ike := decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer
  let st0 := StoresGhost.opened.sessions
  let ist0 := StoresGhost.opened.identity
  let TdLinked := TryDecryptCliLinkedEnvOf 109 W.C W.Q.K
  have hrd : ∀ G (ses_st : SessionState (List (BitVec 8))),
      TopStateTight W.C.F W.Q.K ses_st.pqRatchetState →
      RecordDecryptEnv (w4s2_TryDecryptTopStateGuardedEnv W) (recGhostOf z 0#64 G ses_st) =
        RecordDecryptEnv TdLinked (recGhostOf z 0#64 G ses_st) := by
    intro G ses_st hTop
    funext evs
    unfold RecordDecryptEnv FromVEnv
    by_cases hv : (recGhostOf z 0#64 G ses_st).st.version.toNat =
        (recGhostOf z 0#64 G ses_st).msg.messageVersion.toNat
    · simp only [hv, ↓reduceIte]
      refine h2k463_exists_congr fun G₁ => ?_
      have htd := w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W
        (recordTryDecryptEnvArgs (recGhostOf z 0#64 G ses_st) G₁) hTop
      exact h2k463_and_congr rfl (congrFun (h2k463_seqEnv_congr rfl (h2k463_seqEnv_congr htd rfl)) evs)
    · simp only [hv, ↓reduceIte]
  have hlp :
      FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse
          (w4s2_TryDecryptTopStateGuardedEnv W) kit ke st0 ikit ike ist0 scopeKit z =
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse
          TdLinked kit ke st0 ikit ike ist0 scopeKit z := by
    refine h2k463_seqEnv_congr rfl (funext fun evs => ?_)
    refine h2k463_or_congr rfl (h2k463_or_congr rfl (h2k463_or_congr rfl ?_))
    refine h2k463_exists_congr fun rec =>
      h2k463_exists_congr fun ses =>
        h2k463_exists_congr fun G => by
          have hrs_eq_of :
              ∀ (hScAt : kit.ScopeAt scopeKit st0 z.rem.val rec)
                (_hcur : rec.currentSession = some ses),
                FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
                    (w4s2_TryDecryptTopStateGuardedEnv W) kit ke st0 ikit ike ist0 z rec G ses.state =
                  FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
                    TdLinked kit ke st0 ikit ike ist0 z rec G ses.state := by
            intro hScAt hcur
            have hTop : TopStateTight W.C.F W.Q.K ses.state.pqRatchetState :=
              peerSpqrStateTight640_of_cliSessionStoreSpec
                (A := A.repAlloc) (b := 0#64) (pathOk := cliWrOk) (peer := x.peer)
                (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
                hScAt hcur rfl hPeer
            exact h2k463_seqEnv_congr (hrd G ses.state hTop) rfl
          exact propext
            ⟨fun ⟨hScAt, hcur, hGV, hrs⟩ =>
              ⟨hScAt, hcur, hGV, Eq.mp (congrFun (hrs_eq_of hScAt hcur) evs) hrs⟩,
             fun ⟨hScAt, hcur, hGV, hrs⟩ =>
              ⟨hScAt, hcur, hGV, Eq.mpr (congrFun (hrs_eq_of hScAt hcur) evs) hrs⟩⟩
  unfold CliDecryptSignalSlotEnv WithStoresDecEnv
  exact h2k463_seqEnv_congr rfl hlp

private theorem h2k463_decSigSlotSpecFrozenPlaced_mono_guarded [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    (W : CliHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem) (stk : Nat)
    (hok : subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced A lim
        (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w4s2_TryDecryptTopStateGuardedEnv W)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B))
        S stk)) :
    subroutine_ok prog entry
      (decSigSlotSpecFrozenPlaced A lim
        (cliDecryptSignalBinaryKitSlotEnvExact W A B) S stk) := by
  refine subroutine_ok_mono hok (fun (x, st) R s0 hpre => ?_) (fun (x, st) R s0 sf hpost => ?_)
  · by_cases hPeer : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
    · have henv :
          cliDecryptSignalBinaryKitSlotEnvExact W A B x =
            CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (w4s2_TryDecryptTopStateGuardedEnv W)
              (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
              (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
        have h1 :
            cliDecryptSignalBinaryKitSlotEnvExact W A B x =
              CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
                (TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
                (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
                (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x := by
          funext evs
          exact propext ⟨fun f => f hPeer, fun hp _ => hp⟩
        exact h1.trans
          (h2k463_cliDecryptSignalSlotEnv_topStateGuarded_eq_linked_of_peer W A B x hPeer).symm
      dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
        decSigSlotSpecBasePlaced] at hpre ⊢
      rwa [henv] at hpre
    · dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
        decSigSlotSpecBasePlaced] at hpre
      let H_sp : SepProp :=
        slotFramePlaced A lim st x.toSlotCtx s0 ∗ signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk ∗ ⌜LibsignalFrozen lsmpl s0.mem⌝ ∗ R
      have hpre' : s0.mem ⊨
          ⌜s0.readReg64 .x0 = x.msgA ∧ s0.readReg64 .x1 = x.peerA ∧ s0.readReg64 .x2 = x.meA ∧
            s0.readReg64 .x3 = x.stores + 0xf0#64 ∧ s0.readReg64 .x4 = sessVtPlaced ∧
            s0.readReg64 .x5 = x.stores ∧ s0.readReg64 .x6 = idVtPlaced ∧
            s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
            stk ≤ s0.sp.toNat ∧ FitsEnv M lim st (cliDecryptSignalBinaryKitSlotEnvExact W A B x)⌝ ∗
          H_sp := by
        dsimp only [H_sp]
        refine Eq.mp (congrArg (s0.mem ⊨ ·) ?_) hpre; sep_ac_rfl
      rw [satisfies_pure_sepConj] at hpre'
      have hfit := hpre'.1.2.2.2.2.2.2.2.2.2.2.2
      have htop : FitsEnv M lim st (fun _ => True) :=
        FitsEnv.mono (fun _ _ h => False.elim (hPeer h)) hfit
      exact False.elim (h2k463_not_fitsEnv_top htop)
  · dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
      decSigSlotSpecBasePlaced] at hpost ⊢
    refine Satisfies.mono (sepConj_mono_left
      (Entails.sepExists_mono fun evs =>
        Entails.sepExists_mono fun g' =>
          Entails.sepExists_mono fun e => ?_)) hpost
    apply Entails.pure_left
    rintro ⟨hevs, htr, hout⟩
    refine Entails.pure_right ⟨?_, htr, hout⟩ (Entails.refl _)
    intro hPeer
    exact Eq.mp
      (congrFun
        (h2k463_cliDecryptSignalSlotEnv_topStateGuarded_eq_linked_of_peer W A B x hPeer) evs)
      hevs

/-! ## `h2ki_DecryptSignalSlot463OkAtPreFd` and `h2ki_W2DecryptSignalSlot463OkK` -/

/-- Discharges `h2ki_DecryptSignalSlot463OkAtPreFd` on `lsProg_579` calling `mpl.base 463` via
`AllocWithFds.withFds`. -/
theorem h2k463_decryptSignalSlot463OkAtPreFd
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hAllocFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      AllocContractsFsPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hReadSatFd :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (withFdsGe3Closed
          (h2k_readFileSpecK cliIo.rd cliWrOk
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
            cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))))
    (hhWithFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      RunHooksPlaced
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
        cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hSpqrWithFds :
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel
        (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
        cliBudgetLimits mmpl ghFixed W InitEnv
        (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
        SendEnv)
    (h547 : mpl.base 547 ≠ 0#64) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    h2ki_DecryptSignalSlot463OkAtPreFd
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      X W := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  have hGetPool :
      subroutine_ok (lsProg_589 H) (lsmpl.base 589)
        (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) cliBudgetLimits
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (RunBudgets.dirGetNeed ⟨cliRunBudgets.readFile⟩)) :=
    h2k463_dirGet_withFds_ok rfl hLs hAllocFs hhWithFds hReadSatFd
  have hAesDecPool :
      HookOk (aesDecHookMallocng mmpl W.C.D)
        (aesDecBudgetSpec W.C.D fineCostModel (withFds A) cliBudgetLimits) :=
    fineAesDec_budget_withFds_hookOk γ tp cliElfImage.brkStart cliBudgetLimits hPl_mng W.C.D
  have hInnerPool :
      InnerDecryptFrozenPlacedOk ⟨W.C, W.Q⟩ (withFds A) cliBudgetLimits
        H cliRunBudgets
        (w4s2_TryDecryptTopStateGuardedEnv W)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) :=
    w2_inner_binaryKitFixed_full_placed_ok_of_dirGet_ofEnv mmpl ghFixed W
      (withFds A) cliBudgetLimits h547
      (cliGhostAllocHooks_withFds hG) hhWithFds hGetPool hAesDecPool hSpqrWithFds
      (w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty W.C.F W.Q.K)
      (fun _ _ h => h)
  intro stk hstk hstk64
  dsimp only [h2ki_DecryptSignalSlot463OkAtPreFd, slotWithPreFdsGe3Closed, mkSlot] at hstk ⊢
  have hstk' : cliDecryptSignalNeed cliRunBudgets ≤ stk := hstk
  have hSlotPool :
      subroutine_ok (lsProg_579 H) (lsmpl.base 463)
        (decSigSlotSpecFrozenPlaced (withFds A) cliBudgetLimits
          (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ (withFds A) cliRunBudgets
            (w4s2_TryDecryptTopStateGuardedEnv W)
            (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
            (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets))
          (cliRunSemD2c_placed X W) stk) :=
    cliDecryptSignal_slot_full_placed (i := 579)
      mmpl ghFixed W (withFds A) cliBudgetLimits cliRunBudgets
      (cliRunSemD2c_placed X W) scopeIn (w4s2_TryDecryptTopStateGuardedEnv W)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
      hhWithFds
      (w2SessVt_placed_ok A.repAlloc cliRunBudgets h547)
      (w2IdVt_placed_ok A.repAlloc cliRunBudgets h547)
      hInnerPool
      encodeInjOn_deserializeScopeP_Q (fun _ h => h)
      (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
      (fun _ _ _ hf => ⟨hf.1, hf.2.1⟩)
      stk hstk' hstk64
  have hSlotGuardedPool :
      subroutine_ok (lsProg_579 H) (lsmpl.base 463)
        (decSigSlotSpecFrozenPlaced (withFds A) cliBudgetLimits
          (cliDecryptSignalBinaryKitSlotEnvExact W (withFds A) cliRunBudgets)
          (cliRunSemD2c_placed X W) stk) :=
    h2k463_decSigSlotSpecFrozenPlaced_mono_guarded W (withFds A) cliBudgetLimits
      cliRunBudgets (cliRunSemD2c_placed X W) stk hSlotPool
  exact decSigSlotSpecFrozenPlaced_withFds_to_preFd A rfl
    (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
    (cliRunSemD2c_placed X W) stk hSlotGuardedPool

/-- Witness-packaged `h2ki_W2DecryptSignalSlot463OkK w` closer for any
`w : F3CliElfGhostWitnessK mpl mmpl`. -/
theorem h2k463_w2DecryptSignalSlot463OkK_of_witness
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits w.ghFixed)
    (hAllocFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        AllocContractsFsPlaced
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)))
    (hReadSatFd :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookSat (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
          (withFdsGe3Closed
            (h2k_readFileSpecK cliIo.rd cliWrOk
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
              cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))))
    (hhWithFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        RunHooksPlaced
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W)))
    (hSpqrWithFds :
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl w.hblk w.hext_nodup)
          fineCostModel
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits mmpl w.ghFixed W InitEnv
          (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
          SendEnv) :
    h2ki_W2DecryptSignalSlot463OkK w := by
  intro h547 X W γ tp
  exact h2k463_decryptSignalSlot463OkAtPreFd hLs w.hblk w.hext_nodup w.ghFixed w.hPl_mng
    X W γ tp (hG γ tp) (hAllocFs W γ tp) (hReadSatFd W γ tp)
    (hhWithFds W γ tp) (hSpqrWithFds W γ tp) h547

/-! ## `{M} {A}`-Generic `SpqrV1PlacedSeamsOfEnv` and Unconditional Slot-`463` Closure -/

section SpqrTopStateGuarded

set_option linter.style.haveILetI false

open Arm64.Process SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (ls_blockPlacement_base)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB
   pbToPqRatchetState spqrAuthApi spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchet (VecArg sessionMemmoveSpec)
open CryptoVerification.SignalSession
  (cliHookTablePlaced lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (cliExternsPlaced_row cliGhostExterns_other hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced compress256_row_placed trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Alloc (growOneStack)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.SendTotal
  (BOkTight isEkSide st_bCodec st_bRecvCt_tight st_bRecvEk_tight st_bSize_tight)
open CryptoVerification.SpqrV1Sync.TopSync (topPb)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedAux
  (spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness (spqrRecvTightLinkedEnv_nil_exists)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux (spqrRecvBranchHyps_tightLinked)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
  (StatesRecvExactTightEnv StatesRecvProtoEnv' statesRecvExactTightEnv_sub_statesRecvProtoEnv'
   states_recv_placed_ok_x_exactTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidV1PtsAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_DecodeStateGuardedEnv tlb_DecodeStateTightEnvOf tlb_V1StateMergeBlk325TightOkOf
   tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (topStateTight_decode_props topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf (SpqrRecvC07C09aTightLinkedEnvOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (cliExternsPlaced_exactMemcpy_sat cliExternsPlaced_sessionMemsetRegion_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget
  (cliV1StateMerge_closed_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (chainParamsMerge_decodeState_of_prost cliChainParams_294_cl cliDeallocBudget_at_block
   cliDrop_267_cl cliDrop_270_cl cliEpochDir_299_cl cliFrom_261_cl cliGrowOne_356_cl
   cliLibcMemcpyBudget_at_block cliPushMerge_257_cl cliSessionMemcpyBudget_at_block
   cliSkipBudget_263_cl cliVarint_291_cl decodeErrorPush_of_merge
   epochDirectionMerge_decodeState_of_prost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
  (cliBytesExact_290_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliExternsPlaced_mlkemDecaps_budget_sat cliExternsPlaced_mlkemEncaps2_budget_sat
   cliExternsPlaced_mlkemValidatePk_budget_sat cliExternsPlaced_sessionMemmove_allocVm_sat
   cliRecvCt2PlacedAllocExt)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesFromPbGateU2Bridge
  (gu2b_SpqrSendCoinsExactFromPbLinkedEnv gu2b_StatesFromPbGuardedEnv
   gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (spqrRecvPlacedInnerSpecXTOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudgetInst
  (cliSpqrRecvPlacedContracts_exact trTrapExternsPlaced_isPanic)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2 (w4s2_trTrap_hExt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.V1MergeBlk325Cli
  (v1StateMergeBlk325_cli_of_hExt)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget (StatesIntoPbExactEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedTightBudgetR
  (statesIntoPbExactEnv_tight statesIntoPbTightDom_of_bokTight)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudgetSat
  (statesRecvPlacedContracts_of_ro_leaves_sat)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
  (e2ar_epochDirectionMerge_blk325_cl_ok_tight)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightDecodeStatePlacedBudget
  (e2a_decodeState_cl_placed_ok_of_v1Merge_109)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeStateClPlacedBudget
  (mkDecodeStateCalleeContractsClPlacedX_of_blocks)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContractsOfEnv decodeStatePlacedSpecXOfEnv statesRecvPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
  (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksExactBudgetSat hookSatExactMemcpy_of_sym_eq)

private theorem h2k463_hExt_withPanics (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := fun sym hne => by
  rw [← withPanics_cliGhostExterns mmpl gh W]
  simp only [Rust.withPanics, hExt sym hne]

private theorem h2k463_cliGhost_row_aux (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide) (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans
    (cliExternsPlaced_row mmpl W hrow)

private def h2k463_FromPbStateGuard (F : ShaCompress) (pb : V1State) : Prop :=
  (∃ st : States spqrPolyApi (spqrAuthApi F), BOkTight st ∧ pb = st.into_pb) ∧
    rawV1State pb ≤ 46880 ∧ ValidV1PtsAt 640 pb

private def h2k463_IntoPbStateGuard {F : ShaCompress} (st1 : States spqrPolyApi (spqrAuthApi F)) : Prop :=
  BOkTight st1 ∧ rawV1State st1.into_pb ≤ 46880

private def h2k463_StatesRecvExactPairTightEnv {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (evs : List AllocEvent) : Prop :=
  ∃ outA selfA msgA, StatesRecvExactTightEnv K ⟨outA, selfA, msgA, st, msg⟩ evs

private theorem h2k463_topStateTight_fromPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb)) :
    h2k463_FromPbStateGuard F pb := by
  have hprops := (topStateTight_decode_props hTop hdec).2.2.1 pb hinner
  obtain ⟨_, _, hlt31⟩ := topStateTight_to_tightValid640 hTop
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨_, _, _, st, _, _, _, vn?, ch?, _, hw⟩ := hTop
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq : stBytes = encodeState (pbToPqRatchetState (topPb st vn? ch?)) := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hdec
  have hpre := Except.ok.inj hdec; subst hpre
  simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hinner
  cases hinner
  exact ⟨⟨st, hw.hbok, rfl⟩, hprops⟩

private theorem h2k463_topStateTight_intoPbStateGuard {F : ShaCompress} {K : MlKem} {stBytes : Bytes}
    (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} (hdec : spqrDecodeState stBytes = .ok pre_pb)
    {pb : V1State} (hinner : pre_pb.inner = some (.v1 pb))
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    {sckaMsg : Message spqrPolyApi} {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hrecv : States.recv K st0 sckaMsg = .ok v) :
    h2k463_IntoPbStateGuard v.state := by
  obtain ⟨⟨st, hbok, rfl⟩, -⟩ := h2k463_topStateTight_fromPbStateGuard hTop hdec hinner
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st :=
    st_bCodec F st hbok.1
  rw [hcodec] at hfrom
  have hst0 := Except.ok.inj hfrom; subst hst0
  rcases v with ⟨key, st1⟩
  have hbok1 : BOkTight st1 := by
    cases hek : isEkSide st
    · exact st_bRecvCt_tight F K hek hbok hrecv
    · exact st_bRecvEk_tight F K hek hbok hrecv
  exact ⟨hbok1, st_bSize_tight F st1 hbok1⟩

private theorem h2k463_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hpre | ⟨evs₁, evs₂, rfl, he1, he2⟩
  · exact Or.inl (h1 evs hpre)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ he1, h2 evs₂ he2⟩

private theorem h2k463_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
    {F : ShaCompress} {K : MlKem}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hFromPb_sub : ∀ pb evs, h2k463_FromPbStateGuard F pb → FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ g evs, h2k463_IntoPbStateGuard g.st → IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    {stBytes : Bytes} (hTop : TopStateTight F K stBytes)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (h : SpqrRecvTightLinkedEnv F K
      (fun _ => tlb_DecodeStateTightEnvOf 109) FromPbEnv IntoPbEnv
      (h2k463_StatesRecvExactPairTightEnv K)
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    SpqrRecvC07C09aTightLinkedEnvOf 109 F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs := by
  rcases h with ⟨hTight, hLink⟩
  refine ⟨?_, hLink⟩
  rcases hTight with hfree | hseq
  · exact Or.inl hfree
  · refine Or.inr (h2k463_seqEnv_mono (fun _ hd => hd) (fun _ hafter => ?_) hseq)
    rcases hafter with hfree1 | ⟨hdec, hbr⟩
    · exact Or.inl hfree1
    · refine Or.inr ⟨hdec, ?_⟩
      rcases hbr with hless | hgt | ⟨hinner, heq⟩
      · exact Or.inl hless
      · exact Or.inr (Or.inl hgt)
      · refine Or.inr (Or.inr ⟨hinner, ?_⟩)
        have hPbG : h2k463_FromPbStateGuard F pb :=
          h2k463_topStateTight_fromPbStateGuard hTop hdec hinner
        refine h2k463_seqEnv_mono (fun _ hf => hf) (fun _ hmd => ?_) heq
        rcases hmd with hfree2 | hfromSeq
        · exact Or.inl hfree2
        · refine Or.inr (h2k463_seqEnv_mono (fun evsF hf => hFromPb_sub pb evsF hPbG hf)
            (fun _ haf => ?_) hfromSeq)
          rcases haf with hfree3 | ⟨hfrom, hrecvSeq⟩
          · exact Or.inl hfree3
          · refine Or.inr ⟨hfrom, h2k463_seqEnv_mono
              (fun _ ⟨outA, selfA, msgA, hr⟩ =>
                statesRecvExactTightEnv_sub_statesRecvProtoEnv' K
                  ⟨outA, selfA, msgA, st0, sckaMsg⟩ hfrom hr)
              (fun _ har => ?_) hrecvSeq⟩
            rcases har with hfree4 | ⟨hrecv, hxS, hv1c⟩
            · exact Or.inl hfree4
            · refine Or.inr ⟨hrecv, hxS, ?_⟩
              have hIntoG : h2k463_IntoPbStateGuard xSInto.st :=
                hxS.symm ▸ h2k463_topStateTight_intoPbStateGuard hTop hdec hinner hfrom hrecv
              refine h2k463_seqEnv_mono (fun _ hc => hc) (fun _ he1 => ?_) hv1c
              rcases he1 with hfree5 | ⟨hc1, hc2, haddSeq⟩
              · exact Or.inl hfree5
              · refine Or.inr ⟨hc1, hc2, h2k463_seqEnv_mono (fun _ ha => ha) (fun _ he2 => ?_) haddSeq⟩
                rcases he2 with hfree6 | hrkSeq
                · exact Or.inl hfree6
                · refine Or.inr (h2k463_seqEnv_mono (fun _ hrk => hrk) (fun _ he3 => ?_) hrkSeq)
                  rcases he3 with hfree7 | ⟨hrkOk, hintoSeq⟩
                  · exact Or.inl hfree7
                  · exact Or.inr ⟨hrkOk,
                      h2k463_seqEnv_mono (fun evsI hi => hIntoPb_sub xSInto evsI hIntoG hi)
                        (fun _ ht => ht) hintoSeq⟩

private theorem h2k463_spqrRecv_topStateGuarded_seam_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hDecPre_sub : ∀ g evs, TopStateTight W.C.F W.Q.K g.st.bytes →
      DecodePreEnv g evs → tlb_DecodeStateTightEnvOf 109 evs)
    (hDecPost_sub : ∀ g evs, TopStateTight W.C.F W.Q.K g.st.bytes →
      DecodePostEnv g evs → tlb_DecodeStateTightEnvOf 109 evs)
    (hFromPb_sub : ∀ pb evs, h2k463_FromPbStateGuard W.C.F pb →
      FromPbEnv pb evs → StatesFromPbTightEnv evs)
    (hIntoPb_sub : ∀ (g : StatesIntoPbGhost W.C.F) evs, h2k463_IntoPbStateGuard g.st →
      IntoPbEnv g evs → StatesIntoPbTightEnv evs)
    (hRecvC : SpqrRecvPlacedContractsOfEnv H_inner A lim W.C.F W.Q.K
      DecodePreEnv DecodePostEnv
      (InitInnerEnv W.C.F)
      FromPbEnv
      (fun g => h2k463_StatesRecvExactPairTightEnv W.Q.K g.self g.msg)
      IntoPbEnv
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXTOfEnv M A lim (spqrV1Recv W.C.F W.Q.K)
          (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes))) := by
  refine spqrRecvPlacedInnerSpecXTOfEnv_of_placedSpecXT
    (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv
      (fun (st msg : VecArg) => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (trTrapExternsPlaced_isPanic mmpl gh W)
      hRecvC
      (fun st _ _ _ _ _ =>
        spqrRecvTightLinkedEnv_nil_exists W.C.F W.Q.K
          (fun _ => tlb_DecodeStateTightEnvOf 109)
          (fun _ => StatesFromPbTightEnv)
          (fun _ => StatesIntoPbTightEnv)
          (StatesRecvProtoEnv' W.Q.K)
          st.bytes)
      (fun st msg s0 st_cost _ _ _ _ hfit => ?_))
  by_cases hTop : TopStateTight W.C.F W.Q.K st.bytes
  · refine spqrRecvBranchHyps_tightLinked
      (DecodeStateEnv' := fun _ => tlb_DecodeStateTightEnvOf 109)
      (StatesFromPbEnv' := FromPbEnv)
      (StatesIntoPbEnv' := IntoPbEnv)
      (StatesRecvEnv' := h2k463_StatesRecvExactPairTightEnv W.Q.K)
      st msg s0 st_cost
      (fun evs hpre => hDecPre_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpre)
      (fun evs hpost => hDecPost_sub ⟨st, s0.sp - 3056#64⟩ evs hTop hpost)
      (fun _ _ h => h)
      (fun _ _ _ h => h)
      (fun _ _ h => h)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =>
        FitsEnv.mono
          (fun evs hevs _ =>
            ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
              h2k463_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
                hFromPb_sub hIntoPb_sub hTop hevs⟩)
          hfit)
      (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs _ =>
        ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
          h2k463_spqrRecvTightLinkedEnv_imp_c07c09aOf109_of_topStateTight
            hFromPb_sub hIntoPb_sub hTop hevs⟩)
  · exact False.elim
      (h2k463_not_fitsEnv_top (FitsEnv.mono (fun _ _ h => False.elim (hTop h)) hfit))

private theorem h2k463_hookSat_withAllocVmPreserved_memmove_of_zero
    {H : String → Option (State → State)} {sym : String} (hookStack : Nat)
    (h : HookSat H sym (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    HookSat H sym (withAllocVmPreserved (sessionMemmoveSpec hookStack)) := by
  refine ProofLib.HookSat.mono h fun ⟨base, buf, dst, src, len⟩ R s0 hpre =>
    ⟨(base, buf, dst, src, len), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withAllocVmPreserved, sessionMemmoveSpec, libcMemmoveSpec, stackAt] at hpre ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp]
    ac_nf at hpre ⊢
  · dsimp only [withAllocVmPreserved, sessionMemmoveSpec, stackAt] at hpost ⊢
    simp only [ProofLib.memRegion_zero, sepConj_emp] at hpost
    ac_nf at hpost ⊢

private theorem h2k463_statesRecv_recv_exactTight_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvPlacedSpecOfEnv M A lim W.C.F W.Q.K
          (fun g => h2k463_StatesRecvExactPairTightEnv W.Q.K g.self g.msg))) := by
  let ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hExt := w4s2_trTrap_hExt mmpl gh W
  have hExt_wp := h2k463_hExt_withPanics mmpl gh W hExt
  have hmemset_wp :=
    hookSat_of_eq (hExt_wp "memset" (by decide))
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA.toCliGhostAllocHooks)
  letI : HkdfPlacedHooksExactBudgetSat W.C.F (Rust.withPanics ext) :=
    { memset := hmemset_wp
      memcpy := hookSatExactMemcpy_of_sym_eq (hExt_wp "memcpy" (by decide))
        (cliExternsPlaced_exactMemcpy_sat mmpl gh W hA.toCliGhostAllocHooks)
      compress256 := (hExt_wp _ (by decide)).trans
        (h2k463_cliGhost_row_aux mmpl gh W (compress256_row_placed mmpl W)) }
  have hC := statesRecvPlacedContracts_of_ro_leaves_sat
    (cliRecvCt2PlacedAllocExt mmpl gh W hA hExt)
    (h2k463_hookSat_withAllocVmPreserved_memmove_of_zero growOneStack
      (hookSat_of_eq (hExt_wp _ (by decide))
        (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W)))
    hmemset_wp
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemValidatePk_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemEncaps2_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemDecaps_budget_sat mmpl W)))
    (hookSat_of_eq (hExt_wp _ (by decide)) hHmac)
  have h332 := states_recv_placed_ok_x_exactTight A lim W.C.F W.Q.K ext hC
  have h0 :=
    LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
      (callerProg := spqrRecvPlacedProg ext) (i := 329) h332
  exact subroutine_ok_mono h0
    (fun (g, stB) _ _ hpre => by
      dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
        at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
      exact Entails.pure_mono fun ⟨h1, h2, h3, h4, hfit, hlr⟩ =>
        ⟨h1, h2, h3, h4, hfit.mono (fun evs hevs => ⟨g.outA, g.selfA, g.msgA, hevs⟩), hlr⟩)
    (fun (g, stB) _ _ _ hpost => by
      dsimp only [withLsCodeRoLoaded, statesRecvPlacedSpecOfEnv,
        LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget.statesRecvPlacedSpecOfEnv]
        at hpost ⊢
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left (Entails.sepExists_mono fun evs => ?_)
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, hevs⟩ =>
        ⟨h1, ⟨g.outA, g.selfA, g.msgA, hevs⟩⟩)
    (fun _ _ _ _ hp => hp)

private theorem h2k463_decodeStateCalleeContractsClPlacedX_cliExt [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    DecodeStateCalleeContractsClPlacedX canonicalV1InnerHeap A lim ext := by
  have hExt_wp := h2k463_hExt_withPanics mmpl gh W hExt
  exact mkDecodeStateCalleeContractsClPlacedX_of_blocks
    (cliDeallocBudget_at_block mmpl gh W hA hExt_wp (i := 325))
    (fun stk _ _ => cliLibcMemcpyBudget_at_block mmpl gh W hA hExt_wp stk (i := 325))
    (fun stk _ _ => cliSessionMemcpyBudget_at_block mmpl gh W hA hExt_wp stk (i := 325))
    (cliFrom_261_cl mmpl gh W hA hExt)
    (decodeErrorPush_of_merge (cliPushMerge_257_cl mmpl gh W hA hExt))
    (cliVarint_291_cl mmpl gh W hA hExt)
    (cliSkipBudget_263_cl mmpl gh W hA hExt)
    (chainParamsMerge_decodeState_of_prost (cliChainParams_294_cl mmpl gh W hA hExt))
    (cliGrowOne_356_cl mmpl gh W hA hExt)
    (cliDrop_267_cl mmpl gh W hA hExt)
    (cliDrop_270_cl mmpl gh W hA hExt)
    (cliBytesExact_290_cro mmpl gh W hA hExt)
    (epochDirectionMerge_decodeState_of_prost (cliEpochDir_299_cl mmpl gh W hA hExt))
    (cliV1StateMerge_closed_cl mmpl gh W hA hExt)

private theorem h2k463_decodeState_recv_tight109_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hV1Merge : tlb_V1StateMergeBlk325TightOkOf A lim 80
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
  let ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hc := h2k463_decodeStateCalleeContractsClPlacedX_cliExt mmpl gh W hA
    (w4s2_trTrap_hExt mmpl gh W)
  have hEpochDir := e2ar_epochDirectionMerge_blk325_cl_ok_tight hc
  have hDec325 := e2a_decodeState_cl_placed_ok_of_v1Merge_109
    (F := W.C.F) (K := W.Q.K) hc hEpochDir hV1Merge
  have hblk325 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 325 (Rust.withPanics ext))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
          (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := by
    have h0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        (blkPl_325).base
        (withLsCodeRoLoaded lsmpl
          (spqrDecodeStatePlacedSpecOfEnv canonicalV1InnerHeap A lim
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
            (tlb_DecodeStateGuardedEnv W.C.F W.Q.K))) := hDec325
    rwa [IsLsBlockProg.eq_blockProgram
          (prog := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)),
        ls_blockPlacement_base (i := 325)] at h0
  exact LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget.ls_subroutine_ok_of_blockProgram_cro
    (callerProg := spqrRecvPlacedProg ext) (i := 329) hblk325

/-- `{M : AllocCostModel} {A : RustCliAllocBudget M}`-generic `SpqrV1PlacedSeamsOfEnv`
discharger at `w4s2_SpqrRecvTopStateGuardedBytesEnv`. -/
theorem h2k463_spqrSeams_topStateGuarded_of_hmac [LibsignalPlacement]
    (mmpl : MultiPlacement) (ghFixed : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hGSpqr : CliGhostSpqrAllocHooks M A lim ghFixed)
    (hHmac : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrV1PlacedSeamsOfEnv M A lim mmpl ghFixed W
      (InitialStateEnv W.C.F)
      (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K) := by
  have hBase := gu2b_spqrV1PlacedSeams_exactFromPb_of_hmac mmpl ghFixed W hGSpqr hHmac
  have hRecvBase := cliSpqrRecvPlacedContracts_exact mmpl ghFixed W hGSpqr hHmac
  have hV1Merge :=
    v1StateMergeBlk325_cli_of_hExt mmpl ghFixed W
      (w4s2_trTrap_hExt mmpl ghFixed W) hGSpqr.toCliGhostAllocHooks
  have hDec := h2k463_decodeState_recv_tight109_ok mmpl ghFixed W hGSpqr.toCliGhostAllocHooks hV1Merge
  have hFromPb := gu2b_cliSpqrRecv_statesFromPb_fromPbGuard_ok mmpl ghFixed W hGSpqr
  have hRecv := h2k463_statesRecv_recv_exactTight_ok mmpl ghFixed W hGSpqr hHmac
  exact
    { spqrInitialState := hBase.spqrInitialState
      spqrRecv := h2k463_spqrRecv_topStateGuarded_seam_of_contracts mmpl ghFixed W
        (DecodePreEnv := tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (DecodePostEnv := tlb_DecodeStateGuardedEnv W.C.F W.Q.K)
        (FromPbEnv := gu2b_StatesFromPbGuardedEnv W.C.F)
        (IntoPbEnv := StatesIntoPbExactEnv)
        (fun _ _ hTop h => tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight hTop h)
        (fun _ _ hTop h => tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight hTop h)
        (fun _ _ hG hf => hf hG)
        (fun _ _ hG hEnv =>
          statesIntoPbExactEnv_tight (statesIntoPbTightDom_of_bokTight hG.1) hEnv)
        { dealloc_ok := hRecvBase.dealloc_ok
          memcpy_ok := hRecvBase.memcpy_ok
          dropEpochSlice_ok := hRecvBase.dropEpochSlice_ok
          dropOptProtoInnerState_ok := hRecvBase.dropOptProtoInnerState_ok
          dropOptProtoChain_ok := hRecvBase.dropOptProtoChain_ok
          dropChain_ok := hRecvBase.dropChain_ok
          dropPqRatchetState_ok := hRecvBase.dropPqRatchetState_ok
          dropStates_ok := hRecvBase.dropStates_ok
          decodeState_ok := hDec
          initInner_ok := hRecvBase.initInner_ok
          chainFrom_ok := hRecvBase.chainFrom_ok
          chainFromPb_ok := hRecvBase.chainFromPb_ok
          chainNew_ok := hRecvBase.chainNew_ok
          chainAddEpoch_ok := hRecvBase.chainAddEpoch_ok
          chainRecvKey_ok := hRecvBase.chainRecvKey_ok
          chainIntoPb_ok := hRecvBase.chainIntoPb_ok
          messageDeserialize_ok := hRecvBase.messageDeserialize_ok
          statesFromPb_ok := hFromPb
          statesRecv_ok := hRecv
          statesIntoPb_ok := hRecvBase.statesIntoPb_ok
          encodeToVec_ok := hRecvBase.encodeToVec_ok
          h_inner_eq := hRecvBase.h_inner_eq }
      spqrSendCoins := hBase.spqrSendCoins }

/-- Concrete `withFds (fineHookRustCliAllocBudget ...)` `SpqrV1PlacedSeamsOfEnv` discharger at
`w4s2_SpqrRecvTopStateGuardedBytesEnv`. -/
theorem h2k463_spqrSeams_topStateGuarded_withFds [LibsignalPlacement]
    (mmpl : MultiPlacement) (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (W : CliHooks) (γ : GhostName) (tp brkStart : BitVec 64)
    {lim : BudgetLimits} (henf : lim.enforced = true)
    (hGSpqrWithFds : CliGhostSpqrAllocHooks fineCostModel
      (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim ghFixed) :
    SpqrV1PlacedSeamsOfEnv fineCostModel
      (withFds (fineHookRustCliAllocBudget γ mmpl tp brkStart)) lim mmpl ghFixed W
      (InitialStateEnv W.C.F)
      (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
      (gu2b_SpqrSendCoinsExactFromPbLinkedEnv W.C.F W.Q.K) :=
  h2k463_spqrSeams_topStateGuarded_of_hmac mmpl ghFixed W hGSpqrWithFds
    (cliGhostExterns_libcruxHmac_withFds_hookSat γ mmpl tp brkStart henf ghFixed W hPl_mng)

end SpqrTopStateGuarded

/-- Closes `h2ki_W2DecryptSignalSlot463OkK w` at `w.ghFixed = h2k_ghFixedK mpl mmpl`. -/
theorem h2k463_w2DecryptSignalSlot463OkK_of_ghFixed
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hgh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      w.ghFixed = h2k_ghFixedK mpl mmpl) :
    h2ki_W2DecryptSignalSlot463OkK w := by
  intro h547 X W γ tp
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hgh' : w.ghFixed = h2k_ghFixedK mpl mmpl := hgh
  change h2ki_DecryptSignalSlot463OkAtPreFd
      (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits X W
  rw [hgh']
  exact h2k463_decryptSignalSlot463OkAtPreFd hLs (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    (h2k_ghFixedK mpl mmpl) w.hPl_mng X W γ tp
    (h2kb_hole2_hG mpl mmpl hLs hMm γ tp)
    (h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp).allocFs
    (h2k_hole2_hReadSatK_withFds mpl mmpl hLs hMm W γ tp)
    (h2kb_runHooksPlaced_withFds mpl mmpl hLs hMm W γ tp)
    (h2k463_spqrSeams_topStateGuarded_withFds mmpl (h2k_ghFixedK mpl mmpl) w.hPl_mng W γ tp
      cliElfImage.brkStart rfl (h2kb_hole2_hGSpqr_withFds mpl mmpl hLs hMm γ tp))
    h547

/-- Unconditional `h2ki_W2DecryptSignalSlot463OkK` closer at
`mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2`. -/
theorem h2k463_w2DecryptSignalSlot463OkK_mkWitness
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2ki_W2DecryptSignalSlot463OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k463_w2DecryptSignalSlot463OkK_of_ghFixed
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) hLs hMm rfl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463
