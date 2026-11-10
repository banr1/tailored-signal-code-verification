/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Spine-C Slot `520` (`decryptPrekey`, D3 `PathB`) Closure at `h2k_ghFixedK` (`ElfSlicesPqOomH2KSlot520PathB`)

**Checked by Lean.**

Discharges the unguarded and guarded D3 `PathB` Slot-`520` (`decryptPrekey`) interfaces matching
`ElfSlicesPqOomH2KD3JoinPathB.h2kd3_W4PathB{,Guarded}Slot520Ok{At,K}` via
`D3MatchingPathBPollPlacedBudgetFd.decPkPathBSlotOk_gvSeqFree_frozen_placedBudget_preFd` at
`AllocWithFds.withFds`, `ElfSlicesPqOomH2KSlot463` seam helpers, and
`D3MatchingPathBKitsPlacedBudgetFd.slotOk_preFd_guarded_of_unguarded`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520PathB

open Arm64 (GhostName HookOk HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open CryptoVerification (
  LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns lsmpl
)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives aesDecHookMallocng)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliRunBudgets cliRunBudgets_placed cliRunNeeds cliWrOk
)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliPollSessKitPlaced dpPollProgPlaced loadRec_scopeKit_eq
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer encodeInjOn_deserializeScopeP_Q loadRec scopeIn scopeKit
)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (aesDecBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR (
  DecPkD3MatchingPathBGvEnv DecPkD3MatchingPathBGvSeqFreeOfReadEnv MatchingPathBGvMainEnv
  MatchingPathBGvPollEnv decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0'
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf (TryDecryptCliLinkedEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0 (
  realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'
)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (
  DecPkOkPathB pathB_scopeIn_and_match_of_decPkOkPathB
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBKitsPlacedBudgetFd (
  slotOk_preFd_guarded_of_unguarded
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3MatchingPathBPollPlacedBudgetFd (
  decPkPathBSlotOk_gvSeqFree_frozen_placedBudget_preFd
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue (
  cli_tryDecrypt_of_tdEnv_at_518
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2 (
  h9r2_honestD3RunSlotEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  ReadFileRuleEnvFixed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  cliGhostAllocHooks_withFds fineAesDec_budget_withFds_hookOk withFds
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3Env StageP3ErrEnv StageP3OkPrefixEnv pollTryDecryptPlacedSpecTPTight
  stageP3TryDecryptEnvArgs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsFsPlaced dirGetSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (
  sessDeserialize_cli_dcan_placed_ok
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm (h2asm_Branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges (
  h2kb_hole2_hG h2kb_hole2_runHooksPlaced
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdThreadKit (
  h2k_hole2_hReadSatK_withFds
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (
  h2k_ghFixedK h2k_readFileSpecK
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot463 (
  h2k463_dirGet_withFds_ok h2k463_spqrSeams_topStateGuarded_withFds
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KStrCloneFds (
  h2kb_hole2_hGSpqr_withFds h2kb_runHooksPlaced_withFds
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness (
  F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut (
  cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact libsignalFullPlacementOf
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst (
  hole2_hblk hole2_hext_nodup
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2 (
  w4s2_SpqrRecvTopStateGuardedBytesEnv w4s2_TryDecryptTopStateGuardedEnv
  w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top
)
open VerifiedLibraries (mallocngLib)

/-! ## Spine-C D3 `PathB` Slot-`520` Interfaces -/

/-- D3 `RunSlotEnvs` bundle for `pathB` at `realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'`. -/
noncomputable abbrev h2k520pb_pathBSlotEnvs [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    RunSlotEnvs :=
  h9r2_honestD3RunSlotEnvs
    (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    W A cliRunBudgets (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W)

/-- Explicit-argument Slot-`520` (`decryptPrekey`, D3 `pathB` unguarded) pre-only
`FdsGe3Closed` interface. -/
def h2k520pb_W4PathBSlot520OkAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let sEnvs := h2k520pb_pathBSlotEnvs A X W
    let DecPkEnv₀ := DecPkD3MatchingPathBGvSeqFreeOfReadEnv A.repAlloc W cliRunBudgets_placed
      (ReadFileRuleEnvFixed cliIo.rd) (w4s2_TryDecryptTopStateGuardedEnv W)
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits { sEnvs with decryptPrekey := DecPkEnv₀ }
        (cliRunSemPathB X W) needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

abbrev h2k520pb_W4PathBSlot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2k520pb_W4PathBSlot520OkAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-- Explicit-argument Slot-`520` (`decryptPrekey`, D3 `pathB` guarded) pre-only `FdsGe3Closed`
interface. -/
def h2k520pb_W4PathBGuardedSlot520OkAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let sEnvs := h2k520pb_pathBSlotEnvs A X W
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
        (cliRunSemPathB X W) needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

abbrev h2k520pb_W4PathBGuardedSlot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2k520pb_W4PathBGuardedSlot520OkAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-! ## `TopStateTight` Collapse on `DecPkD3MatchingPathBGvSeqFreeOfReadEnv` -/

private theorem h2k520pb_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs :=
  h.elim (fun ha => Or.inl (h1 evs ha))
    (fun ⟨e1, e2, heq, ha, hb⟩ => Or.inr ⟨e1, e2, heq, h1 e1 ha, h2 e2 hb⟩)

theorem h2k520pb_gvSeqFree_sub_cmkDom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : DecPkGhost} {evs : List AllocEvent}
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hevs : DecPkD3MatchingPathBGvSeqFreeOfReadEnv A W cliRunBudgets_placed
      (ReadFileRuleEnvFixed cliIo.rd) (w4s2_TryDecryptTopStateGuardedEnv W) g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' X W g evs := by
  have hevs109 :
      DecPkD3MatchingPathBGvSeqFreeOfReadEnv A W cliRunBudgets_placed
        (ReadFileRuleEnvFixed cliIo.rd) (TryDecryptCliLinkedEnvOf 109 W.C W.Q.K) g evs := by
    unfold DecPkD3MatchingPathBGvSeqFreeOfReadEnv DecPkD3MatchingPathBGvEnv
      MatchingPathBGvPollEnv at hevs ⊢
    dsimp only at hevs ⊢
    split at hevs
    · next htr =>
      simp only [htr, ↓reduceIte]
      exact hevs
    · next htr =>
      simp only [htr, ↓reduceIte]
      refine h2k520pb_seqEnv_mono (fun _ h => h) ?_ hevs
      rintro evs234 ⟨r, sess, hload_rel, hcur, hmain⟩
      have hload_rel' := hload_rel
      dsimp only [cliPollSessKitPlaced] at hload_rel'
      obtain ⟨hloadS, _, _, _, _, _, _⟩ :=
        pathB_scopeIn_and_match_of_decPkOkPathB encodeInjOn_deserializeScopeP_Q (fun _ h => h)
          hfPeer hdecOk hload_rel' hcur
      have hloadK : loadRec scopeKit g.F g.peer.val = .ok (some ⟨some sess⟩) :=
        (loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hfPeer).trans hloadS
      have hTop : TopStateTight W.C.F W.Q.K sess.state.pqRatchetState := by
        unfold PeerSpqrStateTight640 at hTight
        rw [hloadK] at hTight
        exact hTight sess rfl
      refine ⟨r, sess, hload_rel, hcur, ?_⟩
      unfold MatchingPathBGvMainEnv at hmain ⊢
      rcases hmain with hP2 | ⟨hrem, recG, hex, hgv, hseq⟩
      · exact Or.inl hP2
      · refine Or.inr ⟨hrem, recG, hex, hgv, h2k520pb_seqEnv_mono (fun _ h => h) ?_ hseq⟩
        rintro evs34 (hP3 | ⟨hver, G₁, G', pt, hcl, haft, hmod, hok⟩)
        · refine Or.inl ?_
          unfold StageP3Env at hP3 ⊢
          split at hP3
          · next hv =>
            simp only [hv, ↓reduceIte]
            rcases hP3 with ⟨G₁, hcl, herr⟩
            refine ⟨G₁, hcl, ?_⟩
            unfold StageP3ErrEnv at herr ⊢
            rw [← w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W
              (stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins)
              hTop]
            exact herr
          · next hv =>
            simp only [hv, ↓reduceIte]
            exact hP3
        · refine Or.inr ⟨hver, G₁, G', pt, hcl, haft, hmod, h2k520pb_seqEnv_mono ?_ (fun _ h => h) hok⟩
          intro evsP3 hpfx
          unfold StageP3OkPrefixEnv at hpfx ⊢
          rw [← w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W
            (stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins)
            hTop]
          exact hpfx
  exact decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0' A X W cliRunBudgets_placed
    (fun _ _ h => h) hfPeer hdecOk hTight hevs109

/-! ## Slot-`520` `PathB` Unguarded and Guarded Closers -/

/-- Explicit-seam D3 `PathB` Slot-`520` unguarded closer (`h2k520pb_W4PathBSlot520OkAt`). -/
theorem h2k520pb_w4PathBSlot520OkAt_of_seams
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    {InitEnv : CliHooks → InitialStateGhost → List AllocEvent → Prop}
    {SendEnv : CliHooks → SendCall → List AllocEvent → Prop}
    (hG :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostAllocHooks fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hAllocFs :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        AllocContractsFsPlaced
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hReadSatFd :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
          (withFdsGe3Closed
            (h2k_readFileSpecK cliIo.rd cliWrOk
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
              cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))))
    (hhWithFds :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (hSpqrWithFds :
      ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
          fineCostModel
          (withFds (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
          cliBudgetLimits mmpl ghFixed W (InitEnv W)
          (fun st msg => w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K st.bytes msg.bytes)
          (SendEnv W)) :
    h2k520pb_W4PathBSlot520OkAt (mmpl := mmpl) hblk hext_nodup ghFixed := by
  intro h547 X W γ tp
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  let sEnvs := h2k520pb_pathBSlotEnvs A X W
  let DecPkEnv₀ := DecPkD3MatchingPathBGvSeqFreeOfReadEnv A.repAlloc W cliRunBudgets_placed
    (ReadFileRuleEnvFixed cliIo.rd) (w4s2_TryDecryptTopStateGuardedEnv W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hGWf : CliGhostAllocHooks fineCostModel (withFds A) cliBudgetLimits ghFixed :=
    cliGhostAllocHooks_withFds (hG γ tp)
  have hhP := hhWithFds W γ tp
  have hhClosureWf :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        (withFds A) cliBudgetLimits H :=
    { alloc := hhP.alloc, allocFs := hhP.allocFs, panics := hhP.panics,
      memcpyRO := hhP.memcpyRO, bcmp := hhP.bcmp, fs := hhP.fs,
      utf8 := hhP.utf8, memrchr := hhP.memrchr, codecHooks := hhP.codecHooks,
      allocZeroed := hhP.allocZeroed, stringClone := hhP.stringClone,
      formatInner := hhP.formatInner }
  have hGetPool :
      subroutine_ok (lsProg_589 H) (lsmpl.base 589)
        (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) cliBudgetLimits
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          cliRunBudgets_placed.dirGetNeed) :=
    h2k463_dirGet_withFds_ok rfl hLs (hAllocFs W γ tp) hhP (hReadSatFd W γ tp)
  have hDeserPool :
      subroutine_ok (dpPollProgPlaced H) (lsmpl.base 46)
        (sessDeserializeSpecPlaced scopeKit (withFds A) cliBudgetLimits
          SessDeserializeCancelEnv) :=
    ls_transfer_lscro (callerProg := dpPollProgPlaced H)
      (sessDeserialize_cli_dcan_placed_ok mmpl ghFixed W hGWf (fun _ hr => hr))
  have hAesDecPool :
      HookOk (aesDecHookMallocng mmpl W.C.D)
        (aesDecBudgetSpec W.C.D fineCostModel (withFds A) cliBudgetLimits) :=
    fineAesDec_budget_withFds_hookOk γ tp cliElfImage.brkStart cliBudgetLimits hPl_mng W.C.D
  have hTryDecPool :
      subroutine_ok (dpPollProgPlaced H) (lsmpl.base 508)
        (withLsCodeRoLoaded lsmpl
          (pollTryDecryptPlacedSpecTPTight W.C (withFds A) cliBudgetLimits 0#64 uuidTryParse
            (spqrV1 W.C.F W.Q.K) (w4s2_TryDecryptTopStateGuardedEnv W))) :=
    cli_tryDecrypt_of_tdEnv_at_518 (tdEnv := w4s2_TryDecryptTopStateGuardedEnv)
      mmpl ghFixed W 0#64 hGWf hAesDecPool (hSpqrWithFds W γ tp)
      (w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty W.C.F W.Q.K)
      (fun _ _ h => h)
  exact decPkPathBSlotOk_gvSeqFree_frozen_placedBudget_preFd (A := A) (lim := cliBudgetLimits)
    rfl X mmpl ghFixed W hGWf h547 hhClosureWf hGetPool hDeserPool hTryDecPool
    (cliRunSemPathB X W) { sEnvs with decryptPrekey := DecPkEnv₀ } needs
    (fun _ _ h => h) rfl rfl
    (fun _ _ _ _ hd => ⟨hd.party, hd.loadedMatch, hd.keyPairLt, hd.preKeysWf, hd.baseKeysLt⟩)
    rfl

/-- Guarded upgrade from `h2k520pb_W4PathBSlot520OkAt` to `h2k520pb_W4PathBGuardedSlot520OkAt`. -/
theorem h2k520pb_w4PathBGuardedSlot520OkAt_of_unguarded
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hSlot0 : h2k520pb_W4PathBSlot520OkAt (mmpl := mmpl) hblk hext_nodup ghFixed) :
    h2k520pb_W4PathBGuardedSlot520OkAt (mmpl := mmpl) hblk hext_nodup ghFixed := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  intro h547 X W γ tp
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  exact slotOk_preFd_guarded_of_unguarded rfl (hSlot0 h547 X W γ tp)
    (fun x evs hfPeer hdecOk hTight hevs0 =>
      h2k520pb_gvSeqFree_sub_cmkDom0' A.repAlloc X W hfPeer hdecOk hTight hevs0)

/-- Closes `h2k520pb_W4PathBSlot520OkK w` (unguarded) at `w.ghFixed = h2k_ghFixedK mpl mmpl`. -/
theorem h2k520pb_w4PathBSlot520OkK_of_ghFixed
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hgh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      w.ghFixed = h2k_ghFixedK mpl mmpl) :
    h2k520pb_W4PathBSlot520OkK w := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hgh' : w.ghFixed = h2k_ghFixedK mpl mmpl := hgh
  change h2k520pb_W4PathBSlot520OkAt (mmpl := mmpl) (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) w.ghFixed
  rw [hgh']
  exact h2k520pb_w4PathBSlot520OkAt_of_seams hLs (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    (h2k_ghFixedK mpl mmpl) w.hPl_mng
    (fun γ tp => h2kb_hole2_hG mpl mmpl hLs hMm γ tp)
    (fun W γ tp => (h2kb_hole2_runHooksPlaced mpl mmpl hLs hMm W γ tp).allocFs)
    (fun W γ tp => h2k_hole2_hReadSatK_withFds mpl mmpl hLs hMm W γ tp)
    (fun W γ tp => h2kb_runHooksPlaced_withFds mpl mmpl hLs hMm W γ tp)
    (fun W γ tp =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2k463_spqrSeams_topStateGuarded_withFds mmpl (h2k_ghFixedK mpl mmpl) w.hPl_mng W γ tp
        cliElfImage.brkStart rfl (h2kb_hole2_hGSpqr_withFds mpl mmpl hLs hMm γ tp))

/-- Closes `h2k520pb_W4PathBGuardedSlot520OkK w` (guarded) at `w.ghFixed = h2k_ghFixedK mpl mmpl`. -/
theorem h2k520pb_w4PathBGuardedSlot520OkK_of_ghFixed
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hgh :
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      w.ghFixed = h2k_ghFixedK mpl mmpl) :
    h2k520pb_W4PathBGuardedSlot520OkK w :=
  h2k520pb_w4PathBGuardedSlot520OkAt_of_unguarded w.hblk w.hext_nodup w.ghFixed
    (h2k520pb_w4PathBSlot520OkK_of_ghFixed w hLs hMm hgh)

/-- Unconditional `h2k520pb_W4PathBSlot520OkK` closer at
`mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2`. -/
theorem h2k520pb_w4PathBSlot520OkK_mkWitness
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2k520pb_W4PathBSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k520pb_w4PathBSlot520OkK_of_ghFixed
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) hLs hMm rfl

/-- Unconditional `h2k520pb_W4PathBGuardedSlot520OkK` closer at
`mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2`. -/
theorem h2k520pb_w4PathBGuardedSlot520OkK_mkWitness
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    h2k520pb_W4PathBGuardedSlot520OkK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) :=
  h2k520pb_w4PathBGuardedSlot520OkK_of_ghFixed
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2) hLs hMm rfl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520PathB
