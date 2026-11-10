/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverBPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverRegErrPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathsPlacedBudgetFd
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded D2(c) Slot-`520` Producer

Defines guard-aware slot-envelope inclusion (`GuardSlotIncl`), `DecPkD2cSlotOkFrozenPlacedAtPreFd`,
and the kit-parametric Block-`520` producers `decPk_d2c_canon_slotOk_frozen_of_kits` and
`decPk_d2c_canon_slot520_preFd_of_kits` from `CanonPollKitsPlacedOk`.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPlacedBudgetFd

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonKitsPlacedBudgetFd (
  CanonPollKitsPlacedOk slotOk_decPkFrozenPlaced_withFds_to_preFd
)

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  lsProg_51 lsmpl withLsCl
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (OverPrevEncOK clearPending)
open CryptoVerification.E2E (
  UnreachedPqxdhPrimitives aesDecHookMallocng modelPrims
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost SignalMessageGhost)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunNeeds RunSem dpPollNeed)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  DecPkOkD2c cliDecryptPrekeyNeed decPkDefD2c dpCxAt dpFutStartAt dpWrapFrame
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk dpPollEntryPlaced dpPollProgPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ scopeIn scopeKit
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv aesDecBudgetSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget (
  OverVerNe1e04CliAtFrozenPlacedBody
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlacedBudget (TryDecryptCliEnvOf)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase (
  DecPkD2cSlotOkFrozenPlaced cliDecryptPrekey_ok_state_frozen_placed_at_block
  dpSlot_ok_state_of_codeOk_placed slotsOfDecPkPlacedOf
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAuxBudget (EncodeRawPreallocPlacedOkX)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (withFds)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPollPathsPlacedBudgetFd (
  poll_d2c_canon_gvSeqFree_frozen_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2OverBPlacedBudgetFd (
  StageP2OverQpanCliMemInvPlacedAtXBStmt StageP2OverQpanCliRegErrPlacedAtBStmt
  stageP2Over_qpan_cli_archive_frozen_at_B_of_init75_and_kits
  stageP2Over_qpan_cli_archive_regErr_frozen_at_B_of_init75_and_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage2PathAPlacedBudgetFd (
  StageP2PathAQpanCliNoReadFrozenPlacedAtStmt
  stageP2PathA_qpan_cli_noRead_frozen_of_init75_and_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonStage3Prev1PlacedBudgetFd (
  DecPkD2cCanonPollGvSeqFreeEnv PathCP3Envs cliP2KitEnvsFixed try507_of_tdEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliP2PathAOptFieldsErrEnv cliP2PathAOptFieldsOkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget (
  dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  dpPollSpecStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  dirGetSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

/-! ## 1. Guarded Envelope `FitsEnv` Refutation & Conditional Inclusion -/

/-- No cost-model state admits `fun _ => True`, since an allocation exceeding `MallocngMaxAllocSize`
violates `AllocEvent.withinMaxAlloc`. -/
theorem not_fitsEnv_top {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    ¬ FitsEnv M lim st (fun _ => True) := by
  intro h
  have h1 := h [AllocEvent.alloc (MallocngMaxAllocSize + 1)] trivial
  have h2 : (AllocEvent.alloc (MallocngMaxAllocSize + 1)).withinMaxAlloc := h1.1.1
  dsimp only [AllocEvent.withinMaxAlloc] at h2
  omega

/-- Guard-aware inclusion condition from an inner poll envelope `PollEnv` into a target slot
envelope `SlotEnv` under `FilesOkPeer`, `DecPkOkD2c`, and `FitsEnv M lim st (SlotEnv g)` (`rfl`-equal
to `Hole3W4DecPkFresh.W4fGuardSlotIncl`). -/
def GuardSlotIncl {M : AllocCostModel} (lim : BudgetLimits) (W : CliHooks)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (PollEnv SlotEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (g : DecPkGhost) (st : M.σ),
    FilesOkPeer Scope g.F g.peer.val →
    DecPkOkD2c ⟨W.C, W.Q⟩ Scope g.F g.peer.val g.me.val g.msg →
    FitsEnv M lim st (SlotEnv g) →
    ∀ evs, PollEnv g evs → SlotEnv g evs

/-- Discharges `GuardSlotIncl` for any guarded slot envelope `(fun g evs => Guard g → InnerEnv g evs)`. -/
theorem guardIncl_of_guarded_sub {M : AllocCostModel} {lim : BudgetLimits} {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Guard : DecPkGhost → Prop}
    {PollEnv InnerEnv : DecPkGhost → List AllocEvent → Prop}
    (hSub : ∀ g,
      FilesOkPeer Scope g.F g.peer.val →
      DecPkOkD2c ⟨W.C, W.Q⟩ Scope g.F g.peer.val g.me.val g.msg →
      Guard g →
      ∀ evs, PollEnv g evs → InnerEnv g evs) :
    GuardSlotIncl (M := M) lim W Scope PollEnv (fun g evs => Guard g → InnerEnv g evs) := by
  intro g st hfPeer hdecOk hFits evs hPoll hGuard
  have _ : Guard g := by
    by_contra hng
    exact not_fitsEnv_top (hFits.mono fun _ _ hG => absurd hG hng)
  exact hSub g hfPeer hdecOk hGuard evs hPoll

/-! ## 2. `slotWithPreFdsGe3Closed` D2(c) Slot-`520` Contract (`rfl`-equal to `ElfSlicesPqOomH2KIfaces`) -/

/-- `slotWithPreFdsGe3Closed` D2(c) `decryptPrekey` Slot-`520` contract (`rfl`-equal to
`ElfSlicesPqOomH2KIfaces.DecPkD2cSlotOkFrozenPlacedAtPreFd`). -/
def DecPkD2cSlotOkFrozenPlacedAtPreFd [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (S : RunSem) (needs : RunNeeds) (sEnvs : RunSlotEnvs),
    sEnvs.decryptPrekey = DecPkEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.decryptPrekey = decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn →
    S.decPkOk = DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn →
    needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets →
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey).OkPlaced
      (lsProg_579 H) (lsmpl.base 520)

/-! ## 3. Kit-Parametric `{M} {A}`-Generic & `slotWithPreFdsGe3Closed` D2(c) Slot-`520` Producers -/

private theorem dpPoll_frozen_of_guardIncl [LibsignalFullPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PollEnv SlotEnv : DecPkGhost → List AllocEvent → Prop}
    {ext : LibsignalHooks}
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hIncl : GuardSlotIncl (M := M) lim W Scope PollEnv SlotEnv)
    {stk' : Nat}
    (hpoll : subroutine_ok (dpPollProgPlaced ext) dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim PollEnv B S) stk'))) :
    subroutine_ok (dpPollProgPlaced ext) dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim SlotEnv B S) stk')) := by
  refine subroutine_ok.of_codeLoaded fun y R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withLsFrozen] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcode, hpre0⟩ := hpre
  dsimp only [dpPollSpecStateBudget] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨hpure0, hsp0⟩ := hpre0
  have hinv_front :
      s0.mem ⊨ (dpSlotPollKStatePlaced A lim SlotEnv B S).inv y.g y.st s0 ∗
        (memRegion y.out 48 ∗
          dpFutStartAt y.fut ((dpSlotPollKStatePlaced A lim SlotEnv B S).args y.g) ∗
          dpCxAt y.cx ∗ stackAt s0.sp stk' ∗ R) := by
    simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hsp0
  dsimp only [dpSlotPollKStatePlaced] at hinv_front hpure0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hinv_front
  obtain ⟨⟨hF0, hfOk, hdOk, hfit⟩, hinv_rest⟩ := hinv_front
  obtain ⟨hfPeer, hdecOk⟩ := hok y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have hSub : ∀ evs, PollEnv y.g evs → SlotEnv y.g evs :=
    hIncl y.g y.st hfPeer hdecOk hfit
  have hfitPoll : FitsEnv M lim y.st (PollEnv y.g) := hfit.mono hSub
  have hinv_poll :
      s0.mem ⊨ (dpSlotPollKStatePlaced A lim PollEnv B S).inv y.g y.st s0 ∗
        (memRegion y.out 48 ∗
          dpFutStartAt y.fut ((dpSlotPollKStatePlaced A lim PollEnv B S).args y.g) ∗
          dpCxAt y.cx ∗ stackAt s0.sp stk' ∗ R) := by
    dsimp only [dpSlotPollKStatePlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF0, hfOk, hdOk, hfitPoll⟩, hinv_rest⟩
  have hpre1 :
      s0.mem ⊨
        (withLsFrozen lsmpl
          (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim PollEnv B S) stk')).pre
          ⟨y.out, y.fut, y.cx, y.g, y.st⟩ s0 ∗ R := by
    dsimp only [withLsFrozen, dpPollSpecStateBudget]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcode, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure0, by simpa only [sepConj_comm, sepConj_left_comm, sepConj_assoc] using hinv_poll⟩
  refine hpoll.mono_outcome ⟨y.out, y.fut, y.cx, y.g, y.st⟩ R s0 hpc hrun hpre1 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, hex⟩ | ⟨ho_st, ho⟩
  · refine Or.inl ⟨hret, hcc, Arm64.Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    dsimp only [withLsFrozen, dpPollSpecStateBudget, dpSlotPollKStatePlaced]
    refine sepConj_mono_left (Entails.sepExists_mono fun ws => ?_)
    refine sepConj_mono_right (sepConj_mono_right ?_)
    refine Entails.sepExists_mono fun evs =>
      Entails.sepExists_mono fun g' =>
      Entails.sepExists_mono fun e => ?_
    refine Entails.pure_left fun hm => ?_
    rw [ProofLib.pure_sepConj_of_true ⟨hSub evs hm.1, hm.2⟩]
    exact Entails.refl _
  · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-- Kit-parametric `{M} (A : RustCliAllocBudget M)`-generic Block-`520` producer: proves
`DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim SlotEnv` from `CanonPollKitsPlacedOk`, Block-`589`
`dirGet`, Block-`46` `sessDeserialize`, SPQR seams, and `GuardSlotIncl` from
`DecPkD2cCanonPollGvSeqFreeEnv` (with no `lsReadFileSym` hypotheses). -/
theorem decPk_d2c_canon_slotOk_frozen_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      UnreachedPqxdhPrimitives → DecPkGhost → SessionRecord (List (BitVec 8)) →
        List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {p3c : CliHooks → PathCP3Envs}
    {SlotEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (_hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd)
        cliRunBudgets.dirGetNeed))
    (hDeser : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hKits : CanonPollKitsPlacedOk A lim cliRunBudgets ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M A lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hPrevOk : ∀ r s_old, scopeIn r → r.currentSession = some s_old →
      s_old.state.sessionVersion = 4#32 → OverPrevEncOK (encSession (clearPending s_old)))
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody A lim OverPrevEncOK verNeDecEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hp3Err : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3VerNe : ∀ recG st enc evs,
      StageP3VerNePrev1Env verNeDecEnv recG st enc evs →
      (p3c W).verNeEnv recG st enc evs)
    (hp3Ok : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3Fits : ∀ st_b recG st rem loc msgG msg msgVer enc rest,
      FitsEnv M lim st_b
        (fun evs =>
          (∃ G₁, CloneRel recG G₁ ∧ (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs) ∨
          (p3c W).verNeEnv recG st enc evs ∨
          ∃ G₁, CloneRel recG G₁ ∧ (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs) →
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) verNeDecEnv recG st rem loc msgG msg msgVer enc rest))
    (hErrEnv : ∀ X' g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X' W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverErrEnv X' g r evs)
    (hOkEnv : ∀ X' g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X' W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverOkEnv X' g r evs)
    (hFitsSplit : ∀ X' st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv (P2OverErrEnv X') (P2OverOkEnv X') g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X' W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsFixed A.repAlloc ReadEnv))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X' W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (cliP2KitEnvsFixed A.repAlloc ReadEnv))
          g r))
    (hIncl : ∀ X',
      GuardSlotIncl (M := M) lim W scopeIn
        (DecPkD2cCanonPollGvSeqFreeEnv A.repAlloc W X' ReadEnv DeserEnv
          (P2OverErrEnv X') (P2OverOkEnv X') tdEnv p3c)
        SlotEnv) :
    DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim SlotEnv := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Arm64.Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have hcaller : IsLsBlockProg (lsProg_579 H) 579 (Arm64.Rust.withPanics H) := by
    rw [hpan]; infer_instance
  have hInit75 := hSpqr.initialStateMemInv_lsProg75
  have hTry0 := try507_of_tdEnv mmpl gh W 0#64 hG hAesDec hSpqr hRecv_ne htd
  intro X S needs sEnvs hsDec hfiles hdec hdecOk hneed
  dsimp only [slotsOfDecPkPlacedOf]
  rw [hsDec]
  have hP2A :
      StageP2PathAQpanCliNoReadFrozenPlacedAtStmt A lim X mmpl gh W cliRunBudgets
        (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv))
        (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W cliRunBudgets
          (fun F0 peer => cliPollSelfBudgetEnv A.repAlloc F0 peer (cliKitStk cliRunBudgets) ReadEnv)) :=
    stageP2PathA_qpan_cli_noRead_frozen_of_init75_and_kits A lim ReadEnv X mmpl gh W cliRunBudgets
      hDropNz hG hInit75 hKits.selfOk hKits.spkOk hKits.kpkOk hKits.pkOk
  have hP2Over_raw :
      StageP2OverQpanCliMemInvPlacedAtXBStmt
        (LibsignalFrozen lsmpl) A lim X mmpl gh W cliRunBudgets
        (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
          (cliP2KitEnvsFixed A.repAlloc ReadEnv))
        (P2OverPathCOkEnvOf (A := A.repAlloc) X W cliRunBudgets
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          PromoteOverArchiveCanonSessEnv
          (cliP2KitEnvsFixed A.repAlloc ReadEnv)) :=
    stageP2Over_qpan_cli_archive_frozen_at_B_of_init75_and_kits
      (kitEnvs := cliP2KitEnvsFixed A.repAlloc ReadEnv)
      A lim X mmpl gh W cliRunBudgets hDropNz hG hInit75 hRaw hGrow
      (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun F0 peer _ _ _ _ _ => hKits.selfOk F0 peer)
      (fun F0 _ spkId _ _ _ _ => hKits.spkOk F0 spkId)
      (fun F0 _ spkId kpkId _ kbk _ => hKits.kpkOk F0 kpkId spkId kbk)
      (fun F0 _ _ _ opkWord _ _ => hKits.pkOk F0 opkWord)
  have hP2Over_regErr :
      StageP2OverQpanCliRegErrPlacedAtBStmt
        (LibsignalFrozen lsmpl) A lim X mmpl gh W cliRunBudgets
        (P2OverPathCErrEnvOf (A := A.repAlloc) X W cliRunBudgets
          (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
          (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
          (cliP2KitEnvsFixed A.repAlloc ReadEnv)) :=
    stageP2Over_qpan_cli_archive_regErr_frozen_at_B_of_init75_and_kits
      (kitEnvs := cliP2KitEnvsFixed A.repAlloc ReadEnv)
      A lim X mmpl gh W cliRunBudgets hDropNz hG hInit75 hRaw hGrow
      (fun _ _ _ h => h) (fun _ _ _ _ h => h)
      (fun F0 peer _ _ _ _ _ => hKits.selfOk F0 peer)
      (fun F0 _ spkId _ _ _ _ => hKits.spkOk F0 spkId)
      (fun F0 _ spkId kpkId _ kbk _ => hKits.kpkOk F0 kpkId spkId kbk)
      (fun F0 _ _ _ opkWord _ _ => hKits.pkOk F0 opkWord)
  have hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer scopeIn F peer ∧ DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn F peer me pm :=
    fun _ _ _ _ hf hd => ⟨(hfiles ▸ hf).1, hdecOk ▸ hd⟩
  intro stk h1 h2
  have hstk : cliDecryptPrekeyNeed cliRunBudgets ≤ stk := hneed ▸ h1
  exact dpSlot_ok_state_of_codeOk_placed (LibsignalFrozen lsmpl) cliRunBudgets S stk hstk h2
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim SlotEnv cliRunBudgets S)
      (dpSlotPollKStatePlaced_inv_vm A lim SlotEnv cliRunBudgets S)
      (dpSlotPollKStatePlaced_res_vm A lim SlotEnv cliRunBudgets S)
      (fun stk' hs1 hs2 => by
        rw [hpan]
        exact dpPoll_frozen_of_guardIncl W cliRunBudgets S scopeIn hok (hIncl X)
          (poll_d2c_canon_gvSeqFree_frozen_of_kits A lim hDropNz mmpl gh hG W X S
            hh hDeser hKits hP2A hP2Over_raw hP2Over_regErr hTry0 hPrevOk hVerNeAt
            hp3Err hp3VerNe hp3Ok hp3Fits (hErrEnv X) (hOkEnv X) (hFitsSplit X)
            encodeInjOn_deserializeScopeP_Q hdec hok stk' hs1 hs2))
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢; omega)
      h2)

/-- Instantiates `decPk_d2c_canon_slotOk_frozen_of_kits` at `withFds A`
(`(withFds A).repAlloc = A.repAlloc`) and lifts via `slotOk_decPkFrozenPlaced_withFds_to_preFd`
to discharge `DecPkD2cSlotOkFrozenPlacedAtPreFd`. -/
theorem decPk_d2c_canon_slot520_preFd_of_kits [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (henf : lim.enforced = true)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {P2OverErrEnv P2OverOkEnv :
      UnreachedPqxdhPrimitives → DecPkGhost → SessionRecord (List (BitVec 8)) →
        List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {p3c : CliHooks → PathCP3Envs}
    {SlotEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M (withFds A) lim gh)
    (hh : RunHooksPlaced (withFds A) lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk (withFds A) lim (DirGetEnv PathEnv ReadEnv cliIo.rd)
        cliRunBudgets.dirGetNeed))
    (hDeser : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit (withFds A) lim DeserEnv))
    (hKits : CanonPollKitsPlacedOk (withFds A) lim cliRunBudgets ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRaw : EncodeRawPreallocPlacedOkX A.repAlloc (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGrow : subroutine_ok (lsProg_51 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 621) (withLsCl lsmpl (growOneVecU8BudgetSpec M (withFds A) lim)))
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M (withFds A) lim))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M (withFds A) lim mmpl gh W
      (InitialStateEnv W.C.F) (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hRecv_ne : ∀ stBs msgBs, ∃ evs, RecvBytesEnv stBs msgBs evs)
    (htd : ∀ a evs,
      TryDecryptCliEnvOf W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv RecvBytesEnv FormatInnerEnv a evs →
      tdEnv W a evs)
    (hPrevOk : ∀ r s_old, scopeIn r → r.currentSession = some s_old →
      s_old.state.sessionVersion = 4#32 → OverPrevEncOK (encSession (clearPending s_old)))
    (hVerNeAt : OverVerNe1e04CliAtFrozenPlacedBody (withFds A) lim OverPrevEncOK verNeDecEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hp3Err : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3ErrM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3VerNe : ∀ recG st enc evs,
      StageP3VerNePrev1Env verNeDecEnv recG st enc evs →
      (p3c W).verNeEnv recG st enc evs)
    (hp3Ok : ∀ recG G₁ st rem loc msgG msg rest evs,
      StageP3OkPrefixM3Env (tdEnv W) recG G₁ st rem loc msgG msg rest evs →
      (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs)
    (hp3Fits : ∀ st_b recG st rem loc msgG msg msgVer enc rest,
      FitsEnv M lim st_b
        (fun evs =>
          (∃ G₁, CloneRel recG G₁ ∧ (p3c W).errEnv recG G₁ st rem loc msgG msg rest evs) ∨
          (p3c W).verNeEnv recG st enc evs ∨
          ∃ G₁, CloneRel recG G₁ ∧ (p3c W).okPrefixEnv recG G₁ st rem loc msgG msg rest evs) →
      FitsEnv M lim st_b
        (StageP3Prev1Env (tdEnv W) verNeDecEnv recG st rem loc msgG msg msgVer enc rest))
    (hErrEnv : ∀ X' g r evs,
      P2OverPathCErrEnvOf (A := A.repAlloc) X' W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)) W.C.F)
        (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)))
        (cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverErrEnv X' g r evs)
    (hOkEnv : ∀ X' g r evs,
      P2OverPathCOkEnvOf (A := A.repAlloc) X' W cliRunBudgets
        (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)) W.C.F)
        PromoteOverArchiveCanonSessEnv (cliP2KitEnvsFixed A.repAlloc ReadEnv) g r evs →
      P2OverOkEnv X' g r evs)
    (hFitsSplit : ∀ X' st_b g r,
      FitsEnv M lim st_b (StageP2OverEnv (P2OverErrEnv X') (P2OverOkEnv X') g r) →
      FitsEnv M lim st_b
        (StageP2OverEnv
          (P2OverPathCErrEnvOf (A := A.repAlloc) X' W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)) W.C.F)
            (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)))
            (cliP2KitEnvsFixed A.repAlloc ReadEnv))
          (P2OverPathCOkEnvOf (A := A.repAlloc) X' W cliRunBudgets
            (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X' ⟨W.C, W.Q⟩)) W.C.F)
            PromoteOverArchiveCanonSessEnv (cliP2KitEnvsFixed A.repAlloc ReadEnv))
          g r))
    (hIncl : ∀ X',
      GuardSlotIncl (M := M) lim W scopeIn
        (DecPkD2cCanonPollGvSeqFreeEnv A.repAlloc W X' ReadEnv DeserEnv
          (P2OverErrEnv X') (P2OverOkEnv X') tdEnv p3c)
        SlotEnv) :
    DecPkD2cSlotOkFrozenPlacedAtPreFd (cliGhostExterns gh (cliExternsPlaced mmpl W))
      X W A lim SlotEnv := by
  intro S needs sEnvs hsEnv hfOk hdPk hdOk hneed
  exact slotOk_decPkFrozenPlaced_withFds_to_preFd henf
    (decPk_d2c_canon_slotOk_frozen_of_kits (withFds A) lim mmpl gh W hDropNz hG hh hGet hDeser
      hKits hRaw hGrow hAesDec hSpqr hRecv_ne htd hPrevOk hVerNeAt hp3Err hp3VerNe hp3Ok hp3Fits
      hErrEnv hOkEnv hFitsSplit hIncl X S needs sEnvs hsEnv hfOk hdPk hdOk hneed)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.DecPkD2cCanonPlacedBudgetFd
