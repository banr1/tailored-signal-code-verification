/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAFullPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage2PlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520VmPathA
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520VmPathB
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ValidMatchDecPkSlotSeqFree
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchAuxPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Kit-Parametric D3 `validMatch` Poll and Frozen Slot-`520` Producers (`ElfSlicesPqOomH2KSlot520VmPoll`)

**Checked by Lean.**

Assembles the Block-`518` `withLsFrozen` poll closure
`h2k520vm_decPk_d3_validMatch_seqFree_poll_frozen_kits_placedBudget` from
`CliDecPkPollKitsPlacedOk`, `StageP2PathAQpanCliD3NoReadAtFrozenPlacedBudgetStmt`,
`h2k520vm_closure_pathA_seqFree_d3_frozen_kits_placed_ok`, and
`h2k520vm_closure_pathB_seqFree_d3_frozen_kits_placed_ok`, and lifts it to the frozen Slot-`520`
producer `h2k520vm_decPkValidMatchSlotOk_seqFree_targetGuarded_of_dirGet_frozen`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520VmPoll

open scoped CryptoVerification.LibsignalTripleRatchet CryptoVerification.RustHeap
open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement LibsignalHooks
  LibsignalPlacement libsignalFrozen_of_keepsFrozen lsmpl lsρ
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  sp_sub_cd0_align_std3 stageP1CallStack stageP1ProgPlaced
)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApiRepr (preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SendCall VecArg extract_withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSignedPreKeyVtSym dirAt
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliIdentityStoreSpec cliSessionStoreSpec
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliRunBudgets cliWrOk coinsInstalledPlaced storesAt
)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost RunNeeds RunSem dpPollNeed dpSlotArgsPlaced mkSlot
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns withPanics_cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.RunProofs (
  cliDecryptPrekeyNeed decPkDef dpFutStartAt dpWrapFrame
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit StageP1PostRegs cliIdStoreSpecFull cliIdStoreSpecFullPlaced
  cliId_trustRel_eq_of_trusted cliKitStk cliPollIdKit cliPollIdKitPlaced cliPollKpkKitPlaced
  cliPollPkKitPlaced cliPollSessKit cliPollSessKitPlaced cliPollSpkKitPlaced
  cliPollStoresKitsAtPlaced cliSess_loadRel_isOk closStackUnusedP1OkAt clos_stack_3280_split_for_p1_ok
  coroUnusedP1At coroUnusedP1AtPlaced currentSession_some_of_cliPollSessPlaced_loadRel
  dpClosSubStack dpFutStartAt_split_for_p1_placed dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack
  dpPollProgPlaced pathAInitState pmKyberId pmPreKeyId preKeyMsgAt_eq_idKey_sep
  preKeyMsgRemIdKeyAt sepWPp_conseq_pre sepWPp_sepExists_left stackAt_poll_entry_split
  stackAt_subStack_split stageP1CallStack_le_subStack subStack_le_sp_of_dpPollNeed
  subroutine_ok_of_sepWPp_steps trusted_ok_of_filesOkPeer
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer encodeInjOn_deserializeScopeP_Q filesOk₀ scopeIn scopeKit
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv
)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase (
  cliDecryptPrekey_ok_state_frozen_placed_at_block
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (DecPkOkD3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PathAFullPlacedBudgetFd (
  StageP2PathAQpanCliD3NoReadAtFrozenPlacedBudgetStmt
  stageP2PathAQpan_cli_d3_full_noRead_placed_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchSlotPlacedBudget (
  CliStageP1OkEnv p1Ok_recombine_entails_stageP2_budget_d3_placed sepWPp_bind_p1_false_d3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudget (
  dpPollPre_unpack_d3_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidMatchUntrustedPlacedBudgetFd (
  closure_untrusted_d3_kits_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget (
  dpPollEntrySpatialPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget (
  storesAt_opened_entails_cliPollStoresKitsAtPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  StageP3Env pollTryDecryptPlacedSpecTPTight
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  StageP2PathAEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  cliPollStageP1_fsAt_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.DecPkPollKitsFdsPlacedBudget (
  CliDecPkPollKitsPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.DecPkPollKitsStage2PlacedBudgetFd (
  cliDecPkPollKitsPlacedOk_of_dirGet
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget (
  stageP2Matched_framed_cli_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget (
  stageP1OkPreAt stageP1_ok_placed_of_kits
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv cliPollSessSeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget (
  dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  decPkSlotSpecFrozenPlaced dpPollSpecStateBudget dpSlotPollKStatePlaced dpSlot_ok_state_frozen_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  dirGetSpecPlaced sessDeserializeSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520VmPathA (
  h2k520vm_closure_pathA_seqFree_d3_frozen_kits_placed_ok
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520VmPathB (
  h2k520vm_closure_pathB_seqFree_d3_frozen_kits_placed_ok
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ValidMatchDecPkSlotSeqFree (
  h10b_DecPkD3ValidMatchSeqFreeEnv h10b_DecPkD3ValidMatchSeqFreeOfReadEnv
  h10b_DecPkD3ValidMatchSeqFreePollEnv h10b_decPkValidMatchSlotOk_targetGuarded_frozen
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## Block-`518` `withLsFrozen` Poll Closure -/

/-- Kit-parametric Block-`518` `withLsFrozen` poll closure for D3 `validMatch`. -/
theorem h2k520vm_decPk_d3_validMatch_seqFree_poll_frozen_kits_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : StageP2PathAQpanCliD3NoReadAtFrozenPlacedBudgetStmt A lim DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hG : CliGhostAllocHooks M A lim gh)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hEnv : ∀ g evs,
      h10b_DecPkD3ValidMatchSeqFreePollEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD3 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      dpPollEntryPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')) := by
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hfroz0, hpre0⟩ :=
    extract_withLsFrozen
      (spec := dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk') hpre
  have hro0 : LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨LibsignalCodeLoaded.of_codeLoaded hfroz0.2, hfroz0.1⟩
  have hpre_ro : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hro0, hpre0⟩
  obtain ⟨hpure, hm_base⟩ :=
    dpPollPre_unpack_d3_placed (X := X) (W := W) (B := B) (S := S) (Scope := Scope)
      hSemOk stk' y R s0 hpre_ro
  obtain ⟨_m0, _, _, _hpk0, hdec0⟩ := hpure.decPkOk
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  have hEqP :
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
    dsimp only [
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
      dpPollProgPlaced, stageP1ProgPlaced
    ]
    rw [withPanics_cliGhostExterns mmpl gh W]
  have hDeser' := hEqP ▸ hDeser
  cases b with
  | false =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    rw [hEqP]
    exact closure_untrusted_d3_kits_placed_ok A lim hDropNz mmpl gh W X B S Scope
      hh hinjK hsub hS stk' hneed' hstk63 y
      (hKits.sessOk y.g.F y.g.peer)
      (hKits.idOk y.g.F y.g.peer)
      (fun evs hevs => hpure.fits evs (hEnv y.g evs (Or.inl hevs)))
      (fun evs hevs => hEnv y.g evs (Or.inl hevs))
      R s0 hpc hrun hsp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk htrusted hm_base
  | true =>
    dsimp only [dpPollEntrySpatialPlaced] at hm_base
    have hhSt :
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
          A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
      ⟨hh.alloc, hh.allocFs, hh.panics, hh.memcpyRO, hh.bcmp, hh.fs,
       hh.utf8, hh.memrchr, hh.codecHooks, hh.allocZeroed, hh.stringClone, hh.formatInner⟩
    let σ := cliKitStk B
    let pid := pmPreKeyId y.g.msg
    let sid := y.g.msg.signedPreKeyId
    let kid := pmKyberId y.g.msg
    let kbk := y.g.msg.baseKey
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F sid σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid sid kbk σ
    let kitEnv := cliPollSessSeqFreeBudgetEnv A.repAlloc y.g.F y.g.peer σ DeserEnv ReadEnv
    let ikitEnv := cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer σ ReadEnv
    let pkKitEnv := cliPollPkBudgetEnv A.repAlloc y.g.F pid σ ReadEnv
    let kpkKitEnv := fun kpkId spkId =>
      cliPollKpkBudgetEnv A.repAlloc y.g.F kpkId spkId y.g.msg.baseKey σ ReadEnv
    let sp := s0.sp - 0xcd0#64
    have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned] using hsp
    have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
      (subStack_le_sp_of_dpPollNeed hneed' hpure.stk_le_sp).1
    have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced A.repAlloc σ y.g.stores
      hsub hpure.filesOkPeer hdec0 (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
    have hm_stores : s0.mem ⊨
        memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
        memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        stackAt s0.sp stk' ∗
        R :=
      Satisfies.mono (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hent_stores)))) hm_base
    have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
      have := dpPollNeed_eq_frame_add_subStack B; omega
    have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
      stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
    rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
        preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        stackAt_poll_entry_split s0.sp B stk' hneed' hstk63,
        stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
        clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
    rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
      b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
    rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
    simp only [Nat.reduceMul] at hm_flat
    dsimp only [cliPollStoresKitsAtPlaced, coroUnusedP1AtPlaced] at hm_flat
    let P_p1 : SepProp :=
      stageP1OkPreAt A lim y.st kit ikit StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer y.g.msg.identityKey s0 sp y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) y.g.stores
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
        v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2
    let Fr_inner : SepProp :=
      memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗
      closStackUnusedP1OkAt sp ∗
      memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit
    have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
      Satisfies.mono (by
        dsimp only [P_p1, Fr_inner, stageP1OkPreAt, kit, ikit, pkKit, spkKit, kpkKit,
          cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
          cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKpkStoreSpecFullPlaced,
          CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]
        sep_frame) hm_flat
    rw [hEqP]
    refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
    have hfits_all :
        FitsEnv M lim y.st
          (h10b_DecPkD3ValidMatchSeqFreePollEnv (A := A.repAlloc) W X B ReadEnv DeserEnv
            P2PathAErrEnv P2PathAOkEnv tdEnv y.g) :=
      fun evs hevs => hpure.fits evs (hEnv y.g evs hevs)
    have hfits_p1 : FitsEnv M lim y.st (CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      fun evs hevs => hfits_all evs (Or.inr (Or.inl hevs))
    have hwp := stageP1_ok_placed_of_kits (Qp := fun _ _ => False) mmpl gh W B y.g.F y.g.peer
      y.g.msg.identityKey
      hDropNz hhSt (hKits.sessOk y.g.F y.g.peer) (hKits.idOk y.g.F y.g.peer)
      y.st StoresGhost.opened.sessions StoresGhost.opened.identity
      (Nat.le_trans hp1_le hsub64) rfl rfl
      (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
        StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
      (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
        cliId_trustRel_eq_of_trusted htrusted h)
      hfits_p1
      s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
      v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
      b_390 b_4f2
      hpure.ro
      (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hpure.files_eq)
      hpc hrun hsp_align0 rfl hpure.x0 hpure.x1 hpure.x2
    refine sepWPp_bind_p1_false_d3 hwp ?_
    intro s1 P_1 hsteps01 hpc1 hrun1 hq1
    rcases hq1 with ⟨⟨opt, evs_p1, hP1_raw, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
      hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, _hro1⟩
    have hfroz1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hfroz0 hsteps01.keepsFrozen
    have hevs_p1 : CliStageP1OkEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs_p1 := hP1_raw
    have htr1 : s1.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
      hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
    have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) :=
      ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
       hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
    refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
    simp only [sepExists_sepConj_left]
    refine sepWPp_sepExists_left fun v_a8 =>
      sepWPp_sepExists_left fun v_b8 =>
      sepWPp_sepExists_left fun v_d0 => ?_
    have hrecomb := p1Ok_recombine_entails_stageP2_budget_d3_placed stk' hneed' hstk63 y
      (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
    dsimp only at hrecomb
    refine sepWPp_conseq_pre hrecomb ?_
    cases opt with
    | none =>
      have hfits_p2 :
          FitsEnv M lim (M.stepEvents evs_p1 y.st)
            (StageP2PathAEnv P2PathAErrEnv P2PathAOkEnv y.g) :=
        (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inl h⟩))).seq_right hevs_p1
      have hevs_p2_err : ∀ evs_p2, P2PathAErrEnv y.g evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) :=
        fun evs_p2 he2 =>
          hEnv y.g _ (Or.inr (Or.inr (Or.inl
            ⟨hload_rel, Or.inl (SeqEnv.append hevs_p1 (Or.inl he2))⟩)))
      refine h2k520vm_closure_pathA_seqFree_d3_frozen_kits_placed_ok hDropNz mmpl gh W X B S
        hP2A hG hKits Scope hhSt hDeser' hTryDec
        hinjK hsub hS stk' hneed' hstk63 y kitEnv ikitEnv pkKitEnv kpkKitEnv
        rfl rfl rfl (fun _ _ => rfl)
        evs_p1 s0 s1 coins v_a8 v_b8 v_d0 R
        hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted hload_rel
        hfits_p2 hevs_p2_err ?_ ?_ ?_ ?_ ?_ ?_
        hsteps01 htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
      · intro evs_p2 m i k kp reg dk recG he2 hpk hmsg_i hi hk hkp hreg hacc hex hgv
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hgv, Or.inl h⟩⟩))).seq_right
          (SeqEnv.append hevs_p1 he2)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt he2 hpk hmsg_i hi hk hkp hreg hacc hex hgv
          hver hcl hdec he3 hok
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
            hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hgv,
            Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok, h⟩⟩⟩))).seq_right
          (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpk hmsg_i hi hk hkp hreg hacc hex hgv
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hgv,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inr (Or.inr he4)))⟩⟩⟩)))
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 pt evs_p4 he2 hpk hmsg_i hi hk hkp hreg hacc hex hgv
          hver hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hgv,
          Or.inr ⟨G₁, G', pt, hver, hcl, hdec, hok,
            SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
              (Or.inr (Or.inl he4))⟩⟩⟩)))
      · intro evs_p2 m i k kp reg dk recG G₁ G' evs_p3 e he2 hpk hmsg_i hi hk hkp hreg hacc hex hgv
          hver hcl _hdec he3 _herr _hne
        have he3_env : StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver, ↓reduceIte]
          exact ⟨G₁, hcl, he3⟩
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hgv,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
      · intro evs_p2 m i k kp reg dk recG evs_p3 he2 hpk hmsg_i hi hk hkp hreg hacc hex hgv hver_ne he3
        have he3_env : StageP3Env tdEnv recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
            y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver_ne, ↓reduceIte]
          exact he3
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inl ⟨hload_rel, Or.inr ⟨m, i, k, kp, reg, dk, recG,
          hpk, hmsg_i, hi, hk, hkp, hreg, hacc, hex, hgv,
          Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
    | some r =>
      obtain ⟨sess, hcur⟩ := currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
      have hfits_p2 :
          FitsEnv M lim (M.stepEvents evs_p1 y.st)
            (StageP2MatchedEnv sess y.g.msg.identityKey) :=
        (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur, Or.inl h⟩))).seq_right hevs_p1
      refine h2k520vm_closure_pathB_seqFree_d3_frozen_kits_placed_ok hDropNz
        stageP2Matched_framed_cli_placed_ok hG mmpl W X B S Scope
        hhSt hKits hDeser' hTryDec hinjK hsub hS stk' hneed' hstk63
        y kitEnv ikitEnv rfl rfl evs_p1 r sess s0 s1 coins v_a8 v_b8 v_d0 R
        hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt htrusted hload_rel hcur hfits_p2
        ?_ ?_ ?_ ?_ ?_ ?_
        hsteps01 htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
      · intro hne evs_p2 he2
        have he2_env : StageP2MatchedEnv sess y.g.msg.identityKey evs_p2 := by
          unfold StageP2MatchedEnv
          simp only [hne, ↓reduceIte]
          exact he2
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr
          ⟨r, sess, hload_rel, hcur, Or.inl (SeqEnv.append hevs_p1 he2_env)⟩)))
      · intro hrem evs_p2 recG he2 hex hgv
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, hgv, Or.inl h⟩⟩))).seq_right (SeqEnv.append hevs_p1 he2)
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt he2 hex hgv hcl hdec he3 hok
        exact (hfits_all.mono fun _ h =>
          Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
            Or.inr ⟨hrem, recG, hex, hgv, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok, h⟩⟩⟩))).seq_right
          (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3)
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 he2 hex hgv hcl hdec he3 hok he4
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex, hgv, Or.inr ⟨hver, G₁, G', pt, hcl, hdec, hok,
            SeqEnv.append (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3) (Or.inr he4)⟩⟩⟩)))
      · intro hrem hver evs_p2 recG G₁ G' evs_p3 e he2 hex hgv hcl _hdec he3 _herr _hne
        have he3_env : StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver, ↓reduceIte]
          exact ⟨G₁, hcl, he3⟩
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex, hgv,
            Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))
      · intro hrem hver_ne evs_p2 recG evs_p3 he2 hex hgv he3
        have he3_env : StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins evs_p3 := by
          unfold StageP3Env
          simp only [hver_ne, ↓reduceIte]
          exact he3
        exact hEnv y.g _ (Or.inr (Or.inr (Or.inr ⟨r, sess, hload_rel, hcur,
          Or.inr ⟨hrem, recG, hex, hgv,
            Or.inl (SeqEnv.append (SeqEnv.append hevs_p1 he2) he3_env)⟩⟩)))

/-! ## Caller-Block and `lsProg_579` Frozen Slot-`520` Producers -/

/-- Caller-block (`i < 619`) `decPkSlotSpecFrozenPlaced` reduction at `lsmpl.base 520` for D3
`validMatch` (`DecPkOkD3`) from `CliDecPkPollKitsPlacedOk`. -/
theorem h2k520vm_cliDecryptPrekey_slot_d3_match_seqFree_frozen_kits_placedBudget_at_block
    [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv P2PathAErrEnv P2PathAOkEnv : DecPkGhost → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (_hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKits : CliDecPkPollKitsPlacedOk A lim B ReadEnv DeserEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDeser : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hP2A : StageP2PathAQpanCliD3NoReadAtFrozenPlacedBudgetStmt A lim DeserEnv X mmpl gh W B
      P2PathAErrEnv P2PathAOkEnv)
    (hG : CliGhostAllocHooks M A lim gh)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkD3 ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      h10b_DecPkD3ValidMatchSeqFreeEnv A.repAlloc W X B ReadEnv DeserEnv
        P2PathAErrEnv P2PathAOkEnv tdEnv g evs →
      DecPkEnv g evs)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpan : Rust.withPanics H = H := withPanics_cliGhostExterns mmpl gh W
  have : IsLsBlockProg prog i (Rust.withPanics H) := by
    rw [hpan]; exact hcaller
  have hEq518 :
      lsProg_518 (Rust.withPanics H) =
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced H := rfl
  have hpoll := h2k520vm_decPk_d3_validMatch_seqFree_poll_frozen_kits_placedBudget hDropNz
    mmpl gh W X B S Scope hh hKits hDeser hP2A hG hTryDec hevs_sub hinjK hsub hS hok
  exact dpSlot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := H)
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' hs1 hs2 => by
        rw [hEq518]
        exact hpoll stk' hs1 hs2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed, dpSlotPollKStatePlaced] at hstk ⊢
          omega)
      hstk64)

/-- `slotsOfSigPkFrozenPlaced` producer on `lsProg_579` from Block-`589` `dirGetSpecPlaced`
and `SpqrV1PlacedSeamsOfEnv`. -/
theorem h2k520vm_decPkValidMatchSlotOk_seqFree_of_dirGet_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd)
        cliRunBudgets.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W (InitialStateEnv W.C.F) RecvEnv SendEnv)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      h10b_DecPkD3ValidMatchSeqFreeOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hEqP :
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced H =
      dpPollProgPlaced H := by
    dsimp only [
      CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced,
      dpPollProgPlaced, stageP1ProgPlaced
    ]
    rw [withPanics_cliGhostExterns mmpl gh W]
  have hDeserHelpers : subroutine_ok
      (CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers.dpPollProgPlaced H)
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv) :=
    hEqP.symm ▸ hDeser
  have hKits : CliDecPkPollKitsPlacedOk A lim cliRunBudgets ReadEnv DeserEnv H :=
    cliDecPkPollKitsPlacedOk_of_dirGet mmpl gh W cliRunBudgets h547 hh hGet hDeser
  have hP2A :
      StageP2PathAQpanCliD3NoReadAtFrozenPlacedBudgetStmt A lim DeserEnv X mmpl gh W cliRunBudgets
        _ _ :=
    stageP2PathAQpan_cli_d3_full_noRead_placed_of_kits A lim (DeserEnv := DeserEnv)
      X mmpl gh W cliRunBudgets h547 hG hSpqr
      hKits.selfOk hKits.spkOk hKits.kpkOk hKits.pkOk
  intro stk h1 h2
  exact h2k520vm_cliDecryptPrekey_slot_d3_match_seqFree_frozen_kits_placedBudget_at_block
    (prog := lsProg_579 H) (i := 579)
    A lim cliRunBudgets mmpl gh W (by decide) X S scopeIn
    h547 hh hKits hDeserHelpers hP2A hG hTryDec
    encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
    (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
    hsEnv stk (hneed ▸ h1) h2

/-- Frozen Slot-`520` producer for D3 `validMatch` into any `PeerSpqrStateTight640`-guarded
target envelope `TargetEnv`. -/
theorem h2k520vm_decPkValidMatchSlotOk_seqFree_targetGuarded_of_dirGet_frozen
    [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {RecvEnv : VecArg → VecArg → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {TargetEnv : DecPkGhost → List AllocEvent → Prop}
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd)
        cliRunBudgets.dirGetNeed))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl gh W (InitialStateEnv W.C.F) RecvEnv SendEnv)
    (hTryDec : subroutine_ok
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse
          (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hSlot : ∀ g e,
      sEnvs.decryptPrekey g e ↔
        (PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val → TargetEnv g e))
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets)
    (hBridge : ∀ g evs,
      filesOk₀ scopeIn (fun _ => True) g.F g.peer.val g.me.val →
      DecPkOkD3 ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val →
      h10b_DecPkD3ValidMatchSeqFreeOfReadEnv A.repAlloc W X cliRunBudgets ReadEnv DeserEnv tdEnv g evs →
      TargetEnv g evs) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  h10b_decPkValidMatchSlotOk_targetGuarded_frozen S sEnvs needs hSlot
    (fun sEnvs0 hsEnv0 =>
      h2k520vm_decPkValidMatchSlotOk_seqFree_of_dirGet_frozen_placedBudget mmpl gh W X
        h547 hG hh hGet hDeser hSpqr hTryDec S sEnvs0 needs hsEnv0
        hfiles hdecPk hdecPkOk hneed)
    hfiles hdecPkOk hBridge

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSlot520VmPoll
