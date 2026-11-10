/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Specifications.SignalSession.CliElf
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
import LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR
import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3MatchingPathBAuxPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyG2
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1Placed
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import ProofLib.SepLogic.WPp

/-!
# Unbundled `MainOkPathBD3F3` Assembly on `cliElfBytes`

Proves `hole_m24slot_pathB_assembly_closed`, establishing `MainOkPathBD3F3` on
`cliElfBytes` from unbundled ghost-witness hypotheses via the sequence-free Path-B
block-520 `decryptPrekey` contract and `Dom0` single-slot budget witness.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinPathB

open Arm64 ProofLib SepProp
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (bytesOfString)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym
   stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliMainStk cliResStack cliRunBudgets cliRunBudgets_placed cliRunNeeds
   cliWrOk inputOf mainFrameSize parseArgs)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds addrValOf mkSlot runFiles slotOut slotTrace)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliPollSessKitPlaced loadRec_scopeKit_eq)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (FilesOkPeer encodeInjOn_deserializeScopeP_Q loadRec scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (fineAesDec_budget_hookOk)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (pksmParse_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge (not_fitsEnv_top)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
  (ckx2_w1EncExact_groupSpec ckx2_w1EncExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0 (d3SlotMainFitsOneGiBOf)
open LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR
  (DecPkD3MatchingPathBGvEnv DecPkD3MatchingPathBGvSeqFreeOfReadEnv MatchingPathBGvMainEnv
   MatchingPathBGvPollEnv decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0')
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (recv_rest_length_le_msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf (TryDecryptCliLinkedEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (W4BinaryCallSiteDomCmk0 W4BinaryRecvPrekeyDomCmk0
   W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
   realCliDecPkBinaryWideSlotEnvCmkDom0Fixed'
   realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'
   realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed_ghost_congr
   w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec'
   w4CmkDom0Cum w4CmkDom0GrpS109 w4CmkDom0GrpSOf_109_eq w4CmkDom0Live w4CmkDom0MaxReq
   w4CmkDom0Peak w4CmkDom0_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux (w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryRecvPrekeyParamsCmk w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (DecPkOkPathB pathB_scopeIn_and_match_of_decPkOkPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOfEnvGlue
  (cli_tryDecrypt_of_tdEnv_at_518)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
  (peerSpqrStateTight640_of_cliPqOrD3Recv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
  (MainOkPathBD3F3 cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (CliPqOrD3RecvInputs)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyG2
  (h9g_poll_readFile_and_sessDeser_of_hooks)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2
  (h9r2_honestD3FineSlotEnvs h9r2_pathB_assembly_honest_d2cSlots_of_dom0_singleSlot)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (Block617TransferFixedHyp)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (StageP3Env StageP3ErrEnv StageP3OkPrefixEnv stageP3TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudget
  (stageP3PrevEmptyVRegs_of_base_full_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (CliSpqrRecvTightLinkedEnv SpqrSendCoinsTightLinkedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2
   fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2
   fits2_w2DecSigExact_groupSpec fits2_w2DecSigExact_phaseCredit)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   hole3_decSigEnv_r3a_congr hole3_encEnv_r2_congr hole3_w1_inner hole3_w2_inner hole3_w3_init
   libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_TryDecryptTopStateGuardedEnv w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty
   w4s2_spqrSeams_topStateGuarded w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)

/-! ## `TopStateTight`-Guarded `tryDecrypt` Envelope Reduction -/

private theorem h8pb_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs :=
  h.elim (fun ha => Or.inl (h1 evs ha))
    (fun ⟨e1, e2, heq, ha, hb⟩ => Or.inr ⟨e1, e2, heq, h1 e1 ha, h2 e2 hb⟩)

private theorem h8pb_gvSeqFree_sub_cmkDom0' [LibsignalPlacement]
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
      refine h8pb_seqEnv_mono (fun _ h => h) ?_ hevs
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
      · refine Or.inr ⟨hrem, recG, hex, hgv, h8pb_seqEnv_mono (fun _ h => h) ?_ hseq⟩
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
        · refine Or.inr ⟨hver, G₁, G', pt, hcl, haft, hmod, h8pb_seqEnv_mono ?_ (fun _ h => h) hok⟩
          intro evsP3 hpfx
          unfold StageP3OkPrefixEnv at hpfx ⊢
          rw [← w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W
            (stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins)
            hTop]
          exact hpfx
  exact decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0' A X W cliRunBudgets_placed
    (fun _ _ h => h) hfPeer hdecOk hTight hevs109

/-! ## Frozen Block-520 Path-B Producer -/

section FrozenPathBGvSeqFree

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (ApiError Session SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks
   libsignalFrozen_of_keepsFrozen lsRustNoAllocShimSym lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5ModelPanicProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (SessionExtraRel loadCallStack p1LoadedRecordAt sp_sub_cd0_align_std3 stageP1CallStack
   stageP1UntrustedCallStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure
  (decryptPrekeyCoroCopyAt decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt
   processPrekeyInnerInitAt processPrekeyPostTrustAt)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal RecordGhost apiDecResultAt preKeyMsgAt)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsFrozen noAllocShimSpec rootStack withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost SignalMessageGhost decryptDraws protocolAddressAt signalMessageAt
   vecResultAt)
open CryptoVerification.SignalSession (isCliPanicSymbolPlaced)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
   cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.KitInst
  (cliIdentityStoreSpec cliKyberPreKeyStoreSpecPlaced cliPreKeyStoreSpecPlaced
   cliSessionStoreSpec cliSignedPreKeyStoreSpecPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose
  (RunSem decResAt dpPollNeed dpSlotArgsPlaced slotOutTr)
open CryptoVerification.SignalSession.Cli.RunGlue (cliGhostExterns_other withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (SessMatchesPm decPkDef dpCxAt dpFutDoneAt dpFutStartAt dpWrapFrame)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (LsTokenInit StageP1PostRegs apiDecResultAt_proto_entails_decResAt
   apiDecResultAt_untrusted_entails_decResAt cliIdStoreSpecFull cliIdStoreSpecFullPlaced
   cliId_saveRel_not_err cliId_trustRel_eq_of_trusted cliKitStk cliKpkStoreSpecFullPlaced
   cliPollIdKit cliPollIdKitPlaced cliPollId_trustUpdate_eq_placed cliPollId_vtablesPlacedOk
   cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKit
   cliPollSess_vtablesPlacedOk cliPollSpkKitPlaced cliPollStoresKitsAtPlaced
   cliPollStoresKitsAtPlaced_entails_storesAt cliSess_loadRel_isOk cliSess_storeRel_not_err
   closStackUnusedP1OkAt closStackUnusedUntrustedAt clos_stack_3280_of_p1_untrusted
   clos_stack_3280_split_for_p1_ok clos_stack_3280_split_for_p1_untrusted
   closureCalleeSaved_toCalleeSavedPreserved coroUnusedP1At
   coro_of_p1_untrusted_entails_dpFutDoneAt decPkDef_of_trust_err decPkDef_pathB_remId_ne
   decPkDef_pathB_ver_ne dpClosSubStack dpCxAt_entails_memRegion32
   dpFutStartAt_split_for_p1_placed dpPollEntryPlaced dpPollNeed_eq_frame_add_subStack
   dpPollProgPlaced loadRec_of_cliPollSessPlaced_loadRel pmKyberId pmPreKeyId
   preKeyMsgAt_eq_idKey_sep preKeyMsgRemIdKeyAt rootStack_le_subStack sepWPp_conseq_pre
   sepWPp_sepExists_left sessionExtraRel_of_clone_decRel slotOutTr_of_err slotOutTr_of_ok
   slotOutTr_of_reject sp_frame_sub_add stackAt_poll_entry_split stackAt_subStack_split
   stackAt_subStack_sub_eq stageP1CallStack_le_subStack stageP1UntrustedCallStack_le_subStack
   stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt stageP3Sub5ExtraPrePrevEmpty
   stageP4MatchedCallStack subStack_le_sp_of_dpPollNeed subroutine_ok_of_sepWPp_steps
   trusted_ok_of_filesOkPeer)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn filesOk₀)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
  (chainClone3_placed_ok_of_hooks senderChainClone3_placed_ok_of_hooks)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
  (drop_session_structure4_placed_ok_at)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetAux
  (StageP2MatchedBridgeEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget
  (StageP2MatchedEnv StageP2MatchedMismatchEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (decPkDef_pathB_err_pathB decPkDef_pathB_ok_pathB decPkDef_pathB_panic_pathB
   distinctSid_of_decPkOkPathB genP3S5Model
   storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (decPkSlotSpecFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMainPlacedBudget
  (StageP2MatchedFramedCliPlacedStmt sepWPp_genP3_to_tailQpan_placed sepWPp_pollGoal_frame_placed
   stageP3_exit_prevEmpty_to_pollPost_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlacedBudget
  (pathBP4RemAtPlaced stageP3MidPrevEmpty_eq_p4_placed stageP4MatchedExit_entails_exit_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBTopPlacedBudget
  (cliFiles_eq_of_trace_eq_placed cliPollStageP1_fsAt_placed exit_entails_dpPollPost_placed
   stageP4MatchedStack_placed_le_pow64)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
  (StageP1OkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (ChainClone3OkPlaced SenderChainClone3OkPlaced StageP3VerNeEnv genP3Pre_placed
   genP3S5PostFrame_placed pollTryDecryptPlacedSpecTPTight
   stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced StageP4MatchedEnv StageP4MatchedStoreStepEnv stageP4MatchedExitAtPlaced
   stageP4MatchedPrePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv StageP1UntrustedMangledPlacedStmt dpPollPost_of_decResAt_placed
   runHooks_to_stages stageP1_untrusted_mangled_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlacedBudget
  (stageP2Matched_framed_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlacedBudget
  (stageP1_ok_placed_inst)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlacedBudgetAux
  (StageP3CalleesM3BasePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
  (cliPollIdBudgetEnv cliPollId_kitPlacedOkI cliPollSessBudgetEnv cliPollSessSeqFreeBudgetEnv
   cliPollSess_seqFreeKitPlacedOkSE stageP4Matched_placed_of_kits)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.SlotPlacedBudget
  (dpSlotPollKStatePlaced_inv_vm dpSlotPollKStatePlaced_res_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.WrapperStatePlacedBudget
  (cliDecryptPrekey_ok_state_frozen_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced
   dpSlot_ok_state_frozen_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

private theorem h8pb_sessionGhostValid_of_genP3Pre [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) (F_rem : SepProp)
    (hex : SessionExtraRel recG sess)
    (hm : s.mem ⊨ genP3Pre_placed A lim st_b sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG sess.state rem loc msgG msg s ∗ F_rem) :
    SessionGhostValid recG sess := by
  refine ⟨hex, A.atState lim st_b s, coroPtr + 0xf8#64, s.mem, ?w, ?_⟩
  rotate_left
  refine Arm64.Satisfies.mono ?_ hm
  dsimp only [
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget.genP3Pre_placed,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3Pre_placed]
  sep_frame

set_option maxHeartbeats 800000 in
private theorem h8pb_closure_pathB_p4_cont_pathB_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    {kitEnv4 : SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))}
    (hSkit : SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
      kitEnv4 scopeKit encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (sess : Session (List (BitVec 8)))
    (evs_pre : List AllocEvent)
    (s0 s2 s' : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem P_s' R : SepProp)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (g : RecordGhost) (recG G₁ G' : SessionGhost)
    (pt : List (BitVec 8))
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hIn : scopeIn ⟨some sess⟩)
    (hloadS : loadRec Scope y.g.F y.g.peer.val = .ok (some ⟨some sess⟩))
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hMatch : SessMatchesPm sess y.g.msg)
    (hrem : sess.state.remoteIdentity = some y.g.msg.identityKey)
    (hex : SessionExtraRel recG sess)
    (hfits_p4 : FitsEnv M lim (M.stepEvents evs_pre y.st)
      (StageP4MatchedEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)) kitEnv4
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer.val y.g.msg.identityKey
        { sess with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
          pendingPreKey := none
          pendingKyberPreKey := none }))
    (hevs_ok : ∀ evs_p4,
      StageP4MatchedStoreStepEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)) kitEnv4
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)) (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        StoresGhost.opened.sessions StoresGhost.opened.identity
        y.g.peer.val y.g.msg.identityKey
        { sess with
          state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
          pendingPreKey := none
          pendingKyberPreKey := none } evs_p4 →
      DecPkEnv y.g (evs_pre ++ evs_p4))
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hs2_files : s2.fs.files = y.g.F)
    (htr20 : s2.trace = s0.trace)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hsp_align2 : (s2.sp &&& 15#64 == 0#64) = true)
    (hver : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32)
    (hcl : CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁)
    (hdec_rel : G₁.AfterTryDecrypt true G')
    (hok : (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hpt_lt : ptCap.toNat < 2 ^ 63)
    (hpt_ne : ptPtr ≠ 0#64)
    (hsteps2' : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s2 s')
    (hpc' : s'.pc = dpPollEntryPlaced + 0x34dc#64)
    (hrun' : s'.status = .Running)
    (hs'_sp : s'.sp = s2.sp)
    (htr' : s'.trace = s0.trace)
    (hvregs' : calleeSavedVRegs s' = calleeSavedVRegs s0)
    (hx19' : s'.readReg64 .x19 = y.fut)
    (hx24' : s'.readReg64 .x24 = s2.sp + 0x370#64)
    (hx25' : s'.readReg64 .x25 = s2.sp + 0x210#64)
    (hx26' : s'.readReg64 .x26 = y.out)
    (hx27' : s'.readReg64 .x27 = y.cx)
    (hx28' : s'.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hro' : LibsignalCodeRoLoaded lsmpl s'.mem)
    (hent_s' : P_s' ⊢
      stageP3DispatchOkMidPrevEmpty_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s' y.fut y.out 8#64
        ptCap ptPtr g pt 0#8 G'
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
      genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins))) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
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
    let Fr_tail : SepProp :=
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
      memRegion y.cx 32
    SepWPp prog (s0.readReg64 .x30) s'
      (P_s' ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
          (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
          (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
            ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
            memRegion (y.fut + 0x2a8#64) 4) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ∗
        ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
        kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (genP3S5ModelPanicProp W.C W.Q.K y.g.peer y.g.me sess.state y.g.msg.message
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins s0) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
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
  let st' := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
  let ses' : Session (List (BitVec 8)) :=
    { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  let coinsPost := coinsAfterPlaced y.g.coinsP y.g.coins
    (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)
  obtain ⟨hDec, hWr, hKit', hLen'⟩ :=
    decPkDef_pathB_ok_pathB X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
      hfPeer hdecOk hIn hloadS htrusted hMatch hrem hver hok
  have hex' : SessionExtraRel G' ses' := sessionExtraRel_of_clone_decRel hex hcl hdec_rel
  have hs'_sp0 : s'.sp = sp := hs'_sp.trans hs2_sp
  have hsp_ret : sp + 0xcd0#64 = s0.sp := BitVec.sub_add_cancel s0.sp 0xcd0#64
  have hs'_files : s'.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps2' (htr'.trans htr20.symm)).trans hs2_files
  have hfs_p4 := cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hs'_files
  have hp4_64 : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 :=
    stageP4MatchedStack_placed_le_pow64 A.repAlloc B hneed hstk63
  have hwp4 := stageP4Matched_placed_of_kits mmpl gh W B y.g.F y.g.peer hDropNz hh hSkit
    (cliPollId_kitPlacedOkI mmpl gh W B y.g.F y.g.peer hDropNz hh hReadFile)
    (M.stepEvents evs_pre y.st) s0 s'
    y.fut y.g.msgA y.cx y.out y.g.peerA (y.g.msgA + 0xc8#64)
    (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
    y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
    g G' ses'
    hex' ⟨hKit', hLen'⟩ rfl rfl hfits_p4
    hpt_le hpt_lt hpt_ne hp4_64 hfs_p4 hro' hpc' hrun'
    (hs'_sp ▸ hsp_align2) (htr' ▸ List.prefix_refl _)
    hx19' (hs'_sp ▸ hx24') (hs'_sp ▸ hx25') hx26' hx27' hx28' hvregs'
  intro R' hm hL
  have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_s')) hm
  have hmid := stageP3MidPrevEmpty_eq_p4_placed A lim (M.stepEvents evs_pre y.st) B y
    s0 s2 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG
    preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
    opkHi kyberPreKeyId signedPreKeyId pt g G' st' hs2_sp hs'_sp0 hsp_sub
  dsimp only at hmid
  have hm2 : s'.mem ⊨
      stageP4MatchedPrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit s0 s'
        y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
        (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
        y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
        g G' st' ∗
      (pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
        (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
    have hEq :
        ((stageP3DispatchOkMidPrevEmpty_placed A lim (M.stepEvents evs_pre y.st) s0 s2 s' y.fut y.out 8#64
            ptCap ptPtr g pt 0#8 G' st' ∗
          genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me whisperG y.g.msg.message
            coinsPost) ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
              ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
              memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ∗
          ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
          kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
          memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) ∗ R' =
        stageP4MatchedPrePlaced A lim (M.stepEvents evs_pre y.st) kit ikit s0 s'
          y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
          (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
          y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
          g G' st' ∗
        (pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗ R') := by
      dsimp only [sp, σ, kit, ikit]
      rw [hs2_sp, hmid, sepConj_assoc]
    exact hEq ▸ hm1
  obtain ⟨sf, hsteps_p4, hBranch⟩ := hwp4 _ hm2 hL
  refine ⟨sf, hsteps_p4, ?_⟩
  rcases hBranch with
    ⟨hpcm, hrunm, Pf, hmf, ⟨_hsteps'f, hspf, hcs_p4, hvregs_f, _hro_f, hBr⟩⟩ |
    ⟨_hpanf, _Pf, _hmf, hfalse⟩ |
    ⟨_, hoom⟩
  · rcases hBr with
      ⟨c, evs_p4, hevs_p4, _hsave, _hstore, htr_f, hpost_f⟩ |
      ⟨_evs_p4, _hevs_p4, hsave, _, _⟩ |
      ⟨_, _evs_p4, _hevs_p4, _, hstore, _, _⟩
    · rw [← sepConj_assoc] at hmf
      have hsf_sp : sf.sp = s0.sp := by rw [hspf, hs'_sp0, hsp_ret]
      have hcs_full : CalleeSavedPreserved s0 sf :=
        CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.ClosureCalleeSavedP4.toCalleeSavedPreserved hcs_p4 hvregs_f
      have htr_sf : sf.trace = s0.trace := by
        dsimp only [kit, ikit, cliPollSessKitPlaced, cliPollSessKit, cliSessionStoreSpec,
          cliPollIdKitPlaced, cliIdStoreSpecFullPlaced, cliPollIdKit, cliIdStoreSpecFull,
          cliIdentityStoreSpec] at htr_f
        simpa [htr'] using htr_f
      refine Or.inl ⟨hpcm, hrunm,
        Pf ∗ pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
          (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost,
        hmf, ?_, hsf_sp, hcs_full⟩
      intro hsteps0f hm_f
      let g' : StoresGhost :=
        { StoresGhost.opened with
          identity := StoresGhost.opened.identity.saveUpd cliIo.rd y.g.F y.g.peer.val
            y.g.msg.identityKey
          sessions := StoresGhost.opened.sessions.put (CryptoVerification.SignalSession.Cli.addressText y.g.peer.val)
            (encodeRecord ⟨some ses'⟩) }
      have hout : slotOutTr
          (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
          g' (.ok pt) s0.trace sf.trace :=
        slotOutTr_of_ok s0.trace sf.trace (by rw [hS]; exact hDec) hWr
      have hpost_f' :
          Pf ⊢ stageP4MatchedExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st) kit ikit
            s0 s' sf y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
            (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
            (vecResultAt A.repAlloc y.out (.ok pt)) pt
            y.g.peer y.g.msg.identityKey
            (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
            (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) := by
        rw [M.stepEvents_append evs_pre evs_p4 y.st]
        exact hpost_f
      have hm_f1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hpost_f')) hm_f
      have hexit := stageP4MatchedExit_entails_exit_placed A lim (M.stepEvents (evs_pre ++ evs_p4) y.st)
        B y s0 s' sf rngPtr whisperMsgPtr ptCap ptPtr whisperG
        preKeyMsgRem coinsPost (y.g.msg.message.messageVersion.zeroExtend 32)
        opkHi kyberPreKeyId signedPreKeyId pid kid pt
        (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
        (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c))
        g' hs'_sp0 hsp_sub hmsg_fold rfl rfl rfl rfl rfl rfl
      dsimp only at hexit
      have hm_f2 : sf.mem ⊨
          (stageP4MatchedExitAtPlaced A lim (M.stepEvents (evs_pre ++ evs_p4) y.st) kit ikit
              s0 s' sf y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
              (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
              (vecResultAt A.repAlloc y.out (.ok pt)) pt
              y.g.peer y.g.msg.identityKey
              (kit.storeUpdate StoresGhost.opened.sessions y.g.peer.val ⟨some ses'⟩ (.ok ()))
              (ikit.saveUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey (.ok c)) ∗
            pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG
              (y.g.msg.message.messageVersion.zeroExtend 32) preKeyMsgRem coinsPost ∗
            pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            memRegion y.cx 32 ∗ R) :=
        Arm64.Satisfies.mono (by sep_frame) hm_f1
      have hm_f3 := Arm64.Satisfies.mono (sepConj_mono_left hexit) hm_f2
      have hm_f4 : sf.mem ⊨
          (decResAt A.repAlloc y.out (.ok pt) ∗
            storesAt A.repAlloc y.g.stores g' ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            lsLogOff ∗
            A.pool lim (M.stepEvents (evs_pre ++ evs_p4) y.st) sf ∗
            (LsTokenInit ∗ coinsPost) ∗
            dpFutDoneAt y.fut ∗
            memRegion y.cx 32 ∗
            memRegion sp 3280 ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
        Arm64.Satisfies.mono (by sep_frame) hm_f3
      have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
        (evs_pre ++ evs_p4) g' (.ok pt) (LsTokenInit ∗ coinsPost) (hevs_ok evs_p4 hevs_p4)
        hh hsteps0f htr_sf hout
      exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm_f4
    · dsimp only [kit, ikit, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced] at hsave
      exact False.elim (cliId_saveRel_not_err hsave)
    · dsimp only [kit, ikit, cliPollSessKitPlaced] at hstore
      exact False.elim (cliSess_storeRel_not_err hstore)
  · exact hfalse.elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem h8pb_hookSat_sessionShimBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · exact ⟨hkeep, hsym, Or.inl ⟨hret, hcc, hpost⟩⟩
  · exact ⟨hkeep, hsym, Or.inr hrest⟩

private theorem h8pb_hookSat_sessionMemcpyRegionBudget_of_codec {H : LibsignalHooks}
    (h : HookSat H "memcpy"
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    HookSat H CryptoVerification.lsMemcpySym sessionMemcpyRegionBudgetSpec :=
  (show withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
      sessionMemcpyRegionBudgetSpec from rfl) ▸ h

private theorem h8pb_cliChainClone3_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    ChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  chainClone3_placed_ok_of_hooks
    (h8pb_hookSat_sessionShimBudget_of_codec hh.codecHooks.shim)
    hh.codecHooks.alloc
    (h8pb_hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

private theorem h8pb_cliSenderChainClone3_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SenderChainClone3OkPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  senderChainClone3_placed_ok_of_hooks
    (h8pb_hookSat_sessionShimBudget_of_codec hh.codecHooks.shim)
    hh.codecHooks.alloc
    (h8pb_hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)

private theorem h8pb_cliDropSessionStructure4_budget_placed_ok_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at (i := 518) hh.codecHooks.dealloc (by decide)

set_option maxHeartbeats 800000 in
private theorem h8pb_decPk_matchingPathB_main_gv_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {gh : CliGhostHooks}
    (hG : CliGhostAllocHooks M A lim gh)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    {kitEnv4 : ∀ F0 peer, SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r', Scope r' → scopeIn r')
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (evs_p1 : List AllocEvent)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hfits_main : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess))
    (hevs_main : ∀ evs234,
      MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess evs234 →
      DecPkEnv y.g (evs_p1 ++ evs234))
    (hsteps01 : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    let sp := s0.sp - 0xcd0#64
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  let hP2 : StageP2MatchedFramedCliPlacedStmt :=
    stageP2Matched_framed_cli_placed_ok
  have hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2MatchedEnv sess y.g.msg.identityKey) :=
    hfits_main.mono (fun _ h => Or.inl h)
  have hevs_mismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ evs_p2, StageP2MatchedMismatchEnv evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) := by
    intro hrem_ne evs_p2 hevs_p2
    exact hevs_main _ (Or.inl (by simp [StageP2MatchedEnv, hrem_ne, hevs_p2]))
  have hfits_p3 : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ evs_p2 recG, StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        FitsEnv M lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
          (StageP3Env tdEnv recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
            (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins) := by
    intro hrem_eq evs_p2 recG hevs_p2 hex hgv evs_p3 hevs_p3
    rw [M.stepEvents_append]
    exact ((LibsignalBinary.Heap.fitsEvents_append M lim evs_p2 evs_p3 (M.stepEvents evs_p1 y.st)).mp
      (hfits_main (evs_p2 ++ evs_p3)
        (Or.inr ⟨hrem_eq, recG, hex, hgv,
          LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inl hevs_p3)⟩))).2
  have hfits_p4 : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 pt,
        StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        FitsEnv M lim (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st)
          (StageP4MatchedEnv
            (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
            (kitEnv4 y.g.F y.g.peer)
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
            (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
            StoresGhost.opened.sessions StoresGhost.opened.identity
            y.g.peer.val y.g.msg.identityKey
            { sess with
              state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
              pendingPreKey := none
              pendingKyberPreKey := none }) := by
    intro hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt hevs_p2 hex hgv hcl hdec_rel hevs_p3 hok evs_p4 hevs_p4
    have hstep_eq : M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st =
        M.stepEvents (evs_p2 ++ evs_p3) (M.stepEvents evs_p1 y.st) := by
      rw [List.append_assoc, M.stepEvents_append]
    rw [hstep_eq]
    have hmem : MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess
        ((evs_p2 ++ evs_p3) ++ evs_p4) := by
      rw [List.append_assoc]
      exact Or.inr ⟨hrem_eq, recG, hex, hgv,
        LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inr ⟨hver, G₁, G', pt, hcl, hdec_rel, hok,
          LibsignalBinary.Heap.SeqEnv.append hevs_p3 hevs_p4⟩)⟩
    exact ((LibsignalBinary.Heap.fitsEvents_append M lim (evs_p2 ++ evs_p3) evs_p4
      (M.stepEvents evs_p1 y.st)).mp (hfits_main _ hmem)).2
  have hevs_ok : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 pt evs_p4,
        StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .ok pt →
        StageP4MatchedStoreStepEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
          (kitEnv4 y.g.F y.g.peer)
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
          (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
          StoresGhost.opened.sessions StoresGhost.opened.identity
          y.g.peer.val y.g.msg.identityKey
          { sess with
            state := (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2
            pendingPreKey := none
            pendingKyberPreKey := none } evs_p4 →
        DecPkEnv y.g (((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4) := by
    intro hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt evs_p4 hevs_p2 hex hgv hcl hdec_rel hevs_p3 hok hevs_p4
    have hmem : MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess
        (evs_p2 ++ (evs_p3 ++ evs_p4)) :=
      Or.inr ⟨hrem_eq, recG, hex, hgv,
        LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inr ⟨hver, G₁, G', pt, hcl, hdec_rel, hok,
          LibsignalBinary.Heap.SeqEnv.append hevs_p3 (Or.inr hevs_p4)⟩)⟩
    have happ : ((evs_p1 ++ evs_p2) ++ evs_p3) ++ evs_p4 = evs_p1 ++ (evs_p2 ++ (evs_p3 ++ evs_p4)) := by
      simp [List.append_assoc]
    rw [happ]; exact hevs_main _ hmem
  have hevs_err : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG G₁ G' evs_p3 e,
        StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        CryptoVerification.LibsignalTripleRatchet.Record.CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        StageP3ErrEnv tdEnv recG G₁ sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message
          y.g.coins evs_p3 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error e →
        e ≠ .panic → DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3) := by
    intro hrem_eq hver evs_p2 recG G₁ G' evs_p3 e hevs_p2 hex hgv hcl hdec_rel hevs_p3 _herr _hne_p
    have hmem : MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess (evs_p2 ++ evs_p3) :=
      Or.inr ⟨hrem_eq, recG, hex, hgv,
        LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inl (by simp [StageP3Env, hver]; exact ⟨G₁, hcl, hevs_p3⟩))⟩
    rw [List.append_assoc]; exact hevs_main _ hmem
  have hevs_verNe : sess.state.remoteIdentity = some y.g.msg.identityKey →
      sess.state.version ≠ y.g.msg.message.messageVersion.zeroExtend 32 →
      ∀ evs_p2 recG evs_p3, StageP2MatchedBridgeEnv evs_p2 → SessionExtraRel recG sess →
        SessionGhostValid recG sess →
        StageP3VerNeEnv recG sess.state evs_p3 → DecPkEnv y.g ((evs_p1 ++ evs_p2) ++ evs_p3) := by
    intro hrem_eq hver_ne evs_p2 recG evs_p3 hevs_p2 hex hgv hevs_p3
    have hmem : MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess (evs_p2 ++ evs_p3) :=
      Or.inr ⟨hrem_eq, recG, hex, hgv,
        LibsignalBinary.Heap.SeqEnv.append hevs_p2 (Or.inl (by simp [StageP3Env, hver_ne]; exact hevs_p3))⟩
    rw [List.append_assoc]; exact hevs_main _ hmem
  dsimp only
  let sp := s0.sp - 0xcd0#64
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
  dsimp only [cliPollSessKitPlaced] at hload_rel
  obtain ⟨hloadS, hr_eq, hIn, hMatch, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match_of_decPkOkPathB hinjK hsub hfPeer hdecOk hload_rel hcur
  subst hr_eq
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  let F_p2 : SepProp :=
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let Fr_tail : SepProp :=
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB (A := A.repAlloc) σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hstk_split := stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub
  have hpre_split :
      stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      ((stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
          y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt scopeKit A.repAlloc y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        lsLogOff ∗
        stackAt sp rootStack) ∗ F_p2) ∗ Fr_tail := by
    rw [hstk_split]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores_in))))))) ?_
    unfold cliPollStoresKitsAtPlaced F_p2 Fr_tail
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed A lim DecPkEnv B S stk' y ?_)
  refine hP2 mmpl gh W B S scopeKit y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_p2 _ _
    hh hReadFile hDeser hfits_p2 hcoins hMatch hro1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hroot hpc1 hrun1 hsp_align1 hregs1 ?_ ?_
  · intro hrem_ne evs_p2 sf Pf hevs_p2 _ _ _ hsf_sp htr_f hcs_f hvregs_f _ hent_f
    let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hent_f' :
        Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          apiDecResultAt A.repAlloc y.out
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          coinsInstalledPlaced y.g.coinsP y.g.coins ∗
          LsTokenInit ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp rootStack := by
      rw [M.stepEvents_append evs_p1 evs_p2 y.st]
      exact hent_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_f')) hm_f
    have hdec_at := apiDecResultAt_proto_entails_decResAt A.repAlloc y.out
      (.invalidMessage .preKey .badCiphertext) err
    have hstores_out := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
      (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    have hm2 : sf.mem ⊨
        apiDecResultAt A.repAlloc y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer pid sid kid kbk σ
          y.g.stores StoresGhost.opened ∗
        (protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
            stackAt sp rootStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [cliPollStoresKitsAtPlaced, F_p2, Fr_tail]; sep_frame) hm1
    have hm3 := Arm64.Satisfies.mono (sepConj_mono hdec_at (sepConj_mono_left hstores_out)) hm2
    rw [← hstk_split] at hm3
    have hm4 : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error err) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          lsLogOff ∗
          A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm3
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS (err := err) nofun nofun
        (decPkDef_pathB_remId_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_ne)
    have hpost_goal := exit_entails_dpPollPost_placed A lim DecPkEnv B S stk' hneed hstk63 y s0 sf
      (evs_p1 ++ evs_p2) StoresGhost.opened (.error err)
      (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins)
      (hevs_mismatch hrem_ne evs_p2 hevs_p2) hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm4
  · intro hrem_eq evs_p2 s2 g recG whisperMsgPtr whisperG preKeyMsgRem
      opkHi kyberPreKeyId signedPreKeyId hevs_p2 hwg_eq hex hmsg_fold hsteps12 hpc2 hrun2
      hs2_sp hsp_align2 htr2 _ _ _ hvregs2 _hro2
    have hfr2 : LibsignalFrozen lsmpl s2.mem :=
      libsignalFrozen_of_keepsFrozen hfr1 hsteps12.keepsFrozen
    subst hwg_eq
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error .panic →
        (dpSlotPollKStatePlaced A lim DecPkEnv B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathB_panic_pathB X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS htrusted hMatch hrem_eq hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
        (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
         ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
         memRegion (y.fut + 0x2a8#64) 4) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        (LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents evs_p2 (M.stepEvents evs_p1 y.st))
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
             ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
             memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem) ∗ F_p2 ⊢
        LsTokenInit ∗
          genP3Pre_placed A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
            s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 ∗
          F_p3 := by
      rw [← M.stepEvents_append evs_p1 evs_p2 y.st]
      dsimp only [F_p2, F_p3]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3 fun R_p3 hm_p3 hL_p3 => ?_
    have hgv : SessionGhostValid recG sess :=
      h8pb_sessionGhostValid_of_genP3Pre A lim (M.stepEvents (evs_p1 ++ evs_p2) y.st)
        s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
        (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 _ hex
        (Arm64.Satisfies.mono (by sep_frame) hm_p3)
    refine sepWPp_genP3_to_tailQpan_placed A lim DecPkEnv B S stk' y hpan_model ?_ R_p3 hm_p3 hL_p3
    refine stageP3PrevEmptyVRegs_of_base_full_placed_ok
      (M.stepEvents (evs_p1 ++ evs_p2) y.st)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      (StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hG)
      (h8pb_cliChainClone3_budget_placed_ok mmpl gh W hh)
      (h8pb_cliSenderChainClone3_budget_placed_ok mmpl gh W hh)
      hTryDec (h8pb_cliDropSessionStructure4_budget_placed_ok_at mmpl gh W hh)
      s0 s2 y.fut y.cx y.out 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      g recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message F_p3 _
      (hfits_p3 hrem_eq evs_p2 recG hevs_p2 hex hgv)
      (by decide) (Or.inr (distinctSid_of_decPkOkPathB hdecOk)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' evs_p3 pt ptCap ptPtr s' P_s' hver hcl hdec_rel hevs_p3 hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hro' hent_s'
      have hent_s'' :
          P_s' ⊢
            stageP3DispatchOkMidPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 s' y.fut y.out 8#64
              ptCap ptPtr g pt 0#8 G'
              (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).2 ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_s'
      exact h8pb_closure_pathB_p4_cont_pathB_placedBudget hDropNz mmpl gh W X B S Scope hh hReadFile hS stk' hneed hstk63
        y (hSkit y.g.F y.g.peer) sess ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 s'
        rngPtr whisperMsgPtr ptCap ptPtr y.g.msgG.msg preKeyMsgRem P_s' R
        opkHi kyberPreKeyId signedPreKeyId g recG G₁ G' pt
        hfPeer hdecOk hIn hloadS htrusted hMatch hrem_eq hex
        (hfits_p4 hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt hevs_p2 hex hgv hcl hdec_rel hevs_p3 hok)
        (fun evs_p4 hevs_p4 =>
          hevs_ok hrem_eq hver evs_p2 recG G₁ G' evs_p3 pt evs_p4
            hevs_p2 hex hgv hcl hdec_rel hevs_p3 hok hevs_p4)
        hmsg_fold hs2_files htr20 hs2_sp hsp_sub hsp_align2 hver hcl hdec_rel hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s''
    · intro G₁ G' evs_p3 e sf P_f hver hcl hdec_rel hevs_p3 herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out e ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message
              (coinsAfterPlaced y.g.coinsP y.g.coins
                (decryptDraws W.C sess.state y.g.msg.message.senderRatchetKey y.g.coins)) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf rngPtr whisperMsgPtr y.g.msgG.msg
        preKeyMsgRem _ P_f R opkHi kyberPreKeyId signedPreKeyId e
        (hevs_err hrem_eq hver evs_p2 recG G₁ G' evs_p3 e hevs_p2 hex hgv hcl hdec_rel hevs_p3 herr hne_p)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_err_pathB X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS htrusted hMatch hrem_eq hver herr hne_p)
        hent_f' hsf_sp htr_f hcs_f hvregs_f
    · intro evs_p3 sf P_f hver_ne hevs_p3 hent_f hsf_sp htr_f hcs_f hvregs_f _
      have hent_f' :
          P_f ⊢
            ((s2.sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
            memRegion (s2.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty_placed A lim
              (M.stepEvents ((evs_p1 ++ evs_p2) ++ evs_p3) y.st) s0 s2 sf y.fut y.out
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame_placed A.repAlloc s2.sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr
              (y.g.msg.message.messageVersion.zeroExtend 32) y.g.peer y.g.me y.g.msgG.msg
              y.g.msg.message (coinsAtPlaced y.g.coinsP y.g.coins) := by
        rw [M.stepEvents_append (evs_p1 ++ evs_p2) evs_p3 y.st]
        exact hent_f
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y ((evs_p1 ++ evs_p2) ++ evs_p3) s0 s2 sf rngPtr whisperMsgPtr y.g.msgG.msg
        preKeyMsgRem _ P_f R opkHi kyberPreKeyId signedPreKeyId
        (.invalidMessage .preKey .decryptionFailed)
        (hevs_verNe hrem_eq hver_ne evs_p2 recG evs_p3 hevs_p2 hex hgv hevs_p3)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_eq hver_ne)
        hent_f' hsf_sp htr_f hcs_f hvregs_f

private structure h8pb_DpPollEntryPurePathBFrozenPlacedBudget [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem} (stk' : Nat)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 : State) : Prop where
  fr : LibsignalFrozen lsmpl s0.mem
  ro : LibsignalCodeRoLoaded lsmpl s0.mem
  x0 : s0.readReg64 .x0 = y.out
  x1 : s0.readReg64 .x1 = y.fut
  x2 : s0.readReg64 .x2 = y.cx
  stk_le_sp : stk' ≤ s0.sp.toNat
  files_eq : s0.fs.files = y.g.F
  coins_lt : y.g.coins.length < 2 ^ 63
  filesOkPeer : FilesOkPeer Scope y.g.F y.g.peer.val
  decPkOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg
  fits : FitsEnv M lim y.st (DecPkEnv y.g)

private theorem h8pb_dpPollPre_unpack_pathB_frozen_placedBudget [LibsignalPlacement]
    {W : CliHooks} {X : UnreachedPqxdhPrimitives}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (stk' : Nat) (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State) (hpre : s0.mem ⊨
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R) :
    h8pb_DpPollEntryPurePathBFrozenPlacedBudget (X := X) (W := W) (Scope := Scope) stk' y s0 ∧
      (s0.mem ⊨ LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced stk' y s0 R) := by
  obtain ⟨hfr, hpre0⟩ := extract_withLsFrozen hpre
  have hro : LibsignalCodeRoLoaded lsmpl s0.mem :=
    CryptoVerification.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hfr
  have h2 : s0.mem ⊨
      ⌜s0.readReg64 .x0 = y.out ∧ s0.readReg64 .x1 = y.fut ∧ s0.readReg64 .x2 = y.cx ∧
        (dpSlotArgsPlaced y.g).length = 13 ∧ stk' ≤ s0.sp.toNat⌝ ∗ (memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ dpCxAt y.cx ∗
        (⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
            S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧ FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
          (⌜y.g.coins.length < 2 ^ 63⌝ ∗
            (storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗
              lsLogOff ∗
              A.pool lim y.st s0 ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗ R)))) := by
    simpa only [dpPollSpecStateBudget, dpSlotPollKStatePlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
      sepConj_assoc] using hpre0
  rw [satisfies_pure_sepConj] at h2
  rcases h2 with ⟨⟨hx0, hx1, hx2, _, hstk_sp⟩, h3⟩
  have h3' : s0.mem ⊨
      ⌜s0.fs.files = y.g.F ∧ S.filesOk y.g.F y.g.peer.val y.g.me.val ∧
          S.decPkOk y.g.F y.g.peer.val y.g.me.val y.g.msg ∧ FitsEnv M lim y.st (DecPkEnv y.g)⌝ ∗
        (⌜y.g.coins.length < 2 ^ 63⌝ ∗ (dpCxAt y.cx ∗ (memRegion y.out 48 ∗
              dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗
              storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
              protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
              protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
              coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗
              lsLogOff ∗
              A.pool lim y.st s0 ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
              stackAt s0.sp stk' ∗ R))) := by
    convert h3 using 1
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at h3'
  rcases h3' with ⟨⟨hfiles, hfOk, hdOk, hfits⟩, h4⟩
  rw [satisfies_pure_sepConj] at h4
  rcases h4 with ⟨hcoins_lt, h5⟩
  obtain ⟨hfPeer, hdecOk⟩ := hSemOk y.g.F y.g.peer.val y.g.me.val y.g.msg hfOk hdOk
  have h5_cx := Satisfies.mono (sepConj_mono_left (dpCxAt_entails_memRegion32 y.cx)) h5
  refine ⟨⟨hfr, hro, hx0, hx1, hx2, hstk_sp, hfiles, hcoins_lt, hfPeer, hdecOk, hfits⟩, ?_⟩
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced]
  convert h5_cx using 1
  sep_ac_rfl

private theorem h8pb_extHookStack_le_cliPollSess_loadCallStack [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    extHookStack ≤ loadCallStack (cliPollSessKitPlaced A F0 scopeKit peer (cliKitStk B)) := by
  dsimp only [extHookStack, loadCallStack, cliPollSessKitPlaced, cliPollSessKit,
    cliSessionStoreSpec, cliKitStk,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed,
    CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed,
    CryptoVerification.RustHeap.allocHookStack]
  omega

private theorem h8pb_closure_untrusted_pathB_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r) (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g))
    (hevs_sub : ∀ evs,
      CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs → DecPkEnv y.g evs)
    (R : SepProp) (s0 : State) (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = y.out) (hx1 : s0.readReg64 .x1 = y.fut)
    (hx2 : s0.readReg64 .x2 = y.cx) (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok false)
    (hm_base : s0.mem ⊨
      memRegion y.out 48 ∗ dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      LsTokenInit ∗ lsLogOff ∗ A.pool lim y.st s0 ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
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
  let sp := s0.sp - 0xcd0#64
  let hUntrusted : StageP1UntrustedMangledPlacedStmt := stageP1_untrusted_mangled_placed_ok
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB (A := A.repAlloc) σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗ lsLogOff ∗ A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1UntrustedCallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F scopeKit y.g.peer B
  have hp1_64 : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_untrusted s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗ memRegion (y.fut + 0x100#64) 336 ∗
    cells (y.fut + 0x250#64) 6 ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗
    ((y.fut + 0x390#64) ↦₈ b_390) ∗ ((y.fut + 0x398#64) ↦₆₄ u_398) ∗
    ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ (sp ↦₆₄ v_sp0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗ cells (sp + 0xa90#64) 6 ∗
    cells (s0.sp - 0x60#64) 12 ∗ memRegion y.out 48 ∗ lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim y.st s0 ∗
    stackAt sp (stageP1UntrustedCallStack kit ikit)
  let Fr_inner : SepProp :=
    cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗
    coroUnusedP1At y.fut ∗ closStackUnusedUntrustedAt sp ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hm_split : s0.mem ⊨ P_p1 ∗ (Fr_inner ∗ R) :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
      cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1, Fr_inner ∗ R, hm_split, ?_⟩
  have hwp := hUntrusted
    (M := M) (A := A) (lim := lim) (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Scope := scopeKit) (encRecord := encodeRecord)
    (kit := kit) (kitEnv := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
    (ikit := ikit) (ikitEnv := LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer B ReadEnv)
    (st := StoresGhost.opened.sessions) (ist := StoresGhost.opened.identity) (st_b := y.st)
    y.g.peer y.g.msg.identityKey
    hh.alloc
    hh.codecHooks.dealloc
    ((show withVmPreserved noAllocShimSpec = sessionShimBudgetSpec from rfl) ▸ hh.codecHooks.shim)
    hh.codecHooks.alloc
    (h8pb_hookSat_sessionMemcpyRegionBudget_of_codec hh.codecHooks.memcpy)
    (cliPollSess_vtablesPlacedOk (A := A.repAlloc) y.g.F scopeKit y.g.peer σ hDropNz)
    (cliPollId_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer σ hDropNz)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSess_kitPlacedOkSE mmpl gh W hDropNz hh hRead hDeser)
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollId_kitPlacedOkI mmpl gh W hDropNz hh hRead)
    hp1_64 (h8pb_extHookStack_le_cliPollSess_loadCallStack A.repAlloc B y.g.F y.g.peer) rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1 s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins v_sp0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390
    hro0 (cliPollStageP1_fsAt_placed (runHooks_to_stages hh) y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun (by simpa [State.spAligned] using hsp) rfl hx0 hx1 hx2
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.SepWPp.mono_post_panic ?_ ?_ hwp
  · rintro sf P_f ⟨⟨opt, evs, hevs_p1, hload, _, htr_evs, hent_f⟩, hspf, hcs, hvregs, _⟩
    refine ⟨?_, hspf, closureCalleeSaved_toCalleeSavedPreserved hcs hvregs⟩
    intro hsteps hmf
    have htr_eq : sf.trace = s0.trace := by
      simpa [kit, ikit, cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollSessKit,
        cliSessionStoreSpec, cliIdStoreSpecFullPlaced, cliIdStoreSpecFull,
        cliIdentityStoreSpec] using htr_evs
    have hloadRec : loadRec Scope y.g.F y.g.peer.val = .ok opt :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload
    have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none := by
      rw [hS]
      exact decPkDef_of_trust_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadRec (Or.inr htrusted)
    have hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) s0.trace sf.trace :=
      slotOutTr_of_err StoresGhost.opened s0.trace sf.trace nofun nofun hans
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_f) hmf
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf1
    rcases hmf1 with ⟨v_a8, v_b8, v_d0, hmf2⟩
    have hcoro := coro_of_p1_untrusted_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins b_4f2
    have hstk3280 := clos_stack_3280_of_p1_untrusted s0.sp s0
      0#64 v_a8 (y.fut + 0x390#64) v_b8 y.cx y.out v_d0
    have hres := apiDecResultAt_untrusted_entails_decResAt A.repAlloc y.out y.g.peer.val
    have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt
      (A := A.repAlloc) (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    let Leftover : SepProp :=
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
    have hmf_reord : sf.mem ⊨
        (apiDecResultAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
            pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          (((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs y.st) sf ∗ Leftover ∗
          (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
              (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
              (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
            memRegion (y.fut + 0xe0#64) 368 ∗ cells (y.fut + 0x250#64) 6 ∗
            ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
              (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
            ((y.fut + 0x390#64) ↦₈ 1#8) ∗ cells (y.fut + 0x398#64) 2 ∗
            cells (y.fut + 0x428#64) 8 ∗ cells (y.fut + 0x490#64) 4 ∗
            ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ coroUnusedP1At y.fut) ∗
          memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
                (dpClosSubStack B - stageP1UntrustedCallStack kit ikit) ∗
              stackAt sp (stageP1UntrustedCallStack kit ikit)) ∗
            ((sp ↦₆₄ 0#64) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
              ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
              ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
              ((sp + 0xd0#64) ↦₆₄ v_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
              memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
              cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
              closStackUnusedUntrustedAt sp))) ∗ R := by
      have htrust_id : (cliIdStoreSpecFullPlaced A.repAlloc cliIo.rd y.g.F cliWrOk y.g.peer
          (cliKitStk B).idTrustShim (cliKitStk B).idTrustPoll (cliKitStk B).idSaveShim
          (cliKitStk B).idSavePoll).trustUpdate StoresGhost.opened.identity y.g.peer.val
          y.g.msg.identityKey .receiving (.ok false) = StoresGhost.opened.identity := rfl
      dsimp only [Fr_inner, Leftover, cliPollStoresKitsAtPlaced,
        kit, ikit, pkKit, spkKit, kpkKit, pid, sid, kid, kbk, σ,
        cliPollSessKitPlaced, cliPollIdKitPlaced] at hmf2 ⊢
      rw [htrust_id] at hmf2
      refine Satisfies.mono ?_ hmf2
      sep_frame
    rw [← preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
        ← stackAt_subStack_split sp B (stageP1UntrustedCallStack kit ikit) hp1_le hsub64,
        show sp + 0xcd0#64 = s0.sp from sp_frame_sub_add s0.sp] at hmf_reord
    have hmf_folded : sf.mem ⊨
        (decResAt A.repAlloc y.out (.error (.untrustedIdentity y.g.peer.val)) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs y.st) sf ∗ Leftover ∗ dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280)) ∗ R :=
      Satisfies.mono (sepConj_mono_left
        (sepConj_mono hres (sepConj_mono hstores_back
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono hcoro
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk3280)))))))))))))
        hmf_reord
    dsimp only [sp] at hmf_folded
    rw [← stackAt_poll_entry_split s0.sp B stk' hneed hstk63] at hmf_folded
    have hpost := dpPollPost_of_decResAt_placed A lim DecPkEnv B S stk' y s0 sf evs
      StoresGhost.opened (.error (.untrustedIdentity y.g.peer.val)) Leftover
      hh (hevs_sub evs hevs_p1) hsteps htr_eq hout
    exact Satisfies.mono (sepConj_mono_left hpost) hmf_folded
  · intro _ _ hfalse _ _
    exact False.elim hfalse

private theorem h8pb_p1Ok_post_eq_stageP2PostP1At_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
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
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt Scope A.repAlloc y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ cells (y.fut + 0x398#64) 2 ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗ ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool lim st_b s1) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗ memRegion y.out 48) =
    stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope A.repAlloc y.fut opt := by
  dsimp only [stageP2PostP1At, LibsignalBinary.Heap.RustCliAllocBudget.atState,
    cliPollSessKitPlaced, cliPollIdKitPlaced, cliIdStoreSpecFullPlaced,
    cliPollPkKitPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
    cliPollSpkKitPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
    cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced,
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]
  sep_frame

private theorem h8pb_p1Ok_recombine_entails_stageP2_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st_b : M.σ) (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    let sp := s0.sp - 0xcd0#64
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
    (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
        (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
        (y.g.stores + 0x78#64) kpkKit.kpk_vt rngPtr ∗
      p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      processPrekeyInnerInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores ikit.id_vt (y.g.stores + 0xc8#64) pkKit.pk_vt
        (y.g.stores + 0x50#64) spkKit.spk_vt (y.g.stores + 0x78#64) kpkKit.kpk_vt ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ cells (y.fut + 0x398#64) 2 ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗ ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
      ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ lsLogOff ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗ ikit.identityAt y.g.stores
        (ikit.trustUpdate StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey
          .receiving (.ok true)) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim st_b s1 ∗
      stackAt sp (stageP1CallStack kit ikit)) ∗
    (memRegion (y.fut + 0x250#64) 48 ∗
      coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗ memRegion y.out 48 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP1CallStack kit ikit) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
      pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit) ⊢
    stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
    LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le : stageP1CallStack kit ikit ≤ dpClosSubStack B :=
    stageP1CallStack_le_subStack (A := A.repAlloc) 0#64 y.g.F scopeKit y.g.peer B
  have hstores_back := cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc)
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
    (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
  have hp1_eq := h8pb_p1Ok_post_eq_stageP2PostP1At_placedBudget (Scope := scopeKit)
    y st_b s0 s1 rngPtr v_a8 v_b8 v_d0 opt
  dsimp only at hp1_eq
  have hp1_ent := Entails.of_eq hp1_eq
  have hpm_ent := Entails.of_eq
    (preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg).symm
  have hstk_ent := Entails.of_eq
    (stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64).symm
  have h4 := sepConj_mono hp1_ent (sepConj_mono hstores_back (sepConj_mono hpm_ent hstk_ent))
  let Pass : SepProp :=
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit ∗ lsLogOff ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32
  refine Entails.trans ?_ (Entails.trans (sepConj_mono_left h4 : _ ∗ Pass ⊢ _ ∗ Pass) ?_)
  · dsimp only [cliPollId_trustUpdate_eq_placed, cliPollStoresKitsAtPlaced, Pass,
      sp, σ, pid, sid, kid, kbk, kit, ikit]
    sep_frame
  · dsimp only [Pass, sp, σ, kit, ikit]
    sep_frame

private theorem h8pb_sepWPp_bind_p1_false {prog : Program} {mid ret : BitVec 64}
    {s0 : State} {P P_p1 F : SepProp} {Q1 Q Qpan : State → SepProp → Prop}
    (hp1 : SepWPp prog mid s0 P_p1 Q1 (fun _ _ => False)) (hP : P = P_p1 ∗ F)
    (hnext : ∀ sm P_m, Steps prog s0 sm → sm.pc = mid → sm.status = .Running →
      Q1 sm P_m → SepWPp prog ret sm (P_m ∗ F) Q Qpan) :
    SepWPp prog ret s0 P Q Qpan := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hq1⟩ | ⟨_, _, _, hfalse⟩ |
    ⟨_, hoom⟩⟩ := hp1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm P_m hsteps hpcm hrunm hq1 R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact False.elim hfalse
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 800000 in
private theorem h8pb_closure_trusted_pathB_of_matched_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv)) (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r) (_hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (hfits_p1 : FitsEnv M lim y.st (StageP1OkEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
        StoresGhost.opened.sessions (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey))
    (R : SepProp) (s0 : State) (hpc : s0.pc = dpPollEntryPlaced) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hstk_sp : stk' ≤ s0.sp.toNat)
    (hro0 : LibsignalCodeRoLoaded lsmpl s0.mem) (hx0 : s0.readReg64 .x0 = y.out)
    (hx1 : s0.readReg64 .x1 = y.fut) (hx2 : s0.readReg64 .x2 = y.cx) (hfiles0 : s0.fs.files = y.g.F)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (_hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hm_base : s0.mem ⊨ LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced stk' y s0 R)
    (hMatched : ∀ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
        (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64), StageP1OkEnv
        (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
        StoresGhost.opened.sessions (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
        StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey evs_p1 →
      (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
        (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) →
      r.currentSession = some sess → Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 s1 →
      s1.trace = s0.trace → LibsignalCodeRoLoaded lsmpl s1.mem → s1.sp = s0.sp - 0xcd0#64 →
      dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat → s1.pc = dpPollEntryPlaced + 0x0868#64 →
      s1.status = .Running → (s1.sp &&& 15#64 == 0#64) = true →
      StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) →
      let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
      let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
      let sp := s0.sp - 0xcd0#64
      SepWPp prog (s0.readReg64 .x30) s1
        (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
         preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
         protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗ LsTokenInit ∗
         lsLogOff ∗ stackAt sp (dpClosSubStack B) ∗
         memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R))) :
    let prog := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
    let K := dpSlotPollKStatePlaced A lim DecPkEnv B S
    ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp prog (s0.readReg64 Reg.lr) s0 P
        (fun sf P_f =>
          (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).post y s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          Steps prog s0 sf → (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget K stk')).onPanic y s0 sf ∗ R)) := by
  dsimp only
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced] at hm_base
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
  let sp := s0.sp - 0xcd0#64
  have hsp_align0 : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned] using hsp
  have hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat :=
    (subStack_le_sp_of_dpPollNeed hneed hstk_sp).1
  have hent_stores := storesAt_opened_entails_cliPollStoresKitsAtPlaced_pathB (A := A.repAlloc) σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hm_stores : s0.mem ⊨
      memRegion y.out 48 ∗
        dpFutStartAt y.fut (dpSlotArgsPlaced y.g) ∗ memRegion y.cx 32 ∗
        cliPollStoresKitsAtPlaced A.repAlloc y.g.F scopeKit y.g.peer
          pid sid kid kbk σ y.g.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
        protocolAddressAt A.repAlloc y.g.me y.g.meA ∗ coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗ lsLogOff ∗ A.pool lim y.st s0 ∗
        preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ stackAt s0.sp stk' ∗ R :=
    Satisfies.mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hent_stores)))) hm_base
  have hsub64 : dpClosSubStack B ≤ 2 ^ 64 := by
    have := dpPollNeed_eq_frame_add_subStack B; omega
  have hp1_le := stageP1CallStack_le_subStack (A := A.repAlloc)
    0#64 y.g.F scopeKit y.g.peer B
  have hp1_64 : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans hp1_le hsub64
  rw [dpFutStartAt_split_for_p1_placed y.g y.fut,
      preKeyMsgAt_eq_idKey_sep A.repAlloc y.g.msgG y.g.msgA y.g.msg,
      stackAt_poll_entry_split s0.sp B stk' hneed hstk63,
      stackAt_subStack_split sp B (stageP1CallStack kit ikit) hp1_le hsub64,
      clos_stack_3280_split_for_p1_ok s0.sp] at hm_stores
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_stores
  rcases hm_stores with ⟨u_98, u_a0, u_a8, u_b0, u_b8, u_c0, u_c8, u_d0, v_sp0,
    b_4f2, u_3a0, u_398, b_390, coins, hm_flat⟩
  rw [← ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)] at hm_flat
  simp only [Nat.reduceMul] at hm_flat
  dsimp only [cliPollStoresKitsAtPlaced] at hm_flat
  let P_p1 : SepProp :=
    decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) kit.ss_vt y.g.stores ikit.id_vt
      (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
      (y.g.stores + 0x78#64) kpkKit.kpk_vt coins ∗
    cells (y.fut + 0x70#64) 14 ∗ cells (y.fut + 0xe0#64) 4 ∗ memRegion (y.fut + 0x100#64) 336 ∗
    ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ cells (y.fut + 0x2c8#64) 25 ∗ ((y.fut + 0x390#64) ↦₈ b_390) ∗
    ((y.fut + 0x398#64) ↦₆₄ u_398) ∗ ((y.fut + 0x3a0#64) ↦₆₄ u_3a0) ∗ cells (y.fut + 0x428#64) 8 ∗
    cells (y.fut + 0x490#64) 4 ∗ ((y.fut + 0x4f2#64) ↦₈ b_4f2) ∗ (sp ↦₆₄ v_sp0) ∗
    ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
    ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
    ((sp + 0xc8#64) ↦₆₄ u_c8) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x3e0#64) 368 ∗ cells (s0.sp - 0x60#64) 12 ∗ lsLogOff ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗ A.pool lim y.st s0 ∗
    stackAt sp (stageP1CallStack kit ikit)
  let Fr_inner : SepProp :=
    memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut ∗ closStackUnusedP1OkAt sp ∗
    memRegion y.out 48 ∗ memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
      (dpClosSubStack B - stageP1CallStack kit ikit) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    preKeyMsgRemIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  have hm_split : s0.mem ⊨ (P_p1 ∗ Fr_inner) ∗ R :=
    Satisfies.mono (by dsimp only [P_p1, Fr_inner, kit, ikit, pkKit, spkKit, kpkKit,
      cliPollSessKitPlaced, cliPollIdKitPlaced, cliPollPkKitPlaced, cliPollSpkKitPlaced,
      cliPollKpkKitPlaced, cliIdStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
      cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced]; sep_frame) hm_flat
  refine ⟨P_p1 ∗ Fr_inner, R, hm_split, ?_⟩
  have hwp := stageP1_ok_placed_inst hDropNz mmpl gh W B y.g.F y.g.peer y.g.msg.identityKey
    hh hReadFile hDeser y.st StoresGhost.opened.sessions StoresGhost.opened.identity hp1_64 rfl rfl
    (fun _ (h : (cliPollSessKit A.repAlloc 0#64 y.g.F scopeKit y.g.peer σ).loadRel
      StoresGhost.opened.sessions y.g.peer.val _) => cliSess_loadRel_isOk h)
    (fun _ (h : (cliPollIdKit A.repAlloc 0#64 y.g.F y.g.peer σ).trustRel
      StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey .receiving _) =>
      cliId_trustRel_eq_of_trusted htrusted h)
    hfits_p1 s0 sp y.out y.fut y.cx y.g.msgA y.g.peerA y.g.meA (y.g.stores + 0xf0#64) y.g.stores
    (y.g.stores + 0xc8#64) pkKit.pk_vt (y.g.stores + 0x50#64) spkKit.spk_vt
    (y.g.stores + 0x78#64) kpkKit.kpk_vt coins
    v_sp0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 b_390 b_4f2 hro0
    (cliPollStageP1_fsAt_placed hh y.g.F scopeKit y.g.peer B hfiles0)
    hpc hrun hsp_align0 rfl hx0 hx1 hx2
  refine h8pb_sepWPp_bind_p1_false hwp rfl ?_
  intro s1 P_1 hsteps01 hpc1 hrun1 hq1
  rcases hq1 with ⟨⟨opt, evs_p1, hevs_p1, hload_rel, _htrust_rel, htr_evs, hent_1⟩,
    hs1_sp, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
    hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1, hro1⟩
  have htr1 : s1.trace = s0.trace := CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP1Ok_trace_eq_placed htr_evs
  have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true :=
    hs1_sp ▸ sp_sub_cd0_align_std3 hsp_align0
  have hregs1 : StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64)
      (lsρ cliKyberPreKeyVtSym) :=
    ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
     hx19, hx20, hx22, hx23, hx24, hx25, hx28, hx29, hvregs1⟩
  refine sepWPp_conseq_pre (sepConj_mono_left hent_1) ?_
  simp only [sepExists_sepConj_left]
  refine sepWPp_sepExists_left fun v_a8 =>
    sepWPp_sepExists_left fun v_b8 =>
    sepWPp_sepExists_left fun v_d0 => ?_
  have hrecomb := h8pb_p1Ok_recombine_entails_stageP2_placedBudget stk' hneed hstk63 y
    (M.stepEvents evs_p1 y.st) s0 s1 coins v_a8 v_b8 v_d0 opt
  dsimp only at hrecomb
  refine sepWPp_conseq_pre hrecomb ?_
  cases opt with
  | none =>
    have hload0 : loadRec Scope y.g.F y.g.peer.val = .ok none :=
      loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
    obtain ⟨_, hloadS, _⟩ := hdecOk.loadedMatch
    rw [hload0] at hloadS; cases hloadS
  | some r =>
    obtain ⟨sess, hcur⟩ := CryptoVerification.SignalSession.Cli.RunProofs.Poll.currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
    exact hMatched r sess evs_p1 s1 coins v_a8 v_b8 v_d0 hevs_p1 hload_rel hcur hsteps01 htr1 hro1
      hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

private theorem h8pb_decPk_matchingPathB_poll_gv_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    {gh : CliGhostHooks}
    (hG : CliGhostAllocHooks M A lim gh)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    {kitEnv4 : ∀ F0 peer, SessionStoreBudgetEnv
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hReadFile : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hSemOk : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      MatchingPathBGvPollEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv g evs → DecPkEnv g evs)
    (stk' : Nat) (hneed : (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk')
    (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')) := by
  have hneed' : dpPollNeed B ≤ stk' := hneed
  apply subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hpure, hm_base⟩ :=
    h8pb_dpPollPre_unpack_pathB_frozen_placedBudget (W := W) (X := X) (Scope := Scope) hSemOk stk' y R s0 hpre
  have hfits_poll : FitsEnv M lim y.st
      (MatchingPathBGvPollEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv y.g) :=
    hpure.fits.mono (hevs_sub y.g)
  obtain ⟨b, htrusted⟩ :=
    trusted_ok_of_filesOkPeer (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntryPlacedBudget.dpPollEntrySpatialPlaced] at hm_base
    have hfits_u : FitsEnv M lim y.st (CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g) :=
      hfits_poll.mono (fun evs h => by simp [MatchingPathBGvPollEnv, htrusted, h])
    have hevs_u : ∀ evs, CliDpPollUntrustedEnv (A := A.repAlloc) B ReadEnv DeserEnv y.g evs →
        DecPkEnv y.g evs := fun evs h =>
      hevs_sub y.g evs (by simp [MatchingPathBGvPollEnv, htrusted, h])
    exact h8pb_closure_untrusted_pathB_placedBudget A lim hDropNz mmpl gh W X B S Scope hh hReadFile hDeser
      hinjK hsub hS stk' hneed' hstk63 y hfits_u hevs_u R s0 hpc hrun hsp
      hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.decPkOk
      htrusted hm_base
  | true =>
    have hh_st := runHooks_to_stages hh
    have hne_false :
        StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val y.g.msg.identityKey ≠ .ok false := by
      rw [htrusted]; decide
    have hfits_seq : FitsEnv M lim y.st
        (SeqEnv
          (StageP1OkEnv
            (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
            (cliPollSessBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) DeserEnv ReadEnv)
            StoresGhost.opened.sessions
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
            (cliPollIdBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
            StoresGhost.opened.identity y.g.peer.val y.g.msg.identityKey)
          (fun evs234 =>
            ∃ r sess,
              (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)).loadRel
                StoresGhost.opened.sessions y.g.peer.val (.ok (some r)) ∧
              r.currentSession = some sess ∧
              MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess evs234)) :=
      hfits_poll.mono (fun evs h => by simpa [MatchingPathBGvPollEnv, hne_false] using h)
    refine h8pb_closure_trusted_pathB_of_matched_placedBudget hDropNz mmpl gh W X B S Scope hh_st hReadFile
      hDeser hinjK hsub hS stk' hneed' hstk63 y hfits_seq.seq_left R s0 hpc hrun hsp
      hpure.stk_le_sp hpure.ro hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer
      hpure.decPkOk hpure.coins_lt htrusted hm_base ?_
    intro r sess evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hevs_p1 hload_rel hcur hsteps01 htr1 hro1
      hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
    have hfits_main : FitsEnv M lim (M.stepEvents evs_p1 y.st)
        (MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess) := by
      intro evs234 hmain
      exact ((LibsignalBinary.Heap.fitsEvents_append M lim evs_p1 evs234 y.st).mp
        (hfits_seq (evs_p1 ++ evs234) (LibsignalBinary.Heap.SeqEnv.append hevs_p1 ⟨r, sess, hload_rel, hcur, hmain⟩))).2
    have hevs_main : ∀ evs234,
        MatchingPathBGvMainEnv A.repAlloc W B ReadEnv kitEnv4 tdEnv y.g sess evs234 →
        DecPkEnv y.g (evs_p1 ++ evs234) := by
      intro evs234 hmain
      apply hevs_sub y.g (evs_p1 ++ evs234)
      simp only [MatchingPathBGvPollEnv, hne_false, ↓reduceIte]
      exact LibsignalBinary.Heap.SeqEnv.append hevs_p1 ⟨r, sess, hload_rel, hcur, hmain⟩
    have hfr1 : LibsignalFrozen lsmpl s1.mem :=
      libsignalFrozen_of_keepsFrozen hpure.fr hsteps01.keepsFrozen
    exact h8pb_decPk_matchingPathB_main_gv_frozen_placedBudget hG hDropNz mmpl W X B S Scope
      hh_st hReadFile hDeser hSkit hTryDec hinjK hsub hS stk' hneed' hstk63 y evs_p1 r sess s0 s1
      rngPtr v_a8 v_b8 v_d0 R hpure.files_eq hpure.filesOkPeer hpure.decPkOk hpure.coins_lt
      htrusted hload_rel hcur hfits_main hevs_main hsteps01 htr1 hfr1 hro1 hs1_sp hsp_sub hpc1 hrun1
      hsp_align1 hregs1

private theorem h8pb_toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private theorem h8pb_withPanics_cliGhostExterns_eq (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) =
      cliGhostExterns gh (cliExternsPlaced mmpl W) :=
  withPanics_cliGhostExterns mmpl gh W

private theorem h8pb_cliDecryptPrekey_slot_matchingPathB_gv_frozen_placedBudget_at_block [LibsignalFullPlacement]
    {M : AllocCostModel} {prog : Program} {i : Nat}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (B : RunBudgets)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {kitEnv4 : ∀ F0 peer,
      SessionStoreBudgetEnv (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [hcaller : IsLsBlockProg prog i (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hi : i < 619)
    (X : UnreachedPqxdhPrimitives) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hG : CliGhostAllocHooks M A lim gh)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSkit : ∀ F0 peer, SessionOnlyKitPlacedOkSE A lim
      (cliPollSessKitPlaced A.repAlloc F0 scopeKit peer (cliKitStk B))
      (kitEnv4 F0 peer) scopeKit encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkOkPathB ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hevs_sub : ∀ g evs,
      DecPkD3MatchingPathBGvEnv A.repAlloc W B ReadEnv DeserEnv kitEnv4 tdEnv g evs →
      DecPkEnv g evs)
    (stk : Nat) (hstk : cliDecryptPrekeyNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok prog (lsmpl.base 520) (decPkSlotSpecFrozenPlaced A lim DecPkEnv S stk) := by
  have : IsLsBlockProg prog i (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
    rw [h8pb_withPanics_cliGhostExterns_eq mmpl gh W]
    exact hcaller
  exact dpSlot_ok_state_frozen_placed B S stk hstk hstk64
    (cliDecryptPrekey_ok_state_frozen_placed_at_block (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
      (dpSlotPollKStatePlaced A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_inv_vm A lim DecPkEnv B S)
      (dpSlotPollKStatePlaced_res_vm A lim DecPkEnv B S)
      (fun stk' h1 h2 => by
        rw [h8pb_withPanics_cliGhostExterns_eq mmpl gh W]
        exact h8pb_decPk_matchingPathB_poll_gv_frozen_placedBudget A lim ReadEnv DeserEnv tdEnv DecPkEnv
          hG hDropNz mmpl W X B S Scope
          (h8pb_toSkeletonRunHooks hh) hRead hDeser hSkit hTryDec hinjK hsub hS hok hevs_sub
          stk' h1 h2)
      stk
      (by simp only [dpWrapFrame, dpPollNeed, cliDecryptPrekeyNeed,
        dpSlotPollKStatePlaced] at hstk ⊢; omega)
      hstk64 hi)

private theorem h8pb_decPkPathBSlotOk_gvSeqFree_frozen_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hG : CliGhostAllocHooks M A lim gh)
    (h547 : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets_placed.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim SessDeserializeCancelEnv))
    (hTryDec : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 508)
      (withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C A lim 0#64 uuidTryParse (spqrV1 W.C.F W.Q.K) tdEnv)))
    (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds)
    (hsEnv : ∀ g evs,
      DecPkD3MatchingPathBGvSeqFreeOfReadEnv A.repAlloc W cliRunBudgets_placed ReadEnv tdEnv g evs →
      sEnvs.decryptPrekey g evs)
    (hfiles : S.filesOk = filesOk₀ scopeIn (fun _ => True))
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hdecPkOk : ∀ F peer me pm, S.decPkOk F peer me pm →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn F peer me pm)
    (hneed : needs.decryptPrekey = cliDecryptPrekeyNeed cliRunBudgets_placed) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs).decryptPrekey.OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 520) :=
  fun stk h1 h2 =>
    h8pb_cliDecryptPrekey_slot_matchingPathB_gv_frozen_placedBudget_at_block
      (prog := lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 579)
      A lim cliRunBudgets_placed mmpl gh W (by decide) X S scopeIn
      hG h547 hh hRead hDeser
      (fun F0 peer => cliPollSess_seqFreeKitPlacedOkSE mmpl gh W cliRunBudgets_placed F0 peer h547 hh hRead hDeser)
      hTryDec
      encodeInjOn_deserializeScopeP_Q (fun _ h => h) hdecPk
      (fun F peer me pm hf hd => ⟨(hfiles ▸ hf).1, hdecPkOk F peer me pm hd⟩)
      hsEnv stk (hneed ▸ h1) h2

end FrozenPathBGvSeqFree

/-! ## Guarded Block-520 Slot Adapter on `cliRunSemPathB` -/

private theorem h8pb_slotOk_guarded_of_unguarded [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv₀ : DecPkGhost → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (hsEnv : sEnvs.decryptPrekey = realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W)
    (hUnguarded :
      (slotsOfSigPkFrozenPlaced A lim { sEnvs with decryptPrekey := DecPkEnv₀ }
        (cliRunSemPathB X W) needs).decryptPrekey.OkPlaced prog entry)
    (hBridge : ∀ x evs,
      FilesOkPeer scopeIn x.F x.peer.val →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn x.F x.peer.val x.me.val x.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      DecPkEnv₀ x evs →
      realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' X W x evs) :
    (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W) needs).decryptPrekey.OkPlaced prog entry := by
  intro stk hstk1 hstk2
  have hSub0 := hUnguarded stk hstk1 hstk2
  dsimp only [slotsOfSigPkFrozenPlaced, mkSlot] at hSub0 ⊢
  rw [hsEnv]
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hrest⟩ := hpre
  by_cases hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
  · have hdOk' : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn x.F x.peer.val x.me.val x.msg :=
      ⟨hdOk.party, hdOk.loadedMatch, hdOk.keyPairLt, hdOk.preKeysWf, hdOk.baseKeysLt⟩
    have hImp : ∀ evs, DecPkEnv₀ x evs →
        realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W x evs :=
      fun evs hevs0 _ => hBridge x evs hfOk.1 hdOk' hTight hevs0
    have hfit0 : FitsEnv M lim st (DecPkEnv₀ x) :=
      fun evs hevs0 => hfit evs (hImp evs hevs0)
    have hpre1 :
        s0.mem ⊨
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced
            A lim DecPkEnv₀ (cliRunSemPathB X W) stk).pre (x, st) s0 ∗ R := by
      dsimp only [
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced]
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit0⟩,
        hrest⟩
    refine hSub0.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hp | hex | ho
    · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
      dsimp only [
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
        CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
      refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
      refine Entails.sepExists_elim fun g' => Entails.sepExists_right g' ?_
      refine Entails.sepExists_elim fun e => Entails.sepExists_right e ?_
      refine Entails.pure_left fun ⟨hevs0, htr, hout_e⟩ => ?_
      have hPure :
          (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W x evs ∧ slotTrace s0 sf ∧
            slotOut ((cliRunSemPathB X W).decryptPrekey x.F x.peer.val x.me.val x.msg x.coins)
              g' e s0 sf) = True :=
        propext ⟨fun _ => trivial, fun _ => ⟨hImp evs hevs0, htr, hout_e⟩⟩
      rw [hPure, pure_true, emp_sepConj]
      exact Entails.refl _
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr ho))
  · exfalso
    refine not_fitsEnv_top M lim st (fun evs _ => ?_)
    exact hfit evs (fun h => False.elim (hTight h))

/-! ## `Dom0` `SingleSlotFineSpec` Witness -/

private def h8pb_decPkDom0_singleSlot [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
    (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    (hpk : (cliRunSemPathB X W).pksmParse rest = some pm) :
    SingleSlotFineSpec
      (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W (r3bDecPkGhost g meV peerV pm)) :=
  let hi_dom : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i :=
    hi_g.elim Or.inl Or.inr
  let S4 := w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec' (P := ⟨W.C, W.Q⟩) (c := .recv peerV)
    (i := g.i) hi_dom
  have hSub : ∀ evs,
      realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W (r3bDecPkGhost g meV peerV pm) evs →
      ∃ w : W4BinaryRecvPrekeyParamsCmk,
        W4BinaryRecvPrekeyDomCmk0
          w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps
          (.recv peerV) g.i w ∧
        W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
          w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w evs := by
    intro evs hevs
    have hp640 : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerV) :=
      peerSpqrStateTight640_of_cliPqOrD3Recv hi_dom hp
    have hpk' : pksmParse rest = some pm := hpk
    have hct_cap : pm.message.ciphertext.length ≤ msgCapBytes :=
      Nat.le_trans (pksmParse_lengths_le hpk').2.2.1
        (recv_rest_length_le_msgCapBytes hin hc hst)
    obtain ⟨w4, hcs0, _hik, _hbk, henv⟩ := hevs hp640
    have hdom0 :=
      W4BinaryCallSiteDomCmk0.toCmkDom0Of
        w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps hcs0 hp hct_cap
    have hdom4 :
        W4BinaryRecvPrekeyDomCmk0
          w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps
          (.recv peerV) g.i w4 := by
      intro pAddr hpAddr
      injection hpAddr with hpEq
      subst hpEq
      exact ⟨hcs0.1.eq_peerVal, hdom0.1.outer_dom.peer_len, hcs0.1.eq_files, hcs0.1.eq_rd, hdom0⟩
    exact ⟨w4, hdom4, henv⟩
  { cum := w4CmkDom0Cum
    live := w4CmkDom0Live
    peak := w4CmkDom0Peak
    maxReq := w4CmkDom0MaxReq
    grpS := w4CmkDom0GrpS109
    credit := PhaseCreditSpec.of_imp hSub S4.credit
    live_le_peak := w4CmkDom0_live_le_peak
    groups := PhaseGroupSpec.of_imp (w4CmkDom0GrpSOf_109_eq ▸ S4.groups) hSub }

/-! ## Top-Level `MainOkPathBD3F3` Assembly -/

/-- Establishes `MainOkPathBD3F3` on `cliElfBytes` from unbundled ghost-witness field hypotheses. -/
theorem hole_m24slot_pathB_assembly_closed
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (ghFixed : CliGhostHooks)
    (hookStack : Nat)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hMainStk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk)
    (hTrFrozen : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostSpqrAllocHooks fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hReadSat : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hHooksBundle : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (hSpqr : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    MainOkPathBD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  have _ := hSpqr
  let DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop :=
    fun X W _γ _tp =>
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W
  have hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits ghFixed := by
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    exact fun γ tp => (hGSpqr γ tp).toCliGhostAllocHooks
  refine h9r2_pathB_assembly_honest_d2cSlots_of_dom0_singleSlot
    hLs hblk hext_nodup ghFixed (default : Image)
    (fun [LibsignalPlacement] {_M'} W A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun [LibsignalPlacement] {_M'} W A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    cliRunBudgets DecPkSlotEnv
    (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets)
    w4CmkDom0Cum w4CmkDom0Live w4CmkDom0Peak w4CmkDom0MaxReq w4CmkDom0GrpS109
    rfl hTrFrozen hG hioOf hMainStk (fun _ => hHooksBundle)
    (fun W γ tp g peerV peerG meG fsp hp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact hole3_encEnv_r2_congr W
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) g peerV peerG meG fsp hp)
    (fun W γ tp g fsp w peerV meG msgG m => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact hole3_decSigEnv_r3a_congr W
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) g fsp w peerV meG msgG m)
    (fun X W _γ _tp x y hp hm hs hcp hf hc hmsg => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed_ghost_congr
        w4c_repairedStatesRecvEnvFam X W x y hp hm hs hcp hf hc hmsg)
    (fun h547 X W γ tp =>
      hole3_w1_inner hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
        (hGSpqr γ tp) hFs (hReadSat W γ tp) (hHooksBundle W γ tp) h547)
    (fun h547 X W γ tp =>
      hole3_w2_inner hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
        (hGSpqr γ tp) hFs (hReadSat W γ tp) (hHooksBundle W γ tp) h547)
    (fun h547 X W γ tp =>
      hole3_w3_init hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
        (hGSpqr γ tp) hFs (hReadSat W γ tp) hghNoAlloc (hHooksBundle W γ tp) h547)
    (by decide)
    (fun h547 X W γ tp => ?_)
    (fun _h547 W g peerV M' A' w1R hi hp hc hrep hdom => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have heq : cliEncryptBinaryKitSlotEnvExact W A' w1R.B =
          ckx2_cliEncryptBinaryKitSlotEnvExact W A' w1R.B :=
        congrArg
          (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A' w1R.B)
          (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w1EncExact_phaseCredit W g peerV M' A' w1R hi hp hc hrep hdom)
    (fun _h547 W g peerV M' A' w1R hi hp hc hrep hdom => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have heq : cliEncryptBinaryKitSlotEnvExact W A' w1R.B =
          ckx2_cliEncryptBinaryKitSlotEnvExact W A' w1R.B :=
        congrArg
          (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A' w1R.B)
          (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w1EncExact_groupSpec W g peerV M' A' w1R hi hp hc hrep hdom)
    (fun _h547 W g peerV M' A' w2R hi hp hc hrep hdom => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have heq : cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B =
          ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B :=
        congrArg
          (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A' w2R.B)
          (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact fits2_w2DecSigExact_phaseCredit W g peerV M' A' w2R hi hp hc hrep hdom)
    (fun _h547 W g peerV M' A' w2R hi hp hc hrep hdom => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      have heq : cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B =
          ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B :=
        congrArg
          (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A' w2R.B)
          (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact fits2_w2DecSigExact_groupSpec W g peerV M' A' w2R hi hp hc hrep hdom)
    (fun _h547 X W _γ _tp g meV peerV rest pm hi_g hp hin hc hst hpk => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      exact h8pb_decPkDom0_singleSlot X W g meV peerV rest pm hi_g hp hin hc hst hpk)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    w4CmkDom0_live_le_peak
    (by unfold d3SlotMainFitsOneGiBOf; decide)
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let sEnvs := h9r2_honestD3FineSlotEnvs hblk hext_nodup
    (fun [LibsignalPlacement] {_M'} W A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun [LibsignalPlacement] {_M'} W A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    mmpl cliElfImage.brkStart cliRunBudgets DecPkSlotEnv X W γ tp
  let DecPkEnv₀ := DecPkD3MatchingPathBGvSeqFreeOfReadEnv A.repAlloc W cliRunBudgets_placed
    (ReadFileRuleEnvFixed cliIo.rd) (w4s2_TryDecryptTopStateGuardedEnv W)
  obtain ⟨hReadPoll, hDeserPoll⟩ :=
    h9g_poll_readFile_and_sessDeser_of_hooks mmpl ghFixed W (hG γ tp) (hReadSat W γ tp)
  have hHooksP := (hHooksBundle W γ tp).runHooks
  have hhClosure :
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
        A cliBudgetLimits (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) :=
    { alloc := hHooksP.alloc, allocFs := hHooksP.allocFs, panics := hHooksP.panics,
      memcpyRO := hHooksP.memcpyRO, bcmp := hHooksP.bcmp, fs := hHooksP.fs,
      utf8 := hHooksP.utf8, memrchr := hHooksP.memrchr, codecHooks := hHooksP.codecHooks,
      allocZeroed := hHooksP.allocZeroed, stringClone := hHooksP.stringClone,
      formatInner := hHooksP.formatInner }
  have hAesDec :=
    fineAesDec_budget_hookOk γ tp cliElfImage.brkStart cliBudgetLimits hPl_mng W.C.D
  have hSpqrTop :=
    w4s2_spqrSeams_topStateGuarded mmpl ghFixed hPl_mng W γ tp cliElfImage.brkStart (hGSpqr γ tp)
  have hTryDec :=
    cli_tryDecrypt_of_tdEnv_at_518 (tdEnv := w4s2_TryDecryptTopStateGuardedEnv)
      mmpl ghFixed W 0#64 (hG γ tp) hAesDec hSpqrTop
      (w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty W.C.F W.Q.K)
      (fun _ _ h => h)
  have hSlot0 :
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits { sEnvs with decryptPrekey := DecPkEnv₀ }
        (cliRunSemPathB X W) (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520) :=
    h8pb_decPkPathBSlotOk_gvSeqFree_frozen_placedBudget X mmpl ghFixed W (hG γ tp)
      h547 hhClosure hReadPoll hDeserPoll hTryDec
      (cliRunSemPathB X W) { sEnvs with decryptPrekey := DecPkEnv₀ }
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets))
      (fun _ _ h => h) rfl rfl
      (fun _ _ _ _ hd => ⟨hd.party, hd.loadedMatch, hd.keyPairLt, hd.preKeysWf, hd.baseKeysLt⟩) rfl
  exact h8pb_slotOk_guarded_of_unguarded rfl hSlot0
    (fun x evs hfPeer hdecOk hTight hevs0 =>
      h8pb_gvSeqFree_sub_cmkDom0' A.repAlloc X W hfPeer hdecOk hTight hevs0)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinPathB
