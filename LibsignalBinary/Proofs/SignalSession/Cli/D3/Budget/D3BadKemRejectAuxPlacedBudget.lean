/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3RejectPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2ArmsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemRejectPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPathAPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux

/-!
# Budget-Threaded Stage-P2 and Poll Bad-KEM Rejection

Proves spatial entry/exit bridges, the block-`75` (`initialize_bob_session`) bad-KEM owned-error
contract on `stageP1ProgPlaced`, and `[LibsignalFullPlacement]` Stage-P2 and poll (`dpPollProgPlaced`)
rejection theorems for `MsgCondBadKem`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSessionApi (ApiError KyberPayload PreKeySignalMessage Session SessionRecord)
open CryptoVerification (LibsignalFrozen LibsignalFullPlacement LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (StageP2MemInv hdrOpkIdBv? p1LoadedRecordAt p2_bobStack_le_v1CallStack p2_callStack_le_v1CallStack
   p2_sub56Stack_le_v1CallStack stageP1ProgPlaced)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (p2_over_baseV1Call_le_v1CallStack p2_over_callStack_le_v1CallStack p2_over_dropSS3_le_overPure
   p2_over_pure_le_v1CallStack stageP2OverCallStack4K_eq)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives modelPrims vecU8)
open CryptoVerification.E2E.Pqxdh.Initiator
  (AcceptKeysInput Primitives WellSizedAcceptKeysInput bytesToBv8 dhOptNonZero)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroInitAt processPrekeyPostTrustAt)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bytesToBv8_vecU8 ofSignalPqxdhPrimitives vecU8_length)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt FsFiles speWordsAt withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost preKeyMsgAt)
open CryptoVerification.LibsignalTripleRatchet
  (framelessMemcpySpec lsRustNoAllocShimSym noAllocShimSpec sessionMemcpySpec withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost protocolAddressAt)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsMemcpySym lsReadFileSym)
open CryptoVerification.SignalSession.Cli
  (StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt dpPollNeed)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunProofs (dpFutDoneAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (LsTokenInit PathAEntryWords StageP1PostRegs calleeSavedPreserved_of_closure cliKitStk
   cliPollIdKitPlaced cliPollKpkKitPlaced cliPollKpk_vtablesPlacedOk cliPollPkKitPlaced
   cliPollPk_vtablesPlacedOk cliPollSelfKitPlaced cliPollSelf_vtablesPlacedOk cliPollSessKitPlaced
   cliPollSpkKitPlaced cliPollSpk_vtablesPlacedOk coroCopyTail11At dpClosSubStack dpPollEntryPlaced
   dpPollProgPlaced pmKyberId pmPreKeyId processPrekeyInnerRem23At sepWPp_conseq_pre
   signalMessageRestVerAt sp550P2V1RemAt spMidGapsAt sp_frame_sub_add stageP2PostP1At)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (EncodeInjOn FilesOkPeer blackBox_row_placed loadRec scopeIn scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
  (StageP2BaseCalleesPlaced4K StageP2PureCalleesPlaced4KOfEnv VacuousBobAllocEnv
   initializeBobSessionErr4KInnerPlacedSpec initializeBobSessionErr4KPlacedSpec
   not_fitsEnv_vacuousBobAllocEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
  (P2Sub1To3Arm1Env P2Sub1To3Arm2Env P2Sub1To4Arm3Env P2Sub1To4Env P2Sub1To4OkEnv P2Sub4OkEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
  (StageP2BaseCalleesPlaced4K.of_hooks isSameAccount_4k_placed_ok_on_stageP1)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
  (isSameAccountDistinctSpecExt_to_at_placed)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
  (P2V1Arm4Env P2V1Arm5EnvOfAcceptErr)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget
  (P2OverSub1To3Arm1Env P2OverSub1To3Arm2Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget
  (P2OverSub1To4Arm3Env P2OverSub1To4Env P2OverSub1To4OkEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
  (P2OverV1Arm4Env P2OverV1Arm5EnvOfAcceptErr)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (MsgCondBadKem badKemMsgRemInnerAt badKemSpeWords_entails_decResAt_anyHeap
   bytesToBv8_mkBadKemHdr_ekAPk cliPollKpk_getEvs_nil cliPollPk_getEvs_nil cliPollPk_opkOkEvs_nil
   cliPollPk_opkOkUpdate_eq cliPollSelf_kpEvs_nil cliPollSpk_getEvs_nil
   distinctSid_of_not_sameAcct_d3 hdrOpkIdBv?_mkBadKemHdr mkBadKemHdr
   not_p2SessMatchesMsg_of_v4_badKem pqxdhBadKemErrPayloadAt
   stageP1ProgPlaced_eq_dpPollProgPlaced stageP2OverV1CallStack_le_subStack_badKem_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedPollEnv PqxdhAcceptBadKemErrEnv StageP2BadKemRejectEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget
  (DecPkStoreOk d3_pollPost_of_stageP2_err_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudgetAuxA
  (acceptBadKemEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudgetAux
  (cliStageP2ClosureHooksPlaced uuidTryParse_placed_vm_code_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
  (cliPollSelfBudgetEnv cliPollSelf_kitPlacedOk_stagesHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
  (cliPollKpk_wf_of_preKeysWf_placed cliPollPk_wf_of_preKeysWf_placed cliPollSelf_kpRel_ok_placed
   cliPollSpk_wf_of_preKeysWf_placed sepWPp_with_steps)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
  (cliPollKpk_getErr_entails_decResAt_anyHeap_placed cliPollPk_getErr_entails_decResAt_anyHeap_placed
   cliPollSelf_kpErr_entails_decResAt_err_placed cliPollSpk_getErr_entails_decResAt_anyHeap_placed
   cliPollStageP2_fsAt_stages_placed stageP2V1CallStack_le_subStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
  (cliPollKpkFullBudgetEnv cliPollKpk_kitPlacedOk cliPollPkFullBudgetEnv cliPollPk_kitPlacedOk
   cliPollSpkFullBudgetEnv cliPollSpk_kitPlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_framelessMemcpy_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)

/-- Spatial inner frame preserved across Stage-P2 bad-KEM Path-A and Over-Path-C runs under
`A.repAlloc`. -/
def badKemInnerFramePlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kp : KyberPayload) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B)).storeAt
    (y.g.stores + 240#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
  dirAt A.repAlloc (y.g.stores + 280#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym)
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
  memRegion (y.fut + 640#64) 24 ∗ memRegion (y.fut + 684#64) 8 ∗
  memRegion (y.fut + 692#64) 12 ∗ memRegion (y.fut + 705#64) 7 ∗
  memRegion (y.fut + 913#64) 7 ∗ memRegion (y.fut + 1267#64) 5 ∗
  memRegion (y.fut + 1922#64) 6 ∗
  (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 120 ∗ memRegion (sp + 216#64) 348 ∗
  memRegion (sp + 592#64) 20 ∗ memRegion (sp + 633#64) 39 ∗
  memRegion (sp + 688#64) 36 ∗ memRegion (sp + 736#64) 36 ∗
  memRegion (sp + 784#64) 36 ∗ memRegion (sp + 832#64) 36 ∗
  spMidGapsAt sp ∗ sp550P2V1RemAt sp ∗
  signalMessageRestVerAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
  (⌜y.g.msgG.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
    (if kp.ciphertext = [] then emp else A.repAlloc.live y.g.msgG.kyberPtr kp.ciphertext.length 1) ∗
    memRegion (y.g.msgA + 164#64) 4 ∗
    CryptoVerification.LibsignalTripleRatchetRepr.boxU8At A.repAlloc
      (y.g.msgA + 128#64) y.g.msgG.serPtr y.g.msg.serialized ∗
    memRegion (y.g.msgA + 241#64) 7)

/-- Every deterministic `acceptBadKemEvents P inp` trace lies in `PqxdhAcceptBadKemErrEnv`. -/
theorem acceptBadKemEvents_mem_pqxdhAcceptBadKemErrEnv
    (P : Primitives) (inp : AcceptKeysInput) :
    PqxdhAcceptBadKemErrEnv (acceptBadKemEvents P inp) := by
  unfold PqxdhAcceptBadKemErrEnv acceptBadKemEvents
  dsimp only
  cases hcanon : P.isCanonical inp.hdr.ekAPk
  · simp only [Bool.not_false, ↓reduceIte]; exact Or.inl rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hd1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0
    · simp only [hd1, ↓reduceIte]; exact Or.inr (Or.inl rfl)
    · simp only [hd1, ↓reduceIte]
      by_cases hd2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0
      · simp only [hd2, ↓reduceIte]; exact Or.inr (Or.inr (Or.inl rfl))
      · simp only [hd2, ↓reduceIte]
        by_cases hd3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0
        · simp only [hd3, ↓reduceIte]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · simp only [hd3, ↓reduceIte]
          cases inp.opkBSk? <;> dsimp only
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · rename_i opkSk
            by_cases hd4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0
            · simp only [hd4, ↓reduceIte]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            · simp only [hd4, ↓reduceIte]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- `[LibsignalFullPlacement]` block-`75` (`initialize_bob_session`) bad-KEM owned-error contract
on `stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem cliInitBob_badKem_errOwned_full_placed_ok_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 75)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedFrozenPlacedSpec
        A lim (fun _ => PqxdhAcceptBadKemErrEnv)) := by
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hWF := CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliModelPrims_structural X W
  have hP := CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliModelPrims_matchCrypto X W
  have hH :=
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget.cliResponderPqxdhHookContractsPlaced
      X mmpl gh W hG
  have h_memcpy : HookSat ext lsMemcpySym
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec := by
    have hvm := cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hG
    rcases hvm with ⟨f, hf, hok⟩
    refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
    rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
    · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
      rcases x with ⟨dst, src, bs⟩
      dsimp only [withVmPreserved,
        framelessMemcpySpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
    · exact ⟨hkf, hsym, Or.inr hrest⟩
  have h79 :=
    LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.pqxdhAccept_badKem_err_owned_placed_ok_of_block
      (callerProg := CryptoVerification.lsProg_75 ext) (i := 75)
      hWF
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.ResponderCanonicalPlacedBudget.ecPubKeyIsCanonical_responder_placed_ok_cl
        hWF hH.dalekMontToEd hH.dalekTorsionFree)
      (hH.calculateAgreement_ok hP)
      (LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget.vecAppendElements_fast_placed_ok_cl
        h_memcpy)
      hH.noAllocShim hH.alloc hH.dealloc h_memcpy
  have h75 :=
    LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSession_badKem_errOwned_frozen_placed_ok_of_accept
      h79
  have hbase :=
    CryptoVerification.E2E.Pqxdh.ResponderCore.ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := CryptoVerification.lsProg_75 ext)
      (i := 518) (j := 75) h75
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hsub : ∀ evs,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.AcceptBadKemEnv
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) x.1.inp evs →
      PqxdhAcceptBadKemErrEnv evs := by
    rintro _ rfl
    exact acceptBadKemEvents_mem_pqxdhAcceptBadKemErrEnv _ x.1.inp
  refine hbase.mono_outcome x R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · refine Satisfies.mono (sepConj_mono_left ?_) hpre
    dsimp only [
      LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedFrozenPlacedSpec,
      withLsFrozen,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec]
    refine sepConj_mono_left (sepConj_mono_left ?_)
    exact Entails.pure_mono fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hfits⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, fun evs hevs => hfits evs (hsub evs hevs)⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedFrozenPlacedSpec,
        withLsFrozen,
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemBobAuxPlacedBudget.initializeBobSessionBadKemErrOwnedInnerPlacedSpec]
      refine Entails.sepExists_mono fun evs => sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨htr, hevs⟩ => ⟨htr, hsub evs hevs⟩
    · exact Or.inr hrest

private abbrev r20a3a4_badKemMsgRemInnerAtGen
    (A0 : CryptoVerification.RustHeap.RustAlloc)
    (g : CryptoVerification.LibsignalPublicApiRepr.PreKeyMsgGhost)
    (msgA : BitVec 64) (pm : PreKeySignalMessage) (kp : KyberPayload) : SepProp :=
  ⌜g.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
  (if kp.ciphertext = [] then emp else A0.live g.kyberPtr kp.ciphertext.length 1) ∗
  memRegion (msgA + 164#64) 4 ∗
  CryptoVerification.LibsignalTripleRatchetRepr.boxU8At A0 (msgA + 128#64) g.serPtr pm.serialized ∗
  memRegion (msgA + 241#64) 7

private theorem r20a3a4_badKemMsgRemInnerAtGen_dup_kyber
    (A0 : CryptoVerification.RustHeap.RustAlloc)
    (g : CryptoVerification.LibsignalPublicApiRepr.PreKeyMsgGhost)
    (msgA : BitVec 64) (pm : PreKeySignalMessage) (kp : KyberPayload) :
    r20a3a4_badKemMsgRemInnerAtGen A0 g msgA pm kp ⊢
      ⌜g.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        r20a3a4_badKemMsgRemInnerAtGen A0 g msgA pm kp := by
  dsimp only [r20a3a4_badKemMsgRemInnerAtGen]
  refine Entails.pure_left fun hp => ?_
  have hp' : g.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63 := hp
  rw [pure_sepConj_of_true hp', pure_sepConj_of_true hp]
  exact Entails.refl _

private theorem r20a3a4_preKeyMsgAt_unpack_badKem
    (A0 : CryptoVerification.RustHeap.RustAlloc)
    (g : CryptoVerification.LibsignalPublicApiRepr.PreKeyMsgGhost)
    (msgA : BitVec 64) (pm : PreKeySignalMessage) (kp : KyberPayload)
    (hv4 : pm.messageVersion = 4#8) (hkp : pm.kyberPayload = some kp) :
    preKeyMsgAt A0 g msgA pm ⊢
      ∃∗ opkWord : BitVec 32,
        ⌜∀ id : BitVec 32, pm.preKeyId = some id → opkWord = id⌝ ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.p2BadKemMsgFieldsAt
          msgA g.kyberPtr (mkBadKemHdr pm kp) kp.ciphertext
          pm.message.messageVersion opkWord kp.preKeyId pm.registrationId pm.signedPreKeyId ∗
        signalMessageRestVerAt A0 g.msg msgA pm.message ∗
        r20a3a4_badKemMsgRemInnerAtGen A0 g msgA pm kp := by
  unfold preKeyMsgAt LibsignalBinary.Proofs.SignalSession.Cli.D3.p2BadKemMsgFieldsAt
    r20a3a4_badKemMsgRemInnerAtGen
  rw [hv4, hkp,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.signalMessageAt_eq_ver_sep,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.hdrOpkIdBv?_mkBadKemHdr,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.bytesToBv8_mkBadKemHdr_ekAPk,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.bytesToBv8_mkBadKemHdr_ikAPk]
  dsimp only [CryptoVerification.LibsignalPublicApiRepr.optKyberAt,
    CryptoVerification.LibsignalTripleRatchetRepr.boxU8At]
  rw [LibsignalBinary.Proofs.SignalSession.Cli.D3.boxU8_payload_split_d3
    A0 g.kyberPtr kp.ciphertext]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  cases hopk_eq : pm.preKeyId with
  | none =>
    dsimp only [CryptoVerification.LibsignalPublicApiRepr.optU32At,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.opkOptTag32]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [CryptoVerification.SignalSession.Cli.RunProofs.Poll.memRegion_4_eq_exists_pointsTo32
      (msgA + 124#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun opkWord => ?_
    refine Entails.sepExists_right opkWord (Entails.pure_right (by nofun) ?_)
    exact Entails.of_eq (by sep_ac_rfl)
  | some id =>
    dsimp only [CryptoVerification.LibsignalPublicApiRepr.optU32At,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.opkOptTag32]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right id (Entails.pure_right (fun _ h => Option.some.inj h) ?_)
    exact Entails.of_eq (by sep_ac_rfl)

private theorem r20a3a4_pull_pure_msg_group {M1 M2 M3 Tail : SepProp} {φ : Prop} :
    (M1 ∗ M2 ∗ (⌜φ⌝ ∗ M3)) ∗ Tail = ⌜φ⌝ ∗ ((M1 ∗ M2 ∗ M3) ∗ Tail) := by sep_ac_rfl

/-- Unpack Stage-P2 Path-A (`opt = none`) post-P1 state into `stageP2BadKemPreAtPlaced`. -/
theorem stageP2_entry_unpack_badKem_pathA_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {W : CliHooks} {B : RunBudgets} {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kp : KyberPayload) (st1 : M.σ) (s0 s1 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hv4 : y.g.msg.messageVersion = 4#8) (hkp : y.g.msg.kyberPayload = some kp)
    (hfp : fp = sp + 3184#64) (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val) (hScope : ∀ r', Scope r' → scopeIn r') :
    stageP2PostP1At (A.atState lim st1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    lsLogOff ∗ stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords, ⌜∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id⌝ ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced
          A lim
          (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
          (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId
            y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
          st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
          y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
          0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B)
          (badKemInnerFramePlacedBudget A y kp rngPtr sp) := by
  dsimp only [p1LoadedRecordAt, stageP2PostP1At, RustCliAllocBudget.atState]
  have hdrEq :
      CryptoVerification.E2E.Pqxdh.ResponderClosure.sessionRecordEmptyHeaderAt (y.fut + 224#64) =
        CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 224#64) :=
    rfl
  rw [hdrEq,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.coroCopyAt_eq_head3_tail11,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    (cells (y.fut + 920#64) 2 ∗ memRegion (y.fut + 592#64) 48 ∗
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.coroUnusedP1At y.fut) ∗
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.closStackUnusedP1OkAt sp ∗
    storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    (CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 224#64) ∗
      memRegion (y.fut + 256#64) 336 ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym)
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 912#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 0#8) ∗ (sp ↦₆₄ 0#64) ∗
      ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
      ((sp + 168#64) ↦₆₄ v_a8) ∗ ((sp + 176#64) ↦₆₄ (y.fut + 912#64)) ∗
      ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ y.cx) ∗
      ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 216#64) 348 ∗ memRegion (sp + 992#64) 368 ∗
      CryptoVerification.E2E.Pqxdh.ResponderClosure.decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      memRegion y.out 48 ∗ A.pool lim st1 s1 ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono
    (r20a3a4_preKeyMsgAt_unpack_badKem A.repAlloc y.g.msgG y.g.msgA y.g.msg kp hv4 hkp)
    (sepConj_mono
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun hopkWord => ?_
  have hstoreOkB :
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.DecPkStoreOk
        ⟨W.C, W.Q⟩ y.g.F :=
    ⟨hstoreOk.keyPairLt, hstoreOk.preKeysWf, hstoreOk.baseKeysLt⟩
  have hstores :=
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.storesAt_entails_cliPollStoresKitsAtPlaced
      (A := A.repAlloc) (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := opkWord) (sid := y.g.msg.signedPreKeyId) (kid := kp.preKeyId)
      (kbk := y.g.msg.baseKey) (cliKitStk B) y.g.stores
      CryptoVerification.SignalSession.Cli.StoresGhost.opened
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSessInv_opened_scopeKit hScope hFok)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliIdOwnInv_of_storeOk hstoreOkB)
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliIdInv_opened_peer hFok)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliPkInv_of_storeOk hstoreOkB opkWord)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliSpkInv_of_storeOk hstoreOkB y.g.msg.signedPreKeyId)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliKpkInvFull_of_storeOk hstoreOkB kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  refine Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
    (Entails.pure_right hopkWord ?_)
  exact Entails.of_eq (by
    have htailEq :
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2CoroScratchTailAt y.fut =
          LibsignalBinary.Proofs.SignalSession.Cli.D3.p2CoroScratchTailAt y.fut := rfl
    dsimp only [
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStoresKitsAtPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStoresKitsAt,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced,
      badKemInnerFramePlacedBudget, r20a3a4_badKemMsgRemInnerAtGen,
      cliPollSessKitPlaced, cliPollSpkKitPlaced, cliPollKpkKitPlaced,
      cliPollPkKitPlaced, cliPollIdKitPlaced, lsLogOff]
    simp only [BitVec.reduceNeg, hdrEq, htailEq]
    sep_ac_rfl)

/-- Unpack Stage-P2 Over-Path-C (`opt = some r`, `r.currentSession = some sess`) post-P1 state
into `stageP2OverBadKemPreAtPlaced`. -/
theorem stageP2_entry_unpack_badKem_over_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {W : CliHooks} {B : RunBudgets} {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8))) (kp : KyberPayload)
    (st1 : M.σ) (s0 s1 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess)
    (hv4 : y.g.msg.messageVersion = 4#8) (hkp : y.g.msg.kyberPayload = some kp)
    (hfp : fp = sp + 3184#64) (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val) (hScope : ∀ r', Scope r' → scopeIn r') :
    stageP2PostP1At (A.atState lim st1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    lsLogOff ∗ stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜(y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63) ∧
         (∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id)⌝ ∗
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2OverBadKemPreAtPlaced
          A lim
          (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
          (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId
            y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
          st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
          y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
          0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B)
          (badKemInnerFramePlacedBudget A y kp rngPtr sp) := by
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]; simp only [sepConj_assoc]; refine Entails.pure_left fun _hkit => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun g => ?_
  refine Entails.trans (sepConj_mono_left
    (CryptoVerification.SignalSession.Cli.RunProofs.Poll.sessionRecordAt_some_eq_prev_sess
      A.repAlloc y.fut g r sess hcur)) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun recG => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun _hgcur => ?_
  dsimp only [stageP2PostP1At, RustCliAllocBudget.atState]
  rw [CryptoVerification.SignalSession.Cli.RunProofs.Poll.coroCopyAt_eq_head3_tail11,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    (cells (y.fut + 920#64) 2 ∗ memRegion (y.fut + 592#64) 48 ∗
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.coroUnusedP1At y.fut) ∗
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.closStackUnusedP1OkAt sp ∗
    storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    (CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A.repAlloc y.fut g ∗
      CryptoVerification.LibsignalPublicApiRepr.sessionStateReprAt A.repAlloc (y.fut + 248#64) recG sess ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym)
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 912#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 0#8) ∗ (sp ↦₆₄ 0#64) ∗
      ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
      ((sp + 168#64) ↦₆₄ v_a8) ∗ ((sp + 176#64) ↦₆₄ (y.fut + 912#64)) ∗
      ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ y.cx) ∗
      ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 216#64) 348 ∗ memRegion (sp + 992#64) 368 ∗
      CryptoVerification.E2E.Pqxdh.ResponderClosure.decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      memRegion y.out 48 ∗ A.pool lim st1 s1 ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono
    (r20a3a4_preKeyMsgAt_unpack_badKem A.repAlloc y.g.msgG y.g.msgA y.g.msg kp hv4 hkp)
    (sepConj_mono
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left
        (CryptoVerification.SignalSession.Cli.RunProofs.Poll.stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun hopkWord => ?_
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (r20a3a4_badKemMsgRemInnerAtGen_dup_kyber A.repAlloc y.g.msgG y.g.msgA y.g.msg kp)))) ?_
  rw [r20a3a4_pull_pure_msg_group]; refine Entails.pure_left fun hkyb => ?_
  have hstoreOkB :
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.DecPkStoreOk
        ⟨W.C, W.Q⟩ y.g.F :=
    ⟨hstoreOk.keyPairLt, hstoreOk.preKeysWf, hstoreOk.baseKeysLt⟩
  have hstores :=
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.storesAt_entails_cliPollStoresKitsAtPlaced
      (A := A.repAlloc) (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := opkWord) (sid := y.g.msg.signedPreKeyId) (kid := kp.preKeyId)
      (kbk := y.g.msg.baseKey) (cliKitStk B) y.g.stores
      CryptoVerification.SignalSession.Cli.StoresGhost.opened
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSessInv_opened_scopeKit hScope hFok)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliIdOwnInv_of_storeOk hstoreOkB)
      (CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliIdInv_opened_peer hFok)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliPkInv_of_storeOk hstoreOkB opkWord)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliSpkInv_of_storeOk hstoreOkB y.g.msg.signedPreKeyId)
      (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliKpkInvFull_of_storeOk hstoreOkB kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  have hprevEq :
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A.repAlloc y.fut g =
        LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.prevSessionsEmptyAt A y.fut g :=
    rfl
  refine Entails.sepExists_right g (Entails.sepExists_right recG
    (Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
      (Entails.pure_right ⟨hkyb, hopkWord⟩ ?_)))
  exact Entails.of_eq (by
    have htailEq :
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2CoroScratchTailAt y.fut =
          LibsignalBinary.Proofs.SignalSession.Cli.D3.p2CoroScratchTailAt y.fut := rfl
    dsimp only [
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStoresKitsAtPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStoresKitsAt,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2OverBadKemPreAtPlaced,
      badKemInnerFramePlacedBudget, r20a3a4_badKemMsgRemInnerAtGen,
      cliPollSessKitPlaced, cliPollSpkKitPlaced, cliPollKpkKitPlaced,
      cliPollPkKitPlaced, cliPollIdKitPlaced, lsLogOff]
    simp only [BitVec.reduceNeg, hprevEq, htailEq]
    sep_ac_rfl)

private abbrev r20a5m_badKemMsgRemInnerAtGen
    (A0 : CryptoVerification.RustHeap.RustAlloc)
    (g : CryptoVerification.LibsignalPublicApiRepr.PreKeyMsgGhost)
    (msgA : BitVec 64) (pm : PreKeySignalMessage) (kp : KyberPayload) : SepProp :=
  ⌜g.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
  (if kp.ciphertext = [] then emp else A0.live g.kyberPtr kp.ciphertext.length 1) ∗
  memRegion (msgA + 164#64) 4 ∗
  CryptoVerification.LibsignalTripleRatchetRepr.boxU8At A0 (msgA + 128#64) g.serPtr pm.serialized ∗
  memRegion (msgA + 241#64) 7

private theorem r20a5m_p2BadKemMsgFields_reassemble
    (A0 : CryptoVerification.RustHeap.RustAlloc)
    (g : CryptoVerification.LibsignalPublicApiRepr.PreKeyMsgGhost)
    (msgA : BitVec 64) (pm : PreKeySignalMessage) (kp : KyberPayload) (opkWord : BitVec 32)
    (hv4 : pm.messageVersion = 4#8) (hkp : pm.kyberPayload = some kp)
    (hopkWord : ∀ id : BitVec 32, pm.preKeyId = some id → opkWord = id) :
    LibsignalBinary.Proofs.SignalSession.Cli.D3.p2BadKemMsgFieldsAt
      msgA g.kyberPtr (mkBadKemHdr pm kp) kp.ciphertext
      pm.message.messageVersion opkWord kp.preKeyId pm.registrationId pm.signedPreKeyId ∗
    signalMessageRestVerAt A0 g.msg msgA pm.message ∗
    r20a5m_badKemMsgRemInnerAtGen A0 g msgA pm kp ⊢
      preKeyMsgAt A0 g msgA pm := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.p2BadKemMsgFieldsAt
    r20a5m_badKemMsgRemInnerAtGen preKeyMsgAt
  rw [hv4, hkp,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.signalMessageAt_eq_ver_sep,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.hdrOpkIdBv?_mkBadKemHdr,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.bytesToBv8_mkBadKemHdr_ekAPk,
      LibsignalBinary.Proofs.SignalSession.Cli.D3.bytesToBv8_mkBadKemHdr_ikAPk]
  have hoptU32 :
      ((msgA + 120#64) ↦₃₂
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.opkOptTag32 pm.preKeyId) ∗
      ((msgA + 124#64) ↦₃₂ opkWord) ⊢
      CryptoVerification.LibsignalPublicApiRepr.optU32At (msgA + 120#64) pm.preKeyId := by
    cases hopk_eq : pm.preKeyId with
    | none =>
      dsimp only [CryptoVerification.LibsignalPublicApiRepr.optU32At,
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_right (by
        rw [CryptoVerification.SignalSession.Cli.RunProofs.Poll.memRegion_4_eq_exists_pointsTo32
          (msgA + 124#64)]
        exact Entails.sepExists_right opkWord (Entails.refl _))
    | some id =>
      have hw := hopkWord id hopk_eq
      subst hw
      dsimp only [CryptoVerification.LibsignalPublicApiRepr.optU32At,
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Entails.of_eq rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (((msgA + 120#64) ↦₃₂
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.opkOptTag32 pm.preKeyId) ∗
      ((msgA + 124#64) ↦₃₂ opkWord)) ∗
    (((msgA + 112#64) ↦₈ pm.message.messageVersion) ∗
      signalMessageRestVerAt A0 g.msg msgA pm.message ∗
      CryptoVerification.LibsignalTripleRatchetRepr.boxU8At A0 (msgA + 128#64) g.serPtr pm.serialized ∗
      (((msgA + 144#64) ↦₆₄ g.kyberPtr) ∗
        ((msgA + 152#64) ↦₆₄ BitVec.ofNat 64 kp.ciphertext.length) ∗
        ⌜g.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        ((if kp.ciphertext = [] then emp else A0.live g.kyberPtr kp.ciphertext.length 1) ∗
          (g.kyberPtr ↦ₛ kp.ciphertext)) ∗
        ((msgA + 160#64) ↦₃₂ kp.preKeyId) ∗
        memRegion (msgA + 164#64) 4) ∗
      ((msgA + 168#64) ↦ₛ pm.baseKey.bytes.toList) ∗
      ((msgA + 200#64) ↦ₛ pm.identityKey.publicKey.bytes.toList) ∗
      ((msgA + 232#64) ↦₃₂ pm.registrationId) ∗
      ((msgA + 236#64) ↦₃₂ pm.signedPreKeyId) ∗
      ((msgA + 240#64) ↦₈ 4#8) ∗
      memRegion (msgA + 241#64) 7) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hoptU32) ?_
  dsimp only [CryptoVerification.LibsignalPublicApiRepr.optKyberAt,
    CryptoVerification.LibsignalTripleRatchetRepr.boxU8At]
  rw [LibsignalBinary.Proofs.SignalSession.Cli.D3.boxU8_payload_split_d3
    A0 g.kyberPtr kp.ciphertext]
  exact Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl)

/-- Fold any Stage-P2 bad-KEM error exit (`p2BadKemErrFrameAtPlaced`) back into the poll error
postcondition spatial frame with `A.pool lim stf sf`. -/
theorem p2BadKemErrFrame_fold_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kp : KyberPayload) (w : PathAEntryWords) (stf : M.σ) (s0 sf : State)
    (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hv4 : y.g.msg.messageVersion = 4#8) (hkp : y.g.msg.kyberPayload = some kp)
    (hfp : fp = sp + 3184#64)
    (hopk : ∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id) :
    (decResAt A.repAlloc y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B)).storeAt
      (y.g.stores + 80#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey
      (cliKitStk B)).storeAt (y.g.stores + 120#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 200#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).identityAt
      y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
    LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
      A lim stf s0 sf sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym)
      y.g.peerA (y.g.msgA + 200#64) (mkBadKemHdr y.g.msg kp) kp.ciphertext
      y.g.msg.message.messageVersion
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
      y.g.me y.g.peer (dpClosSubStack B)
      (badKemInnerFramePlacedBudget A y kp rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt A.repAlloc y.out (.error err) ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      lsLogOff ∗ A.pool lim stf sf ∗ stackAt sp (dpClosSubStack B) ∗ anyHeap := by
  have hstores :=
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStoresKitsAtPlaced_entails_storesAt
      (A := A.repAlloc) (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
      (pid := w.opkWord) (sid := y.g.msg.signedPreKeyId) (kid := kp.preKeyId)
      (kbk := y.g.msg.baseKey) (cliKitStk B) y.g.stores
      CryptoVerification.SignalSession.Cli.StoresGhost.opened
  have hmsgFold :=
    r20a5m_p2BadKemMsgFields_reassemble A.repAlloc y.g.msgG y.g.msgA y.g.msg kp w.opkWord
      hv4 hkp hopk
  have hcoro :=
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2_coro_err_fold
      y.fut y.g.msgA y.g.peerA y.g.meA (y.g.stores + 240#64) (lsρ cliSessionVtSym)
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstk :=
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2_stack_err_fold sp fp s0 hfp
  dsimp only [
    LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced,
    badKemInnerFramePlacedBudget]
  refine Entails.trans (show _ ⊢
    (CryptoVerification.E2E.Pqxdh.ResponderClosure.processPrekeyActive10At
        y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym)
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 224#64) 368 ∗ cells (y.fut + 592#64) 6 ∗
      memRegion (y.fut + 640#64) 24 ∗ memRegion (y.fut + 664#64) 20 ∗
      memRegion (y.fut + 684#64) 8 ∗ memRegion (y.fut + 692#64) 12 ∗
      ((y.fut + 704#64) ↦₈ 1#8) ∗ ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 912#64) ↦₈ 1#8) ∗ memRegion (y.fut + 920#64) 96 ∗
      ((y.fut + 1265#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 705#64) 7 ∗ memRegion (y.fut + 913#64) 7 ∗
      memRegion (y.fut + 1160#64) 8 ∗ memRegion (y.fut + 1200#64) 65 ∗
      memRegion (y.fut + 1267#64) 5 ∗
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2CoroScratchTailAt y.fut ∗
      memRegion (y.fut + 1922#64) 6) ∗
    ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 120 ∗ memRegion (sp + 128#64) 88 ∗
      memRegion (sp + 216#64) 348 ∗ memRegion (sp + 592#64) 20 ∗
      memRegion (sp + 624#64) 9 ∗ memRegion (sp + 633#64) 39 ∗
      memRegion (sp + 688#64) 36 ∗ memRegion (sp + 736#64) 36 ∗
      memRegion (sp + 784#64) 36 ∗ memRegion (sp + 832#64) 36 ∗
      memRegion (sp + 880#64) 36 ∗ memRegion (sp + 928#64) 8 ∗
      memRegion (sp + 940#64) 1 ∗ memRegion (sp + 944#64) 48 ∗
      memRegion (sp + 992#64) 368 ∗ spMidGapsAt sp ∗
      cells (sp + 1376#64) 4 ∗ cells (sp + 1696#64) 4 ∗
      cells (sp + 2016#64) 4 ∗ cells (sp + 2352#64) 8 ∗
      memRegion (sp + 2704#64) 288 ∗ memRegion (fp + -128#64) 9 ∗
      sp550P2V1RemAt sp ∗
      CryptoVerification.E2E.Pqxdh.ResponderClosure.decryptPrekeySavedRegsAt (sp + 3280#64) s0) ∗
    decResAt A.repAlloc y.out (.error err) ∗
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStoresKitsAtPlaced
      A.repAlloc y.g.F scopeKit y.g.peer w.opkWord
      y.g.msg.signedPreKeyId kp.preKeyId y.g.msg.baseKey (cliKitStk B) y.g.stores
      CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    (LibsignalBinary.Proofs.SignalSession.Cli.D3.p2BadKemMsgFieldsAt
        y.g.msgA y.g.msgG.kyberPtr (mkBadKemHdr y.g.msg kp) kp.ciphertext
        y.g.msg.message.messageVersion w.opkWord kp.preKeyId
        y.g.msg.registrationId y.g.msg.signedPreKeyId ∗
      signalMessageRestVerAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      r20a5m_badKemMsgRemInnerAtGen A.repAlloc y.g.msgG y.g.msgA y.g.msg kp) ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    lsLogOff ∗ A.pool lim stf sf ∗ stackAt sp (dpClosSubStack B) ∗ anyHeap
    by exact Entails.of_eq (by
      have htailEq :
          LibsignalBinary.Proofs.SignalSession.Cli.D3.p2CoroScratchTailAt y.fut =
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2CoroScratchTailAt y.fut :=
        rfl
      dsimp only [
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStoresKitsAtPlaced,
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStoresKitsAt,
        r20a5m_badKemMsgRemInnerAtGen,
        cliPollSessKitPlaced, cliPollSpkKitPlaced, cliPollKpkKitPlaced,
        cliPollPkKitPlaced, cliPollIdKitPlaced, lsLogOff]
      simp only [BitVec.reduceNeg, htailEq]
      sep_ac_rfl)) ?_
  exact sepConj_mono hcoro
    (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono hstores (sepConj_mono_left hmsgFold))))

private theorem r20f_toSkeletonRunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : CryptoVerification.LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

private def r20a6w_dummyExtras : UnreachedPqxdhPrimitives :=
  ⟨fun _ => [], fun _ _ _ => [], fun _ _ => [], fun _ _ => [], fun _ => ([], []),
   fun _ => [], fun _ _ _ => false⟩

private def r20a6w_alwaysSomePrims (W : CliHooks) : Primitives :=
  { ofSignalPqxdhPrimitives (modelPrims r20a6w_dummyExtras ⟨W.C, W.Q⟩) with
    isCanonical := fun _ => true
    x25519 := fun _ _ => [1]
    kemDecaps := fun _ _ => some [] }

private theorem r20a6w_acceptKeys_ne_none (W : CliHooks) (inp : AcceptKeysInput)
    (htrust : inp.trustedPeer = true) (hrep : inp.replayOk = true)
    (hwell : WellSizedAcceptKeysInput inp)
    (hopk : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) :
    acceptKeys (r20a6w_alwaysSomePrims W) inp ≠ none := by
  have hik : inp.hdr.ikAPk.length = 32 := by
    try (unfold WellSizedAcceptKeysInput at hwell)
    try (cases hwell)
    tauto
  have hek : inp.hdr.ekAPk.length = 32 := by
    try (unfold WellSizedAcceptKeysInput at hwell)
    try (cases hwell)
    tauto
  cases hopk1 : inp.hdr.opkId? <;> cases hopk2 : inp.opkBSk?
  · simp [acceptKeys, r20a6w_alwaysSomePrims, dhOptNonZero, htrust, hrep, hik, hek, hopk1, hopk2]
  · simp [hopk1, hopk2] at hopk
  · simp [hopk1, hopk2] at hopk
  · simp [acceptKeys, r20a6w_alwaysSomePrims, dhOptNonZero, htrust, hrep, hik, hek, hopk1, hopk2]

private theorem r20a6w_hookSat_noAllocShimBudget {H : String → Option (State → State)}
    (hsat : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem r20a6w_hookSat_sessionMemcpyBudget {H : String → Option (State → State)}
    (stk : Nat) (hsat : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    HookSat H "memcpy" (sessionMemcpyBudgetSpec stk) := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hpre' : s0.mem ⊨ (withVmPreserved framelessMemcpySpec).pre (dst, src, bs) s0 ∗
      (stackAt s0.sp stk ∗ R) := by
    dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec,
      withVmPreserved, framelessMemcpySpec] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  rcases hok (dst, src, bs) (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec,
      withVmPreserved, framelessMemcpySpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · rcases hrest with ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · dsimp only [withVmPreserved, framelessMemcpySpec] at hp
      rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
    · dsimp only [withVmPreserved, framelessMemcpySpec] at he
      rw [satisfies_pure_sepConj] at he; exact False.elim he.1
    · dsimp only [withVmPreserved, framelessMemcpySpec] at ho
      rw [satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem r20a6w_baseCalleesPlaced4K [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2BaseCalleesPlaced4K A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  StageP2BaseCalleesPlaced4K.of_hooks
    (r20a6w_hookSat_noAllocShimBudget hh.codecHooks.shim)
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (r20a6w_hookSat_sessionMemcpyBudget allocHookStack hh.codecHooks.memcpy)
    (isSameAccount_4k_placed_ok_on_stageP1
      ((cliGhostExterns_other gh _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
      (uuidTryParse_placed_vm_code_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))

private theorem r20a6w_pureCalleesPlaced4K [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PureCalleesPlaced4KOfEnv (r20a6w_alwaysSomePrims W) A lim W.C.F
      (fun _ _ => VacuousBobAllocEnv) (fun _ => PqxdhAcceptBadKemErrEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hbase := r20a6w_baseCalleesPlaced4K mmpl gh W hh
  refine {
    publicKeySerialize := hbase.publicKeySerialize
    promoteMatchingSessionEmpty := hbase.promoteMatchingSessionEmpty
    curveKeyPairSerde := hbase.curveKeyPairSerde
    kemKeyPairSerde := hbase.kemKeyPairSerde
    preKeyRecordKeyPair := hbase.preKeyRecordKeyPair
    dropSpe2 := hbase.dropSpe2
    isSameAccount := hbase.isSameAccount
    initializeBobV1 := ?_
    initializeBobErr := ?_
    promoteStateEmpty := hbase.promoteStateEmpty
    dropProcessPrekeyImplState1 := hbase.dropProcessPrekeyImplState1
    dropSessionStructure3 := hbase.dropSessionStructure3
  }
  · intro st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfits
    exact (not_fitsEnv_vacuousBobAllocEnv hfits).elim
  · apply subroutine_ok_outcome_intro
    rintro ⟨g, st⟩ R s0 _ _ hpre _
    dsimp only [initializeBobSessionErr4KPlacedSpec, withLsCodeRoLoaded,
      initializeBobSessionErr4KInnerPlacedSpec] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, hpre⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, _, _, htrust, hrep, hopk, hwell, _, _, hnone, _⟩, _⟩
    exact (r20a6w_acceptKeys_ne_none W g.inp htrust hrep hwell hopk hnone).elim

private theorem r20a6w_dup_pure_right {φ : Prop} {P Q : SepProp}
    (h : Q ⊢ ⌜φ⌝ ∗ Q) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem r20a6w_dup_pure_left {φ : Prop} {P Q : SepProp}
    (h : P ⊢ ⌜φ⌝ ∗ P) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_left h) (by rw [sepConj_assoc]; exact Entails.refl _)

private theorem r20a6w_badKemInnerFrame_dup_kyber [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kp : KyberPayload) (rngPtr sp : BitVec 64) :
    badKemInnerFramePlacedBudget A y kp rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        badKemInnerFramePlacedBudget A y kp rngPtr sp := by
  have hleaf :
      (⌜y.g.msgG.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        (if kp.ciphertext = [] then emp else A.repAlloc.live y.g.msgG.kyberPtr kp.ciphertext.length 1) ∗
        memRegion (y.g.msgA + 164#64) 4 ∗
        CryptoVerification.LibsignalTripleRatchetRepr.boxU8At A.repAlloc
          (y.g.msgA + 128#64) y.g.msgG.serPtr y.g.msg.serialized ∗
        memRegion (y.g.msgA + 241#64) 7) ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
        (⌜y.g.msgG.kyberPtr ≠ 0 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
          (if kp.ciphertext = [] then emp else A.repAlloc.live y.g.msgG.kyberPtr kp.ciphertext.length 1) ∗
          memRegion (y.g.msgA + 164#64) 4 ∗
          CryptoVerification.LibsignalTripleRatchetRepr.boxU8At A.repAlloc
            (y.g.msgA + 128#64) y.g.msgG.serPtr y.g.msg.serialized ∗
          memRegion (y.g.msgA + 241#64) 7) := by
    refine Entails.pure_left fun hp => ?_
    have hp' : y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63 := hp
    rw [pure_sepConj_of_true hp', pure_sepConj_of_true hp]
    exact Entails.refl _
  unfold badKemInnerFramePlacedBudget
  repeat (first
    | exact hleaf
    | exact r20a6w_dup_pure_left hleaf
    | refine r20a6w_dup_pure_right ?_)

private theorem r20a6w_stageP2BadKemPreAt_dup_kyber [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (kp : KyberPayload) (w : PathAEntryWords) (st1 : M.σ) (s0 s1 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced
      A lim
      (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
      y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
      0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (badKemInnerFramePlacedBudget A y kp rngPtr sp) ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63⌝ ∗
      LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced
        A lim
        (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
        st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
        y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
        y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
        (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
        0#8 0#8 w.b_4b0 w.b_4f1 0#8
        w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
        StoresGhost.opened.signed StoresGhost.opened.kyber
        StoresGhost.opened.oneTime StoresGhost.opened.identity
        y.g.me y.g.peer (dpClosSubStack B)
        (badKemInnerFramePlacedBudget A y kp rngPtr sp) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced
  repeat (first
    | exact r20a6w_badKemInnerFrame_dup_kyber A y kp rngPtr sp
    | exact r20a6w_dup_pure_left (r20a6w_badKemInnerFrame_dup_kyber A y kp rngPtr sp)
    | refine r20a6w_dup_pure_right ?_)

private theorem r20a6w_freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (LibsignalBinary.Heap.rustDeallocEvents size align) := by
  unfold FreeOnlyEvs LibsignalBinary.Heap.rustDeallocEvents
  intro ev hev
  try split at hev
  all_goals simp at hev
  all_goals rcases hev with rfl
  all_goals exact ⟨_, _, rfl⟩

private theorem r20a6w_fitsEnv_drop_freeOnly {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} (h : FitsEnv M lim st (SeqEnv E FreeOnlyEvs)) :
    FitsEnv M lim st E :=
  h.mono fun _ he => Or.inl he

private theorem r20a6w_fitsEnv_step3 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E1 E2 E3 E4 : List AllocEvent → Prop} {e1 e2 e3 : List AllocEvent}
    (h : FitsEnv M lim st (SeqEnv E1 (SeqEnv E2 (SeqEnv E3 (SeqEnv E4 FreeOnlyEvs)))))
    (h1 : E1 e1) (h2 : E2 e2) (h3 : E3 e3) :
    FitsEnv M lim (M.stepEvents (e2 ++ e3) (M.stepEvents e1 st)) E4 := by
  rw [M.stepEvents_append]
  exact r20a6w_fitsEnv_drop_freeOnly (((h.seq_right h1).seq_right h2).seq_right h3)

private theorem r20a6w_opk_env_eq
    {spkBox : Nat} {spkPoll : List AllocEvent → Prop}
    {kpkBox : Nat} {kpkPoll : List AllocEvent → Prop}
    {pkBox1 pkBox2 : Nat}
    {pkPoll1 pkPoll2 : BitVec 32 → List AllocEvent → Prop}
    {kpBox : Nat} {pm : PreKeySignalMessage} {kp : KyberPayload} {opkWord : BitVec 32}
    (hopk : ∀ id : BitVec 32, pm.preKeyId = some id → opkWord = id)
    (hbox : opkWord = pmPreKeyId pm → pkBox1 = pkBox2)
    (hpoll : opkWord = pmPreKeyId pm → pkPoll1 = pkPoll2) :
    P2Sub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox1 pkPoll1 (hdrOpkIdBv? (mkBadKemHdr pm kp)) =
      P2Sub1To4Arm3Env spkBox spkPoll kpkBox kpkPoll pkBox2 pkPoll2 pm.preKeyId ∧
    P2Sub1To4OkEnv spkBox spkPoll kpkBox kpkPoll pkBox1 pkPoll1 kpBox (hdrOpkIdBv? (mkBadKemHdr pm kp)) =
      P2Sub1To4OkEnv spkBox spkPoll kpkBox kpkPoll pkBox2 pkPoll2 kpBox pm.preKeyId := by
  rw [hdrOpkIdBv?_mkBadKemHdr]
  cases hid : pm.preKeyId with
  | none => exact ⟨rfl, rfl⟩
  | some id =>
    have hw : opkWord = pmPreKeyId pm := by
      unfold pmPreKeyId
      rw [hopk id hid, hid]
      rfl
    unfold P2Sub1To4Arm3Env P2Sub1To4OkEnv P2Sub4OkEnv
    rw [hbox hw, hpoll hw]
    exact ⟨rfl, rfl⟩

set_option maxHeartbeats 1200000 in
private theorem r20a6w_stageP2_badKem_reject_body [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State) (opt : Option (SessionRecord (List (BitVec 8))))
    (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (hbadCond : MsgCondBadKem Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt))
    (hevs_sub : ∀ evs_p2,
      StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt evs_p2 →
      DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val (.ok opt))
    (htr1 : s1.trace = s0.trace) (hro1 : LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x868#64) (hrun1 : s1.status = .Running)
    (halign1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym))
    (hs1_files : s1.fs.files = y.g.F) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
      (fun sf P_f =>
        (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic y s0 sf ∗ R)) := by
  obtain ⟨hnotSameSid, hv4, ⟨kp, hkp, hbadKem⟩, hnoMatch⟩ := hbadCond
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let sp := s0.sp - 0xcd0#64
  let fp := sp + 3184#64
  let st1 := M.stepEvents evs_p1 y.st
  let LeftoverBase : SepProp := coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  let Leftover : SepProp := LeftoverBase ∗ anyHeap
  let Fr_p2 : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗ LeftoverBase
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := nofun
  have herr0_s : err0 ≠ .store () := nofun
  have hkpkId : pmKyberId y.g.msg = kp.preKeyId := by
    unfold pmKyberId; rw [hkp]
  have hpre_split :
      (stageP2PostP1At (A.atState lim st1 s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32) =
      (stageP2PostP1At (A.atState lim st1 s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
       lsLogOff ∗ stackAt sp (dpClosSubStack B)) ∗ Fr_p2 := by
    dsimp only [Fr_p2, LeftoverBase, sp]
    sep_ac_rfl
  rw [hpre_split, ← stageP1ProgPlaced_eq_dpPollProgPlaced mmpl gh W]
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by
    change ((s0.sp - 0xcd0#64) &&& 15#64 == 0#64) = true; rw [← hs1_sp]; exact halign1
  have hx29_fp : s1.readReg64 .x29 = fp :=
    hx29.trans (bv_sub_add_lit s0.sp 3280 3184).symm
  have hsame_le :
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt ≤ dpClosSubStack B :=
    Nat.le_trans
      (by decide : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt ≤ 1048576 - 3280)
      (Nat.le_add_right _ _)
  have htr_pref : s0.trace <+: s1.trace := by rw [htr1]
  let ikBSk : List UInt8 :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => vecU8 kp₀.privateKey.bytes | .error _ => List.replicate 32 0
  let ikBPk : List UInt8 :=
    match StoresGhost.opened.identity.keyPair cliIo.rd y.g.F with
    | .ok kp₀ => vecU8 kp₀.identityKey.publicKey.bytes | .error _ => List.replicate 32 0
  have hikBSk_len : ikBSk.length = 32 := by dsimp only [ikBSk]; split <;> [exact vecU8_length _; simp]
  have hikBPk_len : ikBPk.length = 32 := by dsimp only [ikBPk]; split <;> [exact vecU8_length _; simp]
  have hkp_sk : ∀ kp₀ : IdentityKeyPair,
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp₀) → kp₀.privateKey.bytes.toList = bytesToBv8 ikBSk := by
    intro kp₀ hrel; dsimp only [ikBSk]; rw [cliPollSelf_kpRel_ok_placed hrel, bytesToBv8_vecU8]
  have hkp_pk : ∀ kp₀ : IdentityKeyPair,
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp₀) →
      kp₀.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk := by
    intro kp₀ hrel; dsimp only [ikBPk]; rw [cliPollSelf_kpRel_ok_placed hrel, bytesToBv8_vecU8]
  have hikAPk_len : (mkBadKemHdr y.g.msg kp).ikAPk.length = 32 := vecU8_length _
  have hekAPk_len : (mkBadKemHdr y.g.msg kp).ekAPk.length = 32 := vecU8_length _
  have hkemCt_len : (mkBadKemHdr y.g.msg kp).kemCt.length = 1568 := by simp [mkBadKemHdr]
  have hH := cliStageP2ClosureHooksPlaced mmpl gh W hh
  have hBase := r20a6w_baseCalleesPlaced4K mmpl gh W hh
  have hPure := r20a6w_pureCalleesPlaced4K mmpl gh W hh
  have hSameAcct := isSameAccountDistinctSpecExt_to_at_placed hBase.isSameAccount
  have hInitBob :=
    LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.of_full_badKem_errOwned_placed
      (cliInitBob_badKem_errOwned_full_placed_ok_on_stageP1 r20a6w_dummyExtras mmpl gh W hG)
  have hSelfVt := cliPollSelf_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.peer (cliKitStk B) hDropNz
  have hSelfOk := cliPollSelf_kitPlacedOk_stagesHooks mmpl gh W B y.g.F y.g.peer hDropNz hh hRead
  have hSpkVt := cliPollSpk_vtablesPlacedOk (A := A.repAlloc) y.g.F y.g.msg.signedPreKeyId (cliKitStk B) hDropNz
  have hSpkOk := cliPollSpk_kitPlacedOk mmpl gh W B y.g.F y.g.msg.signedPreKeyId hDropNz hh hRead
  have hKpkVt := cliPollKpk_vtablesPlacedOk (A := A.repAlloc) y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) hDropNz
  have hKpkOk := cliPollKpk_kitPlacedOk mmpl gh W B y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey hDropNz hh hRead
  have hfs1 : FsAt (fun f => f = y.g.F) True (dpPollProgPlaced ext) s1 :=
    .inr ⟨trivial, hh.fs (dpPollProgPlaced ext) 518, hs1_files⟩
  let finishArm := fun (w : PathAEntryWords)
      (hopkWord : ∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id)
      (evs_p2 : List AllocEvent) (sf : State) (P_f : SepProp)
      (hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt evs_p2)
      (_hsteps1f : Steps (stageP1ProgPlaced ext) s1 sf)
      (htrf : sf.trace = s1.trace) (hspf : sf.sp = sp + 3280#64)
      (hcsf : _) (hvregsf : calleeSavedVRegs sf = calleeSavedVRegs s0)
      (hPf_err : P_f ⊢
        ((decResAt A.repAlloc y.out (.error err0) ∗ anyHeap) ∗
          (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B)).storeAt
            (y.g.stores + 80#64) StoresGhost.opened.signed ∗
          (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey
            (cliKitStk B)).storeAt (y.g.stores + 120#64) StoresGhost.opened.kyber ∗
          (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).storeAt
            (y.g.stores + 200#64) StoresGhost.opened.oneTime ∗
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).identityAt
            y.g.stores StoresGhost.opened.identity ∗
          LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
            A lim (M.stepEvents evs_p2 st1) s0 sf sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
            y.g.peerA y.g.meA
            y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym)
            y.g.peerA (y.g.msgA + 200#64) (mkBadKemHdr y.g.msg kp) kp.ciphertext
            y.g.msg.message.messageVersion
            w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
            y.g.me y.g.peer (dpClosSubStack B)
            (badKemInnerFramePlacedBudget A y kp rngPtr sp)) ∗ Fr_p2) =>
    show (Steps (dpPollProgPlaced ext) s0 sf → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withLsFrozen lsmpl
          (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf from by
      refine ⟨?_, hspf.trans (sp_frame_sub_add s0.sp), calleeSavedPreserved_of_closure hcsf hvregsf⟩
      intro hsteps0f hmf
      have hevs_eq : M.stepEvents (evs_p1 ++ evs_p2) y.st = M.stepEvents evs_p2 st1 :=
        AllocCostModel.stepEvents_append M evs_p1 evs_p2 y.st
      have hent : P_f ⊢
          dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt A.repAlloc y.out (.error err0) ∗
          storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
          preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
          protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
          lsLogOff ∗ A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
          memRegion y.cx 32 ∗ Leftover := by
        rw [hevs_eq]
        refine Entails.trans hPf_err ?_
        refine Entails.trans (sepConj_mono_left
          (p2BadKemErrFrame_fold_placedBudget A lim y kp w (M.stepEvents evs_p2 st1) s0 sf
            sp fp rngPtr err0 hv4 hkp rfl hopkWord)) ?_
        dsimp only [Fr_p2, Leftover, LeftoverBase, sp]
        exact Entails.of_eq (by sep_ac_rfl)
      exact d3_pollPost_of_stageP2_err_placedBudget A lim B S
        (r20f_toSkeletonRunHooksPlaced hh) stk' hneed hstk63 y s0 sf
        (evs_p1 ++ evs_p2) err0 P_f Leftover R herr0_p herr0_s hans (hevs_sub evs_p2 hevs2)
        hsteps0f (htrf.trans htr1) hent hmf
  refine sepWPp_with_steps ?_
  cases opt with
  | none =>
    have hunpack :
        ((stageP2PostP1At (A.atState lim st1 s1)
           y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt scopeKit A.repAlloc y.fut none ∗
         preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
         protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         lsLogOff ∗ stackAt sp (dpClosSubStack B)) ∗ Fr_p2) ⊢
          ∃∗ w : PathAEntryWords,
            ⌜(y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63) ∧
              (∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id)⌝ ∗
            LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced
              A lim
              (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
              (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
              (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
              (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
              st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
              y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
              y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
              (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
              0#8 0#8 w.b_4b0 w.b_4f1 0#8
              w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
              StoresGhost.opened.signed StoresGhost.opened.kyber
              StoresGhost.opened.oneTime StoresGhost.opened.identity
              y.g.me y.g.peer (dpClosSubStack B)
              (badKemInnerFramePlacedBudget A y kp rngPtr sp ∗ Fr_p2) := by
      refine Entails.trans (sepConj_mono_left
        (stageP2_entry_unpack_badKem_pathA_placedBudget A lim y kp st1 s0 s1 sp fp
          rngPtr v_a8 v_b8 v_d0 hv4 hkp rfl hstoreOk hfPeer hsub)) ?_
      simp only [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hopkWord => ?_
      refine Entails.trans (sepConj_mono_left
        (r20a6w_stageP2BadKemPreAt_dup_kyber A lim y kp w st1 s0 s1 sp fp rngPtr v_a8 v_b8 v_d0)) ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hkyb => Entails.pure_right ⟨hkyb, hopkWord⟩ ?_
      unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2BadKemPreAtPlaced
      exact Entails.of_eq (by sep_ac_rfl)
    refine sepWPp_conseq_pre hunpack ?_
    refine SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨⟨hct_nz, hct_bd⟩, hopkWord⟩ => ?_
    have ⟨hArm3_eq, hOk14_eq⟩ := r20a6w_opk_env_eq
      (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B)).getBoxSize)
      (spkPoll := (cliPollSpkFullBudgetEnv A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.signed y.g.msg.signedPreKeyId)
      (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
      (kpkPoll := (cliPollKpkFullBudgetEnv A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.kyber kp.preKeyId)
      (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
      (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)).getBoxSize)
      (pkPoll1 := (cliPollPkFullBudgetEnv A.repAlloc y.g.F w.opkWord (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.oneTime)
      (pkPoll2 := (cliPollPkFullBudgetEnv A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.oneTime)
      (kpBox := (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize)
      (pm := y.g.msg) (kp := kp) (opkWord := w.opkWord)
      hopkWord (fun hw => by rw [hw]) (fun hw => by rw [hw])
    have hstk := stageP2V1CallStack_le_subStack_placed (A := A.repAlloc)
      y.g.F y.g.peer y.g.msg.signedPreKeyId kp.preKeyId w.opkWord y.g.msg.baseKey B
    have hfs := stageP1ProgPlaced_eq_dpPollProgPlaced mmpl gh W ▸
      cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer y.g.msg.signedPreKeyId kp.preKeyId
        w.opkWord y.g.msg.baseKey B hfs1
    exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPathAPlacedBudget.stageP2_pathA_badKem_kits_memInv_at_placed
      StageP2MemInv.frozen ext hH hPure hSameAcct hInitBob
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
      hSelfVt hSelfOk
      (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B) ReadEnv)
      hSpkVt hSpkOk
      (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) ReadEnv)
      hKpkVt hKpkOk
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc y.g.F w.opkWord (cliKitStk B) ReadEnv)
      (cliPollPk_vtablesPlacedOk (A := A.repAlloc) y.g.F w.opkWord (cliKitStk B) hDropNz)
      (cliPollPk_kitPlacedOk mmpl gh W B y.g.F w.opkWord hDropNz hh hRead)
      (dpClosSubStack B)
      (Nat.le_trans (p2_callStack_le_v1CallStack _ _ _ _) hstk)
      hsame_le
      (Nat.le_trans LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.p2_badKem_entry_le_stageP2bStack
        (Nat.le_trans LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_stageP2bStack_le_bobV1
          (Nat.le_trans (p2_bobStack_le_v1CallStack _ _ _ _) hstk)))
      st1 s0 s1 (badKemInnerFramePlacedBudget A y kp rngPtr sp ∗ Fr_p2) _
      sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
      y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkBadKemHdr y.g.msg kp) kp.ciphertext ikBSk ikBPk
      y.g.msg.message.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer
      (hfits_p2.mono fun evs hevs => by
        unfold StageP2BadKemRejectEnv; rw [hkpkId]
        rcases hevs with h1 | h2 | h3 | hok4
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
        · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (SeqEnv.inl hok4)))))
      (fun evs14 hevs14 => by
        rw [hOk14_eq] at hevs14
        have hArm4 := hfits_p2.mono fun evs h4 => by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        exact r20a6w_fitsEnv_drop_freeOnly (hArm4.seq_right hevs14))
      (fun _ _ _ _ _ _ _ _ _ _ evs14 evsKp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hevs14 hevsKp => by
        rw [hOk14_eq] at hevs14
        have hArm5 := hfits_p2.mono fun evs h5 => by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]
          exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
        exact r20a6w_fitsEnv_step3 hArm5 hevs14 hevsKp
          (r20a6w_freeOnlyEvs_rustDeallocEvents
            (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize 8))
      hct_nz hsp_sub hikBSk_len hikBPk_len hikAPk_len hekAPk_len hkemCt_len hct_bd hbadKem hro1 hfs
      rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      (fun id hid => hopkWord id ((hdrOpkIdBv?_mkBadKemHdr y.g.msg kp).symm.trans hid))
      (fun id hid => (hopkWord id ((hdrOpkIdBv?_mkBadKemHdr y.g.msg kp).symm.trans hid)).symm)
      (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      hkp_sk hkp_pk (Or.inr (distinctSid_of_not_sameAcct_d3 hnotSameSid))
      hpc1 hrun1 hs1_sp hsp_align htr_pref hvregs1
      hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx29_fp
      (fun e evs sf P_f _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, List.append_nil] at htrf
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inl hevs
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F y.g.msg.signedPreKeyId (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec e evs sf P_f _ _ _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, List.append_nil, List.append_nil] at htrf
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inl hevs)
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec _kpkRec opkId e evs sf P_f _ _ _ _ hopkHdr _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_getEvs_nil,
            List.append_nil, List.append_nil, List.append_nil] at htrf
        rw [← hopkHdr, hArm3_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inl hevs))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F w.opkWord (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec _kpkRec wOpk e evs sf P_f _ _ _ _ _ _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_opkOkEvs_nil,
            cliPollSelf_kpEvs_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htrf
        have hopkUpd := cliPollPk_opkOkUpdate_eq A.repAlloc y.g.F w.opkWord (cliKitStk B)
          (hdrOpkIdBv? (mkBadKemHdr y.g.msg kp)) wOpk
        rw [hopkUpd] at hPf
        unfold P2V1Arm4Env at hevs; rw [hOk14_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs)))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        have hkpEnt := Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)
        refine Entails.trans hPf (Entails.trans (sepConj_mono_left hkpEnt) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _ _ _ _ _ _ wOpk _ _ _ errTag w2 w3 w4 w5 w6 evs sf P_f
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hevs _ _ _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_opkOkEvs_nil,
            cliPollSelf_kpEvs_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htrf
        have hopkUpd := cliPollPk_opkOkUpdate_eq A.repAlloc y.g.F w.opkWord (cliKitStk B)
          (hdrOpkIdBv? (mkBadKemHdr y.g.msg kp)) wOpk
        rw [hopkUpd] at hPf
        unfold P2V1Arm5EnvOfAcceptErr at hevs; rw [hOk14_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g none evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inr (Or.inr hevs)))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        have hbobEnt := badKemSpeWords_entails_decResAt_anyHeap A.repAlloc y.out errTag w2 w3 w4 w5 w6 err0
        refine Entails.trans (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl : _ =
          (speWordsAt y.out errTag w2 w3 w4 w5 w6 ∗ pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4) ∗ _))) ?_
        refine Entails.trans (sepConj_mono_left hbobEnt) ?_
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
  | some r =>
    obtain ⟨sess, hcur⟩ :=
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.currentSession_some_of_cliPollSessPlaced_loadRel
        hload_rel
    have hloadS : loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
      LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.loadRec_of_cliPollSessPlaced_loadRel
        hinjK hsub hfPeer hload_rel
    have hnm := hnoMatch r sess hloadS hcur
    have hunpack :
        ((stageP2PostP1At (A.atState lim st1 s1)
           y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
           (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
           (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
         p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗
         preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
         protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
         protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
         storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
         lsLogOff ∗ stackAt sp (dpClosSubStack B)) ∗ Fr_p2) ⊢
          ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
            ⌜(y.g.msgG.kyberPtr ≠ 0#64 ∧ kp.ciphertext.length < 2 ^ 63) ∧
              (∀ id : BitVec 32, y.g.msg.preKeyId = some id → w.opkWord = id)⌝ ∗
            LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2OverBadKemPreAtPlaced
              A lim
              (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
              (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
              (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
              (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
              st1 s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
              y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
              y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
              (mkBadKemHdr y.g.msg kp) kp.ciphertext y.g.msg.message.messageVersion
              0#8 0#8 w.b_4b0 w.b_4f1 0#8
              w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
              StoresGhost.opened.signed StoresGhost.opened.kyber
              StoresGhost.opened.oneTime StoresGhost.opened.identity
              y.g.me y.g.peer g recG sess (dpClosSubStack B)
              (badKemInnerFramePlacedBudget A y kp rngPtr sp ∗ Fr_p2) := by
      refine Entails.trans (sepConj_mono_left
        (stageP2_entry_unpack_badKem_over_placedBudget A lim y r sess kp st1 s0 s1 sp fp
          rngPtr v_a8 v_b8 v_d0 hcur hv4 hkp rfl hstoreOk hfPeer hsub)) ?_
      simp only [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
      refine Entails.sepExists_elim fun recG => Entails.sepExists_right recG ?_
      refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
      rw [sepConj_assoc]
      refine Entails.pure_left fun hp => Entails.pure_right hp ?_
      unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.stageP2OverBadKemPreAtPlaced
      exact Entails.of_eq (by sep_ac_rfl)
    refine sepWPp_conseq_pre hunpack ?_
    refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG =>
      SepWPp.exists_elim fun w => SepWPp.pure_left fun ⟨⟨hct_nz, hct_bd⟩, hopkWord⟩ => ?_
    have ⟨hArm3_eq, hOk14_eq⟩ := r20a6w_opk_env_eq
      (spkBox := (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B)).getBoxSize)
      (spkPoll := (cliPollSpkFullBudgetEnv A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.signed y.g.msg.signedPreKeyId)
      (kpkBox := (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B)).getBoxSize)
      (kpkPoll := (cliPollKpkFullBudgetEnv A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.kyber kp.preKeyId)
      (pkBox1 := (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B)).getBoxSize)
      (pkBox2 := (cliPollPkKitPlaced A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B)).getBoxSize)
      (pkPoll1 := (cliPollPkFullBudgetEnv A.repAlloc y.g.F w.opkWord (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.oneTime)
      (pkPoll2 := (cliPollPkFullBudgetEnv A.repAlloc y.g.F (pmPreKeyId y.g.msg) (cliKitStk B) ReadEnv).getPollEnv
        StoresGhost.opened.oneTime)
      (kpBox := (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize)
      (pm := y.g.msg) (kp := kp) (opkWord := w.opkWord)
      hopkWord (fun hw => by rw [hw]) (fun hw => by rw [hw])
    have hstk := stageP2OverV1CallStack_le_subStack_badKem_placed (A := A.repAlloc)
      y.g.F y.g.peer y.g.msg.signedPreKeyId kp.preKeyId w.opkWord y.g.msg.baseKey B
    have hfs := stageP1ProgPlaced_eq_dpPollProgPlaced mmpl gh W ▸
      cliPollStageP2_fsAt_stages_placed hh y.g.F y.g.peer y.g.msg.signedPreKeyId kp.preKeyId
        w.opkWord y.g.msg.baseKey B hfs1
    have hPromMissAt :=
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget.promoteMatchingMissAt_placed_of_gen
        (LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.cliPromoteMatchingMissGen_placed_d3
          A.repAlloc mmpl gh W)
        y.fut g recG sess 4#8 (5#8 :: bytesToBv8 (mkBadKemHdr y.g.msg kp).ekAPk)
        (not_p2SessMatchesMsg_of_v4_badKem kp hv4 hnm)
        (by
          rw [bytesToBv8_mkBadKemHdr_ekAPk]
          exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3PathAKitsPlacedBudget.baseKey_serialize_length y.g.msg.baseKey)
    exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopPlacedBudget.stageP2_over_badKem_kits_memInv_at_placed
      StageP2MemInv.frozen ext hH hPure hSameAcct hInitBob
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      (cliPollSelfBudgetEnv A.repAlloc y.g.F y.g.peer (cliKitStk B) ReadEnv)
      hSelfVt hSelfOk
      (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc y.g.F y.g.msg.signedPreKeyId (cliKitStk B) ReadEnv)
      hSpkVt hSpkOk
      (cliPollKpkKitPlaced A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) ReadEnv)
      hKpkVt hKpkOk
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc y.g.F w.opkWord (cliKitStk B) ReadEnv)
      (cliPollPk_vtablesPlacedOk (A := A.repAlloc) y.g.F w.opkWord (cliKitStk B) hDropNz)
      (cliPollPk_kitPlacedOk mmpl gh W B y.g.F w.opkWord hDropNz hh hRead)
      (dpClosSubStack B)
      ((stageP2OverCallStack4K_eq _ _ _ _).symm ▸
        Nat.le_trans (p2_over_callStack_le_v1CallStack _ _ _ _) hstk)
      (Nat.le_trans (p2_sub56Stack_le_v1CallStack _ _ _ _)
        (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack _ _ _ _) hstk))
      (Nat.le_trans p2_over_dropSS3_le_overPure
        (Nat.le_trans (p2_over_pure_le_v1CallStack _ _ _ _) hstk))
      hsame_le
      (Nat.le_trans LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemP2TopSub5PlacedBudget.p2_badKem_entry_le_stageP2bStack
        (Nat.le_trans LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_stageP2bStack_le_bobV1
          (Nat.le_trans (p2_bobStack_le_v1CallStack _ _ _ _)
            (Nat.le_trans (p2_over_baseV1Call_le_v1CallStack _ _ _ _) hstk))))
      st1 s0 s1 (badKemInnerFramePlacedBudget A y kp rngPtr sp ∗ Fr_p2) _
      sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 200#64) (y.g.stores + 80#64) (y.g.stores + 120#64)
      y.g.peerA (y.g.msgA + 200#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkBadKemHdr y.g.msg kp) kp.ciphertext ikBSk ikBPk
      y.g.msg.message.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord kp.preKeyId y.g.msg.registrationId y.g.msg.signedPreKeyId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer g recG sess hPromMissAt
      (hfits_p2.mono fun evs hevs => by
        unfold StageP2BadKemRejectEnv; rw [hkpkId]
        dsimp only [P2OverSub1To4Env, P2OverSub1To3Arm1Env, P2OverSub1To3Arm2Env,
          P2OverSub1To4Arm3Env, P2OverSub1To4OkEnv] at hevs
        rcases hevs with h1 | h2 | h3 | hok4
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · rw [hArm3_eq] at h3; exact Or.inr (Or.inr (Or.inl h3))
        · rw [hOk14_eq] at hok4; exact Or.inr (Or.inr (Or.inr (Or.inl (SeqEnv.inl hok4)))))
      (fun evs14 hevs14 => by
        dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
        have hArm4 := hfits_p2.mono fun evs h4 => by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]
          exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        exact r20a6w_fitsEnv_drop_freeOnly (hArm4.seq_right hevs14))
      (fun _ _ _ _ _ _ _ _ _ _ evs14 evsKp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hevs14 hevsKp => by
        dsimp only [P2OverSub1To4OkEnv] at hevs14; rw [hOk14_eq] at hevs14
        have hArm5 := hfits_p2.mono fun evs h5 => by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]
          exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
        exact r20a6w_fitsEnv_step3 hArm5 hevs14 hevsKp
          (r20a6w_freeOnlyEvs_rustDeallocEvents
            (cliPollSelfKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).kpBoxSize 8))
      hct_nz hsp_sub hikBSk_len hikBPk_len hikAPk_len hekAPk_len hkemCt_len hct_bd hbadKem hro1 hfs
      rfl (fun r' hrel _ => cliPollSpk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      rfl (fun r' hrel _ => cliPollKpk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      (fun id hid => hopkWord id ((hdrOpkIdBv?_mkBadKemHdr y.g.msg kp).symm.trans hid))
      (fun id hid => (hopkWord id ((hdrOpkIdBv?_mkBadKemHdr y.g.msg kp).symm.trans hid)).symm)
      (fun _id r' _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hstoreOk.preKeysWf r' hrel)
      hkp_sk hkp_pk (Or.inr (distinctSid_of_not_sameAcct_d3 hnotSameSid))
      hpc1 hrun1 hs1_sp hsp_align htr_pref hvregs1
      hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx29_fp
      (fun e evs sf P_f _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, List.append_nil] at htrf
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inl hevs
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F y.g.msg.signedPreKeyId (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec e evs sf P_f _ _ _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, List.append_nil, List.append_nil] at htrf
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inl hevs)
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F kp.preKeyId y.g.msg.signedPreKeyId y.g.msg.baseKey (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec _kpkRec opkId e evs sf P_f _ _ _ _ hopkHdr _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_getEvs_nil,
            List.append_nil, List.append_nil, List.append_nil] at htrf
        dsimp only [P2OverSub1To4Arm3Env] at hevs
        rw [← hopkHdr, hArm3_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inl hevs))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        refine Entails.trans hPf (Entails.trans
          (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap_placed A.repAlloc
            y.g.F w.opkWord (cliKitStk B) y.out e err0)) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _spkRec _kpkRec wOpk e evs sf P_f _ _ _ _ _ _ hevs _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_opkOkEvs_nil,
            cliPollSelf_kpEvs_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htrf
        have hopkUpd := cliPollPk_opkOkUpdate_eq A.repAlloc y.g.F w.opkWord (cliKitStk B)
          (hdrOpkIdBv? (mkBadKemHdr y.g.msg kp)) wOpk
        rw [hopkUpd] at hPf
        unfold P2OverV1Arm4Env P2V1Arm4Env at hevs; rw [hOk14_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inr (Or.inl hevs)))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        have hkpEnt := Entails.trans
          (cliPollSelf_kpErr_entails_decResAt_err_placed A.repAlloc y.g.F y.g.peer (cliKitStk B) y.out e err0)
          (entails_sepConj_anyHeap _)
        refine Entails.trans hPf (Entails.trans (sepConj_mono_left hkpEnt) ?_)
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))
      (fun _ _ _ _ _ _ wOpk _ _ _ errTag w2 w3 w4 w5 w6 evs sf P_f
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hevs _ _ _ _ htrf hspf hcsf hvregsf _ hPf hsteps1f => by
        rw [cliPollSpk_getEvs_nil, cliPollKpk_getEvs_nil, cliPollPk_opkOkEvs_nil,
            cliPollSelf_kpEvs_nil, List.append_nil, List.append_nil, List.append_nil, List.append_nil] at htrf
        have hopkUpd := cliPollPk_opkOkUpdate_eq A.repAlloc y.g.F w.opkWord (cliKitStk B)
          (hdrOpkIdBv? (mkBadKemHdr y.g.msg kp)) wOpk
        rw [hopkUpd] at hPf
        unfold P2OverV1Arm5EnvOfAcceptErr P2V1Arm5EnvOfAcceptErr at hevs
        rw [hOk14_eq] at hevs
        have hevs2 : StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g (some r) evs := by
          unfold StageP2BadKemRejectEnv; rw [hkpkId]; exact Or.inr (Or.inr (Or.inr (Or.inr hevs)))
        refine finishArm w hopkWord evs sf P_f hevs2 hsteps1f htrf hspf hcsf hvregsf ?_
        have hbobEnt := badKemSpeWords_entails_decResAt_anyHeap A.repAlloc y.out errTag w2 w3 w4 w5 w6 err0
        refine Entails.trans (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl : _ =
          (speWordsAt y.out errTag w2 w3 w4 w5 w6 ∗ pqxdhBadKemErrPayloadAt A.repAlloc errTag w2 w3 w4) ∗ _))) ?_
        refine Entails.trans (sepConj_mono_left hbobEnt) ?_
        unfold LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BadKemP2KitsPlacedBudget.p2BadKemErrFrameAtPlaced
        exact Entails.of_eq (by sep_ac_rfl))

/-- `[LibsignalFullPlacement]` Stage-P2 `SepWPp` rejection theorem for `MsgCondBadKem`. -/
theorem stageP2_badKem_reject_full_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State) (opt : Option (SessionRecord (List (BitVec 8))))
    (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hstoreOk : DecPkStoreOk ⟨W.C, W.Q⟩ y.g.F)
    (hbadCond : MsgCondBadKem Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st)
      (StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt))
    (hevs_sub : ∀ evs_p2,
      StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv y.g opt evs_p2 →
      DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val (.ok opt))
    (htr1 : s1.trace = s0.trace) (hro1 : LibsignalFrozen lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x868#64) (hrun1 : s1.status = .Running)
    (halign1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym))
    (hs1_files : s1.fs.files = y.g.F) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
       preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
       protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
      (fun sf P_f =>
        (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf →
          (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (withLsFrozen lsmpl
            (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic y s0 sf ∗ R)) := by
  let _ := hcoins
  exact r20a6w_stageP2_badKem_reject_body
    A lim mmpl gh W B S Scope hDropNz hG hh hRead hinjK hsub stk' hneed hstk63
    y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0
    hfPeer hstoreOk hbadCond hans
    hfits_p2 hevs_sub hload_rel htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1 hs1_files

private theorem r20f_stageP2BadKemRejectEnv_nonempty [LibsignalPlacement]
    {A : CryptoVerification.RustHeap.RustAlloc} {B : RunBudgets}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {AcceptErrEnv : List AllocEvent → Prop} (g : DecPkGhost) :
    ∃ opt0 evs2, StageP2BadKemRejectEnv (A := A) B ReadEnv AcceptErrEnv g opt0 evs2 :=
  ⟨none, _, Or.inl (Or.inl rfl)⟩

/-- `[LibsignalFullPlacement]` `dpPollProgPlaced` `subroutine_ok` rejection contract for `MsgCondBadKem`. -/
theorem decPk_badKem_reject_poll_full_placedBudget [LibsignalFullPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hG : CliGhostAllocHooks M A lim gh)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
      MsgCondBadKem Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (withLsFrozen lsmpl
        (dpPollSpecStateBudget
          (dpSlotPollKStatePlaced A lim
            (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv
              (StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv))
            B S)
          stk')) := by
  let P2Env := StageP2BadKemRejectEnv (A := A.repAlloc) B ReadEnv PqxdhAcceptBadKemErrEnv
  let DecPkEnv := DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv P2Env
  let hhSkel := r20f_toSkeletonRunHooksPlaced hh
  apply CryptoVerification.SignalSession.Cli.RunProofs.Poll.subroutine_ok_of_sepWPp_steps
  intro y R s0 hpc hrun hpre hsp
  obtain ⟨hfroz0, hp0⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsFrozen hpre
  have hpre_cro : s0.mem ⊨
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).pre y s0 ∗ R := by
    dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded.of_libsignalFrozen hfroz0, hp0⟩
  obtain ⟨hpure, hm_base⟩ :=
    LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.dpPollPre_unpack_d3_placedBudget
      (W := W) (Scope := Scope)
      (MsgCond := fun F peer me pm =>
        MsgCondBadKem Scope F peer me pm ∧ ∀ coins, S.decryptPrekey F peer me pm coins = some none)
      (fun F peer me pm hf hd =>
        let ⟨h1, h2, h3, h4⟩ := hok F peer me pm hf hd
        ⟨h1, ⟨h2.keyPairLt, h2.preKeysWf, h2.baseKeysLt⟩, h3, h4⟩)
      stk' y R s0 hpre_cro
  obtain ⟨hbadCond, hAns0⟩ := hpure.msgCond
  have hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none :=
    hAns0 y.g.coins
  obtain ⟨b, htrusted⟩ :=
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.trusted_ok_of_filesOkPeer
      (peer := y.g.peer) hpure.filesOkPeer y.g.msg.identityKey
  cases b with
  | false =>
    exact LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.closure_untrusted_d3_placedBudget_ok
      A lim hDropNz mmpl gh W B S Scope hhSkel hRead hDeser hsub
      stk' hneed hstk63 y
      (fun evs hevs => hpure.fits evs (Or.inl hevs))
      (fun _ h => Or.inl h)
      R s0 hpc hrun hsp
      hpure.rocl hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.storeOk
      hans htrusted hm_base
  | true =>
    obtain ⟨opt0, evs2_0, hp2_0⟩ :=
      r20f_stageP2BadKemRejectEnv_nonempty (A := A.repAlloc) (B := B) (ReadEnv := ReadEnv)
        (AcceptErrEnv := PqxdhAcceptBadKemErrEnv) y.g
    have hfits_p1 : FitsEnv M lim y.st
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget.StageP1OkEnv
          (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer (cliKitStk B))
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollSessBudgetEnv
            A.repAlloc y.g.F y.g.peer B ReadEnv DeserEnv)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliPollIdBudgetEnv
            A.repAlloc y.g.F y.g.peer B ReadEnv)
          CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
          y.g.peer.val y.g.msg.identityKey) :=
      fun evs1 hevs1 =>
        ((LibsignalBinary.Heap.fitsEvents_append M lim evs1 evs2_0 y.st).mp
          (hpure.fits (evs1 ++ evs2_0) (Or.inr ⟨opt0, Or.inr ⟨evs1, evs2_0, rfl, hevs1, hp2_0⟩⟩))).1
    refine LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget.closure_trusted_p1_d3_placedBudget_bind
      A lim hDropNz mmpl gh W B S Scope hhSkel hRead hDeser hsub
      stk' hneed hstk63 y hfits_p1 R s0 hpc hrun hsp hpure.stk_le_sp
      hpure.rocl hpure.x0 hpure.x1 hpure.x2 hpure.files_eq hpure.filesOkPeer hpure.storeOk
      htrusted hm_base ?_
    intro opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hevs_p1 hload_rel hsteps01 htr1 _hro1 hs1_sp
      hsp_sub hpc1 hrun1 halign1 hregs1
    have hfroz1 : LibsignalFrozen lsmpl s1.mem :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hfroz0 hsteps01.keepsFrozen
    have hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st) (P2Env y.g opt) :=
      fun evs2 hp2_evs =>
        ((LibsignalBinary.Heap.fitsEvents_append M lim evs_p1 evs2 y.st).mp
          (hpure.fits (evs_p1 ++ evs2) (Or.inr ⟨opt, Or.inr ⟨evs_p1, evs2, rfl, hevs_p1, hp2_evs⟩⟩))).2
    have hevs_sub : ∀ evs_p2, P2Env y.g opt evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2) :=
      fun evs_p2 hp2_evs => Or.inr ⟨opt, Or.inr ⟨evs_p1, evs_p2, rfl, hevs_p1, hp2_evs⟩⟩
    have hs1_files : s1.fs.files = y.g.F :=
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget.cliFiles_eq_of_trace_eq_placed
        (i := 518) hhSkel hsteps01 htr1).trans hpure.files_eq
    exact stageP2_badKem_reject_full_placedBudget
      A lim mmpl gh W B S Scope hDropNz hG hh hRead hinjK hsub stk' hneed hstk63
      y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0
      hpure.filesOkPeer ⟨hpure.storeOk.keyPairLt, hpure.storeOk.preKeysWf, hpure.storeOk.baseKeysLt⟩
      hbadCond hans hpure.coins_lt
      hfits_p2 hevs_sub hload_rel htr1 hfroz1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1 hs1_files

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemRejectAuxPlacedBudget
