/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3PathAKitsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Folds

/-!
# Budget-Threaded `v3` (`"X3DH no longer supported"`) Poll Rejection

Proves `stageP2_v3_reject_placedBudget` and `decPk_v3_reject_poll_placedBudget` for message-version
`3` `PreKeySignalMessage`s under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3RejectPlacedBudget

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Process ProofLib ProofLib.Variant SepProp
open CryptoGames.LibsignalSessionApi (ApiError PreKeySignalMessage Session SessionRecord)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (p1LoadedRecordAt p2CoroScratchTailAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (stageP2OverPureAndErrStack)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyActive10At processPrekeyPostTrustAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal PreKeyMsgGhost RecordGhost apiDecResultAt preKeyMsgAt sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost protocolAddressAt signalMessageAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli (cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym cliSignedPreKeyVtSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt dpPollNeed)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm decPkDef dpFutDoneAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (LsTokenInit StageP1PostRegs apiDecResultAt_proto_entails_decResAt calleeSavedPreserved_of_closure cliKitStk cliPollSessKitPlaced closStackUnusedP1OkAt clos_stack_3280_split_for_p1_ok coroCopyAt_eq_head3_tail11 coroCopyTail11At coroUnusedP1At coro_unused_split_p2v1 dpClosSubStack dpPollEntryPlaced dpPollProgPlaced p2_coro_err_fold preKeyMsgAt_eq_base_idKey_sep preKeyMsgRemBaseIdKeyAt_eq_ver_sep preKeyMsgRemMatchedAt processPrekeyInnerInitAt_eq_330_388_rem23 processPrekeyInnerRem23At savedRegs_entails_memRegion_96' sepWPp_conseq_pre sessionRecordAt_some_eq_prev_sess sp_frame_sub_add stageP2PostP1At)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (EncodeInjOn FilesOkPeer loadRec scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (drop_session_structure3_placed_ok_on_stageP1)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3PollRejectAuxPlacedBudget (DecPkD3UntypedPollEnv DecPkStoreOk MsgCondPkToENone StageP2V3RejectEnv cliPromoteMatchingMissGen_placed_d3 cliStageP2ClosureHooksPlaced_d3 cliStrToOwnedLocal2_placedBudget_ok d3_pollPost_of_stageP2_err_placedBudget decPkDef_eq_some_none_of_d3b3 decPk_d3_untyped_poll_reject_placedBudget stageP1ProgPlaced_eq_dpPollProgPlaced stageP2V3RejectEnv_nonempty)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3PathAKitsPlacedBudget (baseKey_serialize_length not_p2SessMatchesMsg_of_v3' pkToE?_eq_none_of_v3 stageP2_over_v3_kits_placed stageP2_pathA_v3_kits_placed v3PubKeySerialize_placedBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (DpPollGhostStateBudget dpPollSpecStateBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced sessDeserializeSpecPlaced)
/-! ## 1. `v3` Message Condition & Pure `decPkDef` Evaluation -/

def MsgCondV3 (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer _me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  pm.messageVersion = 3#8 ∧
  ∀ r s, loadRec Scope F peer = .ok (some r) → r.currentSession = some s → ¬ SessMatchesPm s pm

theorem decPkDef_eq_some_none_of_v3
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    (hv3 : MsgCondV3 Scope F peer me pm) :
    decPkDef X W Scope F peer me pm coins = some none :=
  decPkDef_eq_some_none_of_d3b3 X W Scope F peer me pm coins (pkToE?_eq_none_of_v3 hv3.1) hv3.2

theorem msgCondPkToENone_of_v3
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (hparse : ∃ body : List (BitVec 8), CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse body = some pm)
    (hAcct : ¬ CryptoVerification.SignalSession.Cli.RunProofs.SameServiceId peer me)
    (hv3 : MsgCondV3 Scope F peer me pm) :
    MsgCondPkToENone Scope F peer me pm :=
  ⟨hparse, pkToE?_eq_none_of_v3 hv3.1, hAcct, hv3.2⟩

/-! ## 2. Spatial Split & Exit Fold Between `stageP2PostP1At` and `v3` Stage P2 Kits -/

def v3StackRemAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 8#64) 144 ∗ memRegion (sp + 564#64) 316 ∗ memRegion (sp + 916#64) 76 ∗
  memRegion (sp + 1016#64) 344 ∗ memRegion (sp + 1360#64) 1344 ∗ memRegion (sp + 2752#64) 432

theorem closStack_v3_split (sp : BitVec 64) :
    closStackUnusedP1OkAt sp ∗ memRegion (sp + 992#64) 368 =
      memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗
      memRegion (sp + 2704#64) 48 ∗ v3StackRemAt sp := by
  unfold closStackUnusedP1OkAt v3StackRemAt
  rw [ProofLib.memRegion_split (sp + 564#64) 316 112 (by decide),
      ProofLib.memRegion_split (sp + 564#64 + 316#64) 36 76 (by decide),
      ProofLib.memRegion_split (sp + 992#64) 24 344 (by decide),
      ProofLib.memRegion_split (sp + 1360#64) 1344 480 (by decide),
      ProofLib.memRegion_split (sp + 1360#64 + 1344#64) 48 432 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl

private theorem closStack_v3_fold (sp0 : BitVec 64) (s0 : State)
    (u98 ua0 ua8 ub0 ub8 uc0 uc8 ud0 : BitVec 64) :
    let sp := sp0 - 3280#64
    (sp ↦₆₄ 0#64) ∗
    ((sp + 152#64) ↦₆₄ u98) ∗ ((sp + 160#64) ↦₆₄ ua0) ∗
    ((sp + 168#64) ↦₆₄ ua8) ∗ ((sp + 176#64) ↦₆₄ ub0) ∗
    ((sp + 184#64) ↦₆₄ ub8) ∗ ((sp + 192#64) ↦₆₄ uc0) ∗
    ((sp + 200#64) ↦₆₄ uc8) ∗ ((sp + 208#64) ↦₆₄ ud0) ∗
    memRegion (sp + 216#64) 348 ∗ memRegion (sp + 880#64) 36 ∗
    memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
    v3StackRemAt sp ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0 ⊢ memRegion sp 3280 := by
  dsimp only
  let sp := sp0 - 3280#64
  have hsp_add : sp + 3280#64 = sp0 := sp_frame_sub_add sp0
  have hsaved : decryptPrekeySavedRegsAt (sp + 3280#64) s0 ⊢ cells (sp0 - 96#64) 12 := by
    rw [hsp_add, ← ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide)]
    exact savedRegs_entails_memRegion_96' sp0 s0
  have hjoin :
      memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗
      memRegion (sp + 2704#64) 48 ∗ v3StackRemAt sp =
      closStackUnusedP1OkAt sp ∗ memRegion (sp + 992#64) 368 :=
    (closStack_v3_split sp).symm
  rw [clos_stack_3280_split_for_p1_ok sp0]
  refine Entails.sepExists_right u98 (Entails.sepExists_right ua0
    (Entails.sepExists_right ua8 (Entails.sepExists_right ub0
      (Entails.sepExists_right ub8 (Entails.sepExists_right uc0
        (Entails.sepExists_right uc8 (Entails.sepExists_right ud0
          (Entails.sepExists_right 0#64 ?_))))))))
  refine Entails.trans (show _ ⊢
    decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
    (memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗
      memRegion (sp + 2704#64) 48 ∗ v3StackRemAt sp) ∗
    ((sp ↦₆₄ 0#64) ∗ ((sp + 152#64) ↦₆₄ u98) ∗ ((sp + 160#64) ↦₆₄ ua0) ∗
      ((sp + 168#64) ↦₆₄ ua8) ∗ ((sp + 176#64) ↦₆₄ ub0) ∗
      ((sp + 184#64) ↦₆₄ ub8) ∗ ((sp + 192#64) ↦₆₄ uc0) ∗
      ((sp + 200#64) ↦₆₄ uc8) ∗ ((sp + 208#64) ↦₆₄ ud0) ∗
      memRegion (sp + 216#64) 348) by exact Entails.of_eq (by dsimp only [sp]; sep_ac_rfl)) ?_
  rw [hjoin]
  refine Entails.trans (sepConj_mono_left hsaved) ?_
  exact Entails.of_eq (by dsimp only [sp]; sep_ac_rfl)

private def v3InnerFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (rngPtr sp v_b8 : BitVec 64) : SepProp :=
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
  coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
  memRegion (y.fut + 640#64) 24 ∗ memRegion (y.fut + 664#64) 20 ∗
  memRegion (y.fut + 684#64) 8 ∗ memRegion (y.fut + 692#64) 12 ∗
  memRegion (y.fut + 920#64) 96 ∗ memRegion (y.fut + 705#64) 7 ∗ memRegion (y.fut + 913#64) 7 ∗
  memRegion (y.fut + 1160#64) 8 ∗ memRegion (y.fut + 1200#64) 65 ∗ memRegion (y.fut + 1267#64) 5 ∗
  p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 1922#64) 6 ∗
  (sp ↦₆₄ 0#64) ∗ ((sp + 176#64) ↦₆₄ (y.fut + 912#64)) ∗
  ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ y.cx) ∗
  memRegion (sp + 216#64) 348 ∗ v3StackRemAt sp ∗
  signalMessageAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
  ((y.g.msgA + 200#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
  preKeyMsgRemMatchedAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
  protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
  protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
  storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened

private theorem coro_unused_split_v3 (fut : BitVec 64) :
    cells (fut + 920#64) 2 ∗ memRegion (fut + 592#64) 48 ∗ coroUnusedP1At fut ⊢
      ∃∗ b_4f1 : BitVec 8,
        cells (fut + 1016#64) 6 ∗ cells (fut + 1128#64) 4 ∗
        ((fut + 1265#64) ↦₈ b_4f1) ∗ cells (fut + 592#64) 6 ∗
        memRegion (fut + 640#64) 24 ∗ memRegion (fut + 664#64) 20 ∗
        memRegion (fut + 684#64) 8 ∗ memRegion (fut + 692#64) 12 ∗
        memRegion (fut + 920#64) 96 ∗ memRegion (fut + 705#64) 7 ∗ memRegion (fut + 913#64) 7 ∗
        memRegion (fut + 1160#64) 8 ∗ memRegion (fut + 1200#64) 65 ∗ memRegion (fut + 1267#64) 5 ∗
        p2CoroScratchTailAt fut ∗ memRegion (fut + 1922#64) 6 := by
  refine Entails.trans (coro_unused_split_p2v1 fut) ?_
  refine Entails.sepExists_elim fun u488 => Entails.sepExists_elim fun b4b0 =>
    Entails.sepExists_elim fun b4f1 => Entails.sepExists_right b4f1 ?_
  have h488 : ((fut + 1160#64) ↦₆₄ u488) ⊢ memRegion (fut + 1160#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion _ _
  have h4b0 : ((fut + 1200#64) ↦₈ b4b0) ∗ memRegion (fut + 1201#64) 64 ⊢ memRegion (fut + 1200#64) 65 := by
    rw [ProofLib.memRegion_split (fut + 1200#64) 1 64 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)
  refine Entails.trans (show _ ⊢
    ((fut + 1160#64) ↦₆₄ u488) ∗ (((fut + 1200#64) ↦₈ b4b0) ∗ memRegion (fut + 1201#64) 64) ∗
    (cells (fut + 1016#64) 6 ∗ cells (fut + 1128#64) 4 ∗
      ((fut + 1265#64) ↦₈ b4f1) ∗ cells (fut + 592#64) 6 ∗
      memRegion (fut + 640#64) 24 ∗ memRegion (fut + 664#64) 20 ∗
      memRegion (fut + 684#64) 8 ∗ memRegion (fut + 692#64) 12 ∗
      memRegion (fut + 920#64) 96 ∗ memRegion (fut + 705#64) 7 ∗ memRegion (fut + 913#64) 7 ∗
      memRegion (fut + 1267#64) 5 ∗ p2CoroScratchTailAt fut ∗ memRegion (fut + 1922#64) 6)
    by exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h488 (sepConj_mono_left h4b0)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem preKeyMsgAt_v3_eq (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) (hv3 : m.messageVersion = 3#8) :
    preKeyMsgAt A g a m =
      ((a + 168#64) ↦ₛ m.baseKey.bytes.toList) ∗ ((a + 240#64) ↦₈ 3#8) ∗
      signalMessageAt A g.msg a m.message ∗
      ((a + 200#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemMatchedAt A g a m := by
  rw [preKeyMsgAt_eq_base_idKey_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep, hv3]; sep_ac_rfl

private def v3P2PrePlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (opt : Option (SessionRecord (List (BitVec 8))))
    (st1 : M.σ) (s0 s1 : State) (rngPtr sp v_a8 v_b8 v_d0 : BitVec 64) : SepProp :=
  stageP2PostP1At (A.atState lim st1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
  p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗
  preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
  protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
  protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
  storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
  lsLogOff ∗ stackAt sp (dpClosSubStack B)

set_option maxHeartbeats 800000 in
private theorem v3_entry_unpack_pathA_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st1 : M.σ) (s0 s1 : State) (rngPtr sp v_a8 v_b8 v_d0 : BitVec 64)
    (hv3 : y.g.msg.messageVersion = 3#8) :
    v3P2PrePlaced y none st1 s0 s1 rngPtr sp v_a8 v_b8 v_d0 ⊢
      ∃∗ b_4f1 : BitVec 8,
        cells (y.fut + 1016#64) 6 ∗ cells (y.fut + 1128#64) 4 ∗
        ((y.fut + 1265#64) ↦₈ b_4f1) ∗ ((y.fut + 1266#64) ↦₈ 0#8) ∗
        CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 224#64) ∗
        memRegion (y.fut + 256#64) 336 ∗ cells (y.fut + 592#64) 6 ∗
        ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 912#64) ↦₈ 0#8) ∗
        ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
        ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
        ((sp + 168#64) ↦₆₄ v_a8) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
        memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
        memRegion y.out 48 ∗ lsLogOff ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
        A.pool lim st1 s1 ∗ stackAt sp (dpClosSubStack B) ∗
        v3InnerFramePlaced y rngPtr sp v_b8 := by
  dsimp only [v3P2PrePlaced, p1LoadedRecordAt, stageP2PostP1At, RustCliAllocBudget.atState_pool]
  have hdrEq : CryptoVerification.E2E.Pqxdh.ResponderClosure.sessionRecordEmptyHeaderAt (y.fut + 224#64) =
      CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 224#64) := rfl
  rw [hdrEq, coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23,
      preKeyMsgAt_v3_eq A.repAlloc y.g.msgG y.g.msgA y.g.msg hv3]
  refine Entails.trans (show _ ⊢
    (cells (y.fut + 920#64) 2 ∗ memRegion (y.fut + 592#64) 48 ∗ coroUnusedP1At y.fut) ∗
    (closStackUnusedP1OkAt sp ∗ memRegion (sp + 992#64) 368) ∗
    (CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 224#64) ∗
      memRegion (y.fut + 256#64) 336 ∗
      ((y.fut + 1266#64) ↦₈ 0#8) ∗ ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 912#64) ↦₈ 0#8) ∗
      ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
      ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
      ((sp + 168#64) ↦₆₄ v_a8) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
      memRegion y.out 48 ∗ lsLogOff ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      A.pool lim st1 s1 ∗ stackAt sp (dpClosSubStack B) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      (sp ↦₆₄ 0#64) ∗ ((sp + 176#64) ↦₆₄ (y.fut + 912#64)) ∗
      ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ y.cx) ∗
      memRegion (sp + 216#64) 348 ∗
      signalMessageAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      ((y.g.msgA + 200#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemMatchedAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened)
    by sep_frame) ?_
  rw [closStack_v3_split sp]
  refine Entails.trans (sepConj_mono_left (coro_unused_split_v3 y.fut)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun b_4f1 => Entails.sepExists_right b_4f1 ?_
  dsimp only [v3InnerFramePlaced]; exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem v3_entry_unpack_over_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (st1 : M.σ) (s0 s1 : State) (rngPtr sp v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess)
    (hv3 : y.g.msg.messageVersion = 3#8) :
    v3P2PrePlaced y (some r) st1 s0 s1 rngPtr sp v_a8 v_b8 v_d0 ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ b_4f1 : BitVec 8,
        cells (y.fut + 1016#64) 6 ∗ cells (y.fut + 1128#64) 4 ∗
        ((y.fut + 1265#64) ↦₈ b_4f1) ∗ ((y.fut + 1266#64) ↦₈ 0#8) ∗
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A.repAlloc y.fut g ∗
        sessionStateReprAt A.repAlloc (y.fut + 248#64) recG sess ∗
        cells (y.fut + 592#64) 6 ∗ ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 912#64) ↦₈ 0#8) ∗
        ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
        ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
        ((sp + 168#64) ↦₆₄ v_a8) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
        memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
        memRegion y.out 48 ∗ lsLogOff ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
        A.pool lim st1 s1 ∗ stackAt sp (dpClosSubStack B) ∗
        v3InnerFramePlaced y rngPtr sp v_b8 := by
  dsimp only [v3P2PrePlaced]
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]; simp only [sepConj_assoc]
  refine Entails.pure_left fun _hkit => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun g => ?_
  refine Entails.trans
    (sepConj_mono_left (sessionRecordAt_some_eq_prev_sess A.repAlloc y.fut g r sess hcur)) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun recG => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun _hgcur => ?_
  have hprevEq : CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A.repAlloc y.fut g =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A.repAlloc y.fut g := rfl
  dsimp only [stageP2PostP1At, RustCliAllocBudget.atState_pool]
  rw [hprevEq, coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23,
      preKeyMsgAt_v3_eq A.repAlloc y.g.msgG y.g.msgA y.g.msg hv3]
  refine Entails.trans (show _ ⊢
    (cells (y.fut + 920#64) 2 ∗ memRegion (y.fut + 592#64) 48 ∗ coroUnusedP1At y.fut) ∗
    (closStackUnusedP1OkAt sp ∗ memRegion (sp + 992#64) 368) ∗
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A.repAlloc y.fut g ∗
      sessionStateReprAt A.repAlloc (y.fut + 248#64) recG sess ∗
      ((y.fut + 1266#64) ↦₈ 0#8) ∗ ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 912#64) ↦₈ 0#8) ∗
      ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
      ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
      ((sp + 168#64) ↦₆₄ v_a8) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
      memRegion y.out 48 ∗ lsLogOff ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
      A.pool lim st1 s1 ∗ stackAt sp (dpClosSubStack B) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      (sp ↦₆₄ 0#64) ∗ ((sp + 176#64) ↦₆₄ (y.fut + 912#64)) ∗
      ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ y.cx) ∗
      memRegion (sp + 216#64) 348 ∗
      signalMessageAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      ((y.g.msgA + 200#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemMatchedAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened)
    by sep_frame) ?_
  rw [closStack_v3_split sp]
  refine Entails.trans (sepConj_mono_left (coro_unused_split_v3 y.fut)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun b_4f1 =>
    Entails.sepExists_right g (Entails.sepExists_right recG (Entails.sepExists_right b_4f1 ?_))
  dsimp only [v3InnerFramePlaced]; exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem v3_exit_fold_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (stf : M.σ) (s0 sf : State) (rngPtr v_b8 : BitVec 64)
    (hv3 : y.g.msg.messageVersion = 3#8) :
    let sp := s0.sp - 3280#64
    let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
    processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
    ((y.fut + 1265#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 1#8) ∗
    memRegion (y.fut + 224#64) 368 ∗ cells (y.fut + 592#64) 6 ∗
    ((y.fut + 704#64) ↦₈ 1#8) ∗ ((y.fut + 912#64) ↦₈ 1#8) ∗
    ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
    ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
    ((sp + 168#64) ↦₆₄ 3#64) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ 24#64) ∗
    memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
    apiDecResultAt A.repAlloc y.out (.error err) ∗ lsLogOff ∗
    decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
    A.pool lim stf sf ∗ stackAt sp (dpClosSubStack B) ∗
    v3InnerFramePlaced y rngPtr sp v_b8 ⊢
      dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗
      decResAt A.repAlloc y.out (.error err) ∗
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      lsLogOff ∗ A.pool lim stf sf ∗ stackAt sp (dpClosSubStack B) := by
  dsimp only [v3InnerFramePlaced]
  let sp := s0.sp - 3280#64
  let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
  have hcoro := p2_coro_err_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstk := closStack_v3_fold s0.sp s0
    (y.fut + 920#64) (y.fut + 1266#64) 3#64 (y.fut + 912#64) v_b8 y.cx y.out 24#64
  dsimp only at hstk
  have hres := apiDecResultAt_proto_entails_decResAt A.repAlloc y.out
    (.invalidMessage .preKey .badCiphertext) err
  refine Entails.trans (show _ ⊢
    (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 112#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 120#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 128#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 240#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 200#64) (lsρ cliPreKeyVtSym) (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 224#64) 368 ∗
      cells (y.fut + 592#64) 6 ∗ memRegion (y.fut + 640#64) 24 ∗ memRegion (y.fut + 664#64) 20 ∗
      memRegion (y.fut + 684#64) 8 ∗ memRegion (y.fut + 692#64) 12 ∗
      ((y.fut + 704#64) ↦₈ 1#8) ∗ ((y.fut + 816#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 904#64) ↦₆₄ (y.g.msgA + 200#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 912#64) ↦₈ 1#8) ∗ memRegion (y.fut + 920#64) 96 ∗
      ((y.fut + 1265#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 705#64) 7 ∗ memRegion (y.fut + 913#64) 7 ∗
      memRegion (y.fut + 1160#64) 8 ∗ memRegion (y.fut + 1200#64) 65 ∗ memRegion (y.fut + 1267#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 1922#64) 6) ∗
    ((sp ↦₆₄ 0#64) ∗
      ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
      ((sp + 168#64) ↦₆₄ 3#64) ∗ ((sp + 176#64) ↦₆₄ (y.fut + 912#64)) ∗
      ((sp + 184#64) ↦₆₄ v_b8) ∗ ((sp + 192#64) ↦₆₄ y.cx) ∗
      ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ 24#64) ∗
      memRegion (sp + 216#64) 348 ∗ memRegion (sp + 880#64) 36 ∗
      memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
      v3StackRemAt sp ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0) ∗
    apiDecResultAt A.repAlloc y.out (.error err) ∗
    storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
    (((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
      signalMessageAt A.repAlloc y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      ((y.g.msgA + 200#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemMatchedAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
    protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    lsLogOff ∗ A.pool lim stf sf ∗ stackAt sp (dpClosSubStack B)
    by exact Entails.of_eq (by dsimp only [sp]; sep_ac_rfl)) ?_
  rw [← preKeyMsgAt_v3_eq A.repAlloc y.g.msgG y.g.msgA y.g.msg hv3]
  exact sepConj_mono hcoro (sepConj_mono hstk (sepConj_mono_left hres))

/-! ## 3. Stage P2 & Poll-Closure Budget Theorems (`stageP2_v3_reject_placedBudget`, `decPk_v3_reject_poll_placedBudget`) -/

private theorem hoverPure_le_subStack (B : RunBudgets) :
    stageP2OverPureAndErrStack ≤ dpClosSubStack B :=
  Nat.le_trans (by decide : stageP2OverPureAndErrStack ≤ 1048576 - 3280) (Nat.le_add_right _ _)

set_option maxHeartbeats 800000 in
theorem stageP2_v3_reject_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostStateBudget (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (R : SepProp) (s0 : State) (opt : Option (SessionRecord (List (BitVec 8))))
    (evs_p1 : List AllocEvent) (s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hfPeer : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hv3Cond : MsgCondV3 Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hans : S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = some none)
    (hfits_p2 : FitsEnv M lim (M.stepEvents evs_p1 y.st) StageP2V3RejectEnv)
    (hevs_sub : ∀ evs_p2, StageP2V3RejectEnv evs_p2 → DecPkEnv y.g (evs_p1 ++ evs_p2))
    (hload_rel : (cliPollSessKitPlaced A.repAlloc y.g.F scopeKit y.g.peer
      (cliKitStk B)).loadRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions y.g.peer.val (.ok opt))
    (htr1 : s1.trace = s0.trace) (hro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = dpPollEntryPlaced + 0x868#64) (hrun1 : s1.status = .Running)
    (halign1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s1
      (stageP2PostP1At (A.atState lim (M.stepEvents evs_p1 y.st) s1)
         y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32)
      (fun sf P_f => (Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (dpPollSpecStateBudget (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
          (dpPollSpecStateBudget (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim DecPkEnv B S) stk')).onPanic y s0 sf ∗ R)) := by
  obtain ⟨hv3, hnoMatch⟩ := hv3Cond
  let sp := s0.sp - 3280#64
  let st1 := M.stepEvents evs_p1 y.st
  let Leftover : SepProp := coinsInstalledPlaced y.g.coinsP y.g.coins ∗ LsTokenInit
  let Fr_p2 : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32 ∗ Leftover
  have hpre_split :
      (stageP2PostP1At (A.atState lim st1 s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (s0.sp - 0xcd0#64) v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt scopeKit A.repAlloc y.fut opt ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
       LsTokenInit ∗ lsLogOff ∗ stackAt (s0.sp - 0xcd0#64) (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗ memRegion y.cx 32) =
      v3P2PrePlaced y opt st1 s0 s1 rngPtr sp v_a8 v_b8 v_d0 ∗ Fr_p2 := by
    dsimp only [v3P2PrePlaced, Fr_p2, Leftover, sp]; sep_ac_rfl
  rw [hpre_split, ← stageP1ProgPlaced_eq_dpPollProgPlaced mmpl gh W]
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, hx28, _, hvregs1⟩
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by
    change ((s0.sp - 0xcd0#64) &&& 15#64 == 0#64) = true; rw [← hs1_sp]; exact halign1
  let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
  cases opt with
  | none =>
    have hunpack :
        v3P2PrePlaced y none st1 s0 s1 rngPtr sp v_a8 v_b8 v_d0 ∗ Fr_p2 ⊢
          ∃∗ b_4f1 : BitVec 8,
            cells (y.fut + 1016#64) 6 ∗ cells (y.fut + 1128#64) 4 ∗
            ((y.fut + 1265#64) ↦₈ b_4f1) ∗ ((y.fut + 1266#64) ↦₈ 0#8) ∗
            CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 224#64) ∗
            memRegion (y.fut + 256#64) 336 ∗ cells (y.fut + 592#64) 6 ∗
            ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 912#64) ↦₈ 0#8) ∗
            ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
            ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
            ((sp + 168#64) ↦₆₄ v_a8) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
            memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
            memRegion y.out 48 ∗ lsLogOff ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
            A.pool lim st1 s1 ∗ stackAt sp (dpClosSubStack B) ∗
            (v3InnerFramePlaced y rngPtr sp v_b8 ∗ Fr_p2) := by
      refine Entails.trans (sepConj_mono_left
        (v3_entry_unpack_pathA_placed y st1 s0 s1 rngPtr sp v_a8 v_b8 v_d0 hv3)) ?_
      simp only [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun b_4f1 => Entails.sepExists_right b_4f1 ?_
      exact Entails.of_eq (by sep_ac_rfl)
    refine sepWPp_conseq_pre hunpack ?_
    refine SepWPp.exists_elim fun b_4f1 => ?_
    exact stageP2_pathA_v3_kits_placed
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      (cliStageP2ClosureHooksPlaced_d3 A lim mmpl gh W hh)
      (v3PubKeySerialize_placedBudget A lim mmpl gh W hh)
      (cliStrToOwnedLocal2_placedBudget_ok A lim mmpl gh W hh)
      (dpClosSubStack B) (hoverPure_le_subStack B)
      st1 hfits_p2 s0 s1 (v3InnerFramePlaced y rngPtr sp v_b8 ∗ Fr_p2) _ _
      sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym)
      v_a8 v_d0 y.g.msg.baseKey 0#8 0#8 b_4f1 0#8
      hsp_sub hro1 hpc1 hrun1 hs1_sp hsp_align hvregs1
      hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
      (fun evs_p2 sf P_f hevs2 _hsteps1f _hpcf _hrunf hspf htrf hcsf hvregsf _hCodef hPf => by
        refine ⟨?_, hspf.trans (sp_frame_sub_add s0.sp), calleeSavedPreserved_of_closure hcsf hvregsf⟩
        intro hsteps0f hmf
        have hevs_eq : M.stepEvents (evs_p1 ++ evs_p2) y.st = M.stepEvents evs_p2 st1 :=
          AllocCostModel.stepEvents_append M evs_p1 evs_p2 y.st
        have hent : P_f ⊢
            dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt A.repAlloc y.out (.error err) ∗
            storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            lsLogOff ∗ A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            memRegion y.cx 32 ∗ Leftover := by
          rw [hevs_eq]
          refine Entails.trans hPf ?_
          refine Entails.trans (Entails.of_eq (by sep_ac_rfl : _ =
            (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
              (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
            ((y.fut + 1265#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 1#8) ∗
            memRegion (y.fut + 224#64) 368 ∗ cells (y.fut + 592#64) 6 ∗
            ((y.fut + 704#64) ↦₈ 1#8) ∗ ((y.fut + 912#64) ↦₈ 1#8) ∗
            ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
            ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
            ((sp + 168#64) ↦₆₄ 3#64) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ 24#64) ∗
            memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
            apiDecResultAt A.repAlloc y.out (.error err) ∗ lsLogOff ∗
            decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
            A.pool lim (M.stepEvents evs_p2 st1) sf ∗ stackAt sp (dpClosSubStack B) ∗
            v3InnerFramePlaced y rngPtr sp v_b8) ∗ Fr_p2)) ?_
          refine Entails.trans (sepConj_mono_left
            (v3_exit_fold_placed y (M.stepEvents evs_p2 st1) s0 sf rngPtr v_b8 hv3)) ?_
          dsimp only [Fr_p2, sp]; exact Entails.of_eq (by sep_ac_rfl)
        exact d3_pollPost_of_stageP2_err_placedBudget A lim B S hh stk' hneed hstk63 y s0 sf
          (evs_p1 ++ evs_p2) err P_f Leftover R nofun nofun hans (hevs_sub evs_p2 hevs2)
          hsteps0f (htrf.trans htr1) hent hmf)
  | some r =>
    obtain ⟨sess, hcur⟩ := D3PollRejectAuxPlacedBudget.currentSession_some_of_cliPollSessPlaced_loadRel hload_rel
    have hloadS : loadRec Scope y.g.F y.g.peer.val = .ok (some r) :=
      D3PollRejectAuxPlacedBudget.loadRec_of_cliPollSessPlaced_loadRel hinjK hsub hfPeer hload_rel
    have hnm : ¬ SessMatchesPm sess y.g.msg := hnoMatch r sess hloadS hcur
    have hunpack :
        v3P2PrePlaced y (some r) st1 s0 s1 rngPtr sp v_a8 v_b8 v_d0 ∗ Fr_p2 ⊢
          ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ b_4f1 : BitVec 8,
            cells (y.fut + 1016#64) 6 ∗ cells (y.fut + 1128#64) 4 ∗
            ((y.fut + 1265#64) ↦₈ b_4f1) ∗ ((y.fut + 1266#64) ↦₈ 0#8) ∗
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A.repAlloc y.fut g ∗
            sessionStateReprAt A.repAlloc (y.fut + 248#64) recG sess ∗
            cells (y.fut + 592#64) 6 ∗ ((y.fut + 704#64) ↦₈ 0#8) ∗ ((y.fut + 912#64) ↦₈ 0#8) ∗
            ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
            ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
            ((sp + 168#64) ↦₆₄ v_a8) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ v_d0) ∗
            memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
            memRegion y.out 48 ∗ lsLogOff ∗ decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
            A.pool lim st1 s1 ∗ stackAt sp (dpClosSubStack B) ∗
            (v3InnerFramePlaced y rngPtr sp v_b8 ∗ Fr_p2) := by
      refine Entails.trans (sepConj_mono_left
        (v3_entry_unpack_over_placed y r sess st1 s0 s1 rngPtr sp v_a8 v_b8 v_d0 hcur hv3)) ?_
      simp only [sepExists_sepConj_left]
      refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
      refine Entails.sepExists_elim fun recG => Entails.sepExists_right recG ?_
      refine Entails.sepExists_elim fun b_4f1 => Entails.sepExists_right b_4f1 ?_
      exact Entails.of_eq (by sep_ac_rfl)
    refine sepWPp_conseq_pre hunpack ?_
    refine SepWPp.exists_elim fun g => SepWPp.exists_elim fun recG => SepWPp.exists_elim fun b_4f1 => ?_
    have hPromMissAt : LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget.PromoteMatchingMissAtPlacedProp A.repAlloc
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) y.fut g recG sess 3#8 y.g.msg.baseKey.serialize :=
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget.promoteMatchingMissAt_placed_of_gen
        (cliPromoteMatchingMissGen_placed_d3 A.repAlloc mmpl gh W)
        y.fut g recG sess 3#8 y.g.msg.baseKey.serialize
        (not_p2SessMatchesMsg_of_v3' hv3 hnm) (baseKey_serialize_length y.g.msg.baseKey)
    exact stageP2_over_v3_kits_placed
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      (withPanics_cliGhostExterns mmpl gh W)
      (cliStageP2ClosureHooksPlaced_d3 A lim mmpl gh W hh)
      (v3PubKeySerialize_placedBudget A lim mmpl gh W hh)
      (cliStrToOwnedLocal2_placedBudget_ok A lim mmpl gh W hh)
      (drop_session_structure3_placed_ok_on_stageP1 hh.codecHooks.dealloc)
      (dpClosSubStack B) (hoverPure_le_subStack B)
      st1 hfits_p2 s0 s1 (v3InnerFramePlaced y rngPtr sp v_b8 ∗ Fr_p2) _ _
      sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 80#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym)
      v_a8 v_d0 g recG sess y.g.msg.baseKey 0#8 0#8 b_4f1 0#8
      hPromMissAt hsp_sub hro1 hpc1 hrun1 hs1_sp hsp_align hvregs1
      hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
      (fun evs_p2 sf P_f hevs2 _hsteps1f _hpcf _hrunf hspf htrf hcsf hvregsf _hCodef hPf => by
        refine ⟨?_, hspf.trans (sp_frame_sub_add s0.sp), calleeSavedPreserved_of_closure hcsf hvregsf⟩
        intro hsteps0f hmf
        have hevs_eq : M.stepEvents (evs_p1 ++ evs_p2) y.st = M.stepEvents evs_p2 st1 :=
          AllocCostModel.stepEvents_append M evs_p1 evs_p2 y.st
        have hent : P_f ⊢
            dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt A.repAlloc y.out (.error err) ∗
            storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
            preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
            protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
            protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
            lsLogOff ∗ A.pool lim (M.stepEvents (evs_p1 ++ evs_p2) y.st) sf ∗
            stackAt sp (dpClosSubStack B) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
            memRegion y.cx 32 ∗ Leftover := by
          rw [hevs_eq]
          refine Entails.trans hPf ?_
          refine Entails.trans (Entails.of_eq (by sep_ac_rfl : _ =
            (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
              y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 200#64) (lsρ cliPreKeyVtSym)
              (y.g.stores + 120#64) (lsρ cliKyberPreKeyVtSym) ∗
            ((y.fut + 1265#64) ↦₈ 0#8) ∗ ((y.fut + 1266#64) ↦₈ 1#8) ∗
            memRegion (y.fut + 224#64) 368 ∗ cells (y.fut + 592#64) 6 ∗
            ((y.fut + 704#64) ↦₈ 1#8) ∗ ((y.fut + 912#64) ↦₈ 1#8) ∗
            ((y.g.msgA + 168#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗ ((y.g.msgA + 240#64) ↦₈ 3#8) ∗
            ((sp + 152#64) ↦₆₄ (y.fut + 920#64)) ∗ ((sp + 160#64) ↦₆₄ (y.fut + 1266#64)) ∗
            ((sp + 168#64) ↦₆₄ 3#64) ∗ ((sp + 200#64) ↦₆₄ y.out) ∗ ((sp + 208#64) ↦₆₄ 24#64) ∗
            memRegion (sp + 880#64) 36 ∗ memRegion (sp + 992#64) 24 ∗ memRegion (sp + 2704#64) 48 ∗
            apiDecResultAt A.repAlloc y.out (.error err) ∗ lsLogOff ∗
            decryptPrekeySavedRegsAt (sp + 3280#64) s0 ∗
            A.pool lim (M.stepEvents evs_p2 st1) sf ∗ stackAt sp (dpClosSubStack B) ∗
            v3InnerFramePlaced y rngPtr sp v_b8) ∗ Fr_p2)) ?_
          refine Entails.trans (sepConj_mono_left
            (v3_exit_fold_placed y (M.stepEvents evs_p2 st1) s0 sf rngPtr v_b8 hv3)) ?_
          dsimp only [Fr_p2, sp]; exact Entails.of_eq (by sep_ac_rfl)
        exact d3_pollPost_of_stageP2_err_placedBudget A lim B S hh stk' hneed hstk63 y s0 sf
          (evs_p1 ++ evs_p2) err P_f Leftover R nofun nofun hans (hevs_sub evs_p2 hevs2)
          hsteps0f (htrf.trans htr1) hent hmf)

theorem decPk_v3_reject_poll_placedBudget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    (hDeser : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hinjK : EncodeInjOn scopeKit) (hsub : ∀ r, Scope r → scopeIn r)
    (hok : ∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      FilesOkPeer Scope F peer ∧ DecPkStoreOk ⟨W.C, W.Q⟩ F ∧
      MsgCondV3 Scope F peer me pm ∧
      (∀ coins, S.decryptPrekey F peer me pm coins = some none))
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (dpPollSpecStateBudget
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.dpSlotPollKStatePlaced A lim
          (DecPkD3UntypedPollEnv (A := A.repAlloc) B ReadEnv DeserEnv (fun _ _ => StageP2V3RejectEnv)) B S)
        stk')) :=
  decPk_d3_untyped_poll_reject_placedBudget A lim
    (P2Env := fun _ _ => StageP2V3RejectEnv) (MsgCondV3 Scope)
    hDropNz mmpl gh W B S Scope hh hRead hDeser hsub hok
    (fun _ _ => ⟨none, stageP2V3RejectEnv_nonempty⟩)
    stk' hneed hstk63
    (fun y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hfPeer _hstoreOk hv3Cond hans _hcoins
         hevs_p1 hfits_p2 hload_rel _hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1 =>
      stageP2_v3_reject_placedBudget A lim mmpl gh W B S Scope hh hinjK hsub stk' hneed hstk63
        y R s0 opt evs_p1 s1 rngPtr v_a8 v_b8 v_d0 hfPeer hv3Cond hans hfits_p2
        (fun evs2 hevs2 => Or.inr ⟨opt, Or.inr ⟨evs_p1, evs2, rfl, hevs_p1, hevs2⟩⟩)
        hload_rel htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 halign1 hregs1)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3V3RejectPlacedBudget
