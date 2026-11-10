/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonStage2AuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFolds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFold

/-!
# Budget-Threaded Stage P2 Spatial Folds for Non-Canonical Wire Encodings

Spatial entry/exit folds and frame-preservation lemmas for Stage P2 of `decrypt_prekey` poll on
non-canonical `PreKeySignalMessage` wire encodings under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (SignalMessage SessionState)
open CryptoGames.LibsignalSessionApi (ApiError PreKeySignalMessage Session SessionRecord)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3SpillAll)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (coroOpkIdAtP4 hdrOpkIdBv? opkOptTag32 p1LoadedRecordAt p2CoroScratchTailAt p2MsgFieldsAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (prevArchived1At)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (clearPending prevVecAt)
open CryptoVerification.E2E (PEParams PreKeyMessageFields)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyActive10At processPrekeyPostTrustAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stackAt_sub_eq stageP3Sub5ExtraPre)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal PreKeyMsgGhost RecordGhost optKyberAt optU32At preKeyMsgAt sessionRecordAt sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost SignalMessageGhost boxU8At protocolAddressAt sessionStateAt signalMessageAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.MainHops (coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem decResAt)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOk₀ dpFutDoneAt pkToE? pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (LsTokenInit PathAEntryWords bytesToBv8_vecU8 cliIdInv_opened_peer cliIdOwnInv_opened cliKitStk cliKpkInvFull_opened cliPkInv_opened cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced cliPollSpkKitPlaced cliPollStoresKitsAt cliPollStoresKitsAt_entails_storesAt cliSessInv_opened_scopeKit cliSpkInv_opened closStackUnusedP1OkAt coroCopyAt_eq_head3_tail11 coroCopyTail11At coroUnusedP1At coro_unused_split_p2v1 dpClosSubStack genP3CallFramePlaced genP3PrePlaced hdrOpkIdBv?_mkPathAHdr memRegion_4_eq_exists_pointsTo32 mkPathAHdr p2StageP3Sub5ExtraPrePrev1 p2_coro_err_fold p2_coro_ok_fold p2_coro_opk_slot_fold p2_stack_err_fold pmOfE_fields preKeyMsgAt_eq_base_idKey_sep preKeyMsgRemBaseIdKeyAt processPrekeyInnerInitAt_eq_330_388_rem23 processPrekeyInnerRem23At sessionRecordAt_some_eq_prev_sess signalMessageAt_eq_ver_sep signalMessageRestVerAt sp550P2V1RemAt spMidGapsAt sp_3e0_344_eq_104_240 sp_3e0_368_eq_344_24 stackAt_root_eq_chainClone stack_unused_split_p2v1 stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt storesAt_entails_cliPollStoresKitsAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll.OverP2Inst (encSessionMem_clearPending_eq sessionAt_dup_canonSession)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer coinsInstalledPlaced_entails_coinsAtPlaced scopeIn scopeKit)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget (p2OverOkPostAtPlaced)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5PlacedBudget (stageP2OverPreAtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (kpkId_shift_or_one_eq_append_d3 p2Over_not_sessMatchesMsg_d3 p2_stk_ok_fold_d3_placed pm_fields_of_pkToE)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget (p1LoadedRecordAt_atState_eq_repAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (genP3Pre_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget (decResAt_err_atState_eq_repAlloc p2ErrFrameAtPlaced preKeyMsgAt_atState_eq_repAlloc preKeyMsgRemBaseIdKeyAt_atState_eq_repAlloc signalMessageRestVerAt_atState_eq_repAlloc stageP2PreAtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlacedBudget (p2OkPostAtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (DpPollGhostStateBudget dpSlotPollKStatePlaced)

export LibsignalBinary.Proofs.SignalSession.Cli.D3 (p2Over_not_sessMatchesMsg_d3)

def pathAMsgRemInnerAtD3 (A_r : RustAlloc) (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (pm : PreKeySignalMessage) : SepProp :=
  ⌜g.kyberPtr ≠ 0 ∧ 1569 < 2 ^ 63⌝ ∗ A_r.live g.kyberPtr 1569 1 ∗ memRegion (msgA + 0xa4#64) 4 ∗
  boxU8At A_r (msgA + 0x80#64) g.serPtr pm.serialized ∗ memRegion (msgA + 0xf1#64) 7

theorem pathAMsgRemInnerAtD3_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : PreKeyMsgGhost) (msgA : BitVec 64) (pm : PreKeySignalMessage) :
    pathAMsgRemInnerAtD3 (A.atState lim st s) g msgA pm = pathAMsgRemInnerAtD3 A.repAlloc g msgA pm := rfl

theorem pathAMsgRemInnerAtD3_dup_kyberPtr (A_r : RustAlloc) (g : PreKeyMsgGhost)
    (msgA : BitVec 64) (pm : PreKeySignalMessage) :
    pathAMsgRemInnerAtD3 A_r g msgA pm ⊢ ⌜g.kyberPtr ≠ 0#64⌝ ∗ pathAMsgRemInnerAtD3 A_r g msgA pm := by
  unfold pathAMsgRemInnerAtD3; refine Entails.pure_left fun hp => ?_
  have hne : g.kyberPtr ≠ 0#64 := hp.1
  rw [pure_sepConj_of_true hne, pure_sepConj_of_true hp]; exact Entails.refl _

theorem preKeyMsgAt_unpack_pathA_d3 (A_r : RustAlloc) (g : PreKeyMsgGhost) (msgA : BitVec 64)
    {pm : PreKeySignalMessage} (m : PreKeyMessageFields) (i : SignalMessage)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i) :
    preKeyMsgAt A_r g msgA pm ⊢
      ∃∗ opkWord : BitVec 32, ⌜∀ id : BitVec 32, m.opkId = some id → opkWord = id⌝ ∗
        p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion opkWord m.kpkId m.regId m.spkId ∗
        signalMessageRestVerAt A_r g.msg msgA i ∗ pathAMsgRemInnerAtD3 A_r g msgA pm := by
  obtain ⟨hver, hreg, hopk, hspk, hbase, hidk, hmsg, hkyb⟩ := pm_fields_of_pkToE hpk hmsg_i
  unfold preKeyMsgAt p2MsgFieldsAt pathAMsgRemInnerAtD3
  rw [hmsg, hopk, hkyb, hbase, hidk, hreg, hspk, hver, signalMessageAt_eq_ver_sep, hdrOpkIdBv?_mkPathAHdr]
  dsimp only [mkPathAHdr]
  rw [bytesToBv8_vecU8 m.baseKey, bytesToBv8_vecU8 m.idPub, bytesToBv8_vecU8 m.kyberCt]
  dsimp only [optKyberAt, boxU8At]
  have hne : (8#8 :: m.kyberCt.toList) ≠ [] := List.cons_ne_nil _ _
  have hlen1569 : BitVec.ofNat 64 (8#8 :: m.kyberCt.toList).length = 1569#64 := by simp [m.kyberCt.toList_length]
  have hlenNat : (8#8 :: m.kyberCt.toList).length = 1569 := by simp [m.kyberCt.toList_length]
  simp only [hne, ↓reduceIte, hlen1569, hlenNat, BitVec.add_assoc, BitVec.reduceAdd]
  cases hopk_eq : m.opkId with
  | none =>
    dsimp only [optU32At, opkOptTag32]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [memRegion_4_eq_exists_pointsTo32 (msgA + 0x7c#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    exact Entails.sepExists_elim fun opkWord =>
      Entails.sepExists_right opkWord (Entails.pure_right (by nofun) (Entails.of_eq (by sep_ac_rfl)))
  | some id =>
    dsimp only [optU32At, opkOptTag32]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right id
      (Entails.pure_right (fun _ h => Option.some.inj h) (Entails.of_eq (by sep_ac_rfl)))

theorem p2MsgFields_reassemble_slices_d3 (A_r : RustAlloc) (g : PreKeyMsgGhost) (msgA : BitVec 64)
    {pm : PreKeySignalMessage} (m : PreKeyMessageFields) (i : SignalMessage)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i) (opkWord : BitVec 32)
    (hopkWord : ∀ id : BitVec 32, m.opkId = some id → opkWord = id) :
    p2MsgFieldsAt msgA g.kyberPtr (mkPathAHdr m) i.messageVersion opkWord m.kpkId m.regId m.spkId ∗
    signalMessageRestVerAt A_r g.msg msgA i ∗ pathAMsgRemInnerAtD3 A_r g msgA pm ⊢
      signalMessageAt A_r g.msg msgA pm.message ∗ ((msgA + 0xa8#64) ↦ₛ pm.baseKey.bytes.toList) ∗
      ((msgA + 0xc8#64) ↦ₛ pm.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt A_r g msgA pm := by
  obtain ⟨hver, hreg, hopk, hspk, hbase, hidk, hmsg, hkyb⟩ := pm_fields_of_pkToE hpk hmsg_i
  unfold p2MsgFieldsAt pathAMsgRemInnerAtD3 preKeyMsgRemBaseIdKeyAt
  rw [hmsg, hopk, hkyb, hbase, hidk, hreg, hspk, hver, signalMessageAt_eq_ver_sep, hdrOpkIdBv?_mkPathAHdr]
  dsimp only [mkPathAHdr]
  rw [bytesToBv8_vecU8 m.baseKey, bytesToBv8_vecU8 m.idPub, bytesToBv8_vecU8 m.kyberCt]
  dsimp only [optKyberAt, boxU8At]
  have hne : (8#8 :: m.kyberCt.toList) ≠ [] := List.cons_ne_nil _ _
  have hlen1569 : BitVec.ofNat 64 (8#8 :: m.kyberCt.toList).length = 1569#64 := by simp [m.kyberCt.toList_length]
  have hlenNat : (8#8 :: m.kyberCt.toList).length = 1569 := by simp [m.kyberCt.toList_length]
  simp only [hne, ↓reduceIte, hlen1569, hlenNat, BitVec.add_assoc, BitVec.reduceAdd]
  have hoptU32 : ((msgA + 0x78#64) ↦₃₂ opkOptTag32 m.opkId) ∗ ((msgA + 0x7c#64) ↦₃₂ opkWord) ⊢
      optU32At (msgA + 0x78#64) m.opkId := by
    cases hopk_eq : m.opkId with
    | none =>
      dsimp only [optU32At, opkOptTag32]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_right (pointsTo32_entails_memRegion _ _)
    | some id =>
      rw [hopkWord id hopk_eq]; dsimp only [optU32At, opkOptTag32]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (((msgA + 0x78#64) ↦₃₂ opkOptTag32 m.opkId) ∗ ((msgA + 0x7c#64) ↦₃₂ opkWord)) ∗
    (((msgA + 0x70#64) ↦₈ i.messageVersion) ∗ signalMessageRestVerAt A_r g.msg msgA i ∗
      ((msgA + 0xa8#64) ↦ₛ m.baseKey.toList) ∗ ((msgA + 0xc8#64) ↦ₛ m.idPub.toList) ∗
      boxU8At A_r (msgA + 0x80#64) g.serPtr pm.serialized ∗
      (((msgA + 0x90#64) ↦₆₄ g.kyberPtr) ∗ ((msgA + 0x98#64) ↦₆₄ 1569#64) ∗ ⌜g.kyberPtr ≠ 0 ∧ 1569 < 2 ^ 63⌝ ∗
        (A_r.live g.kyberPtr 1569 1 ∗ (g.kyberPtr ↦ₛ (8#8 :: m.kyberCt.toList))) ∗
        ((msgA + 0xa0#64) ↦₃₂ m.kpkId) ∗ memRegion (msgA + 0xa4#64) 4) ∗
      ((msgA + 0xe8#64) ↦₃₂ m.regId) ∗ ((msgA + 0xec#64) ↦₃₂ m.spkId) ∗
      ((msgA + 0xf0#64) ↦₈ 4#8) ∗ memRegion (msgA + 0xf1#64) 7) by
    simp only [boxU8At, BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hoptU32)
    (Entails.of_eq (by simp only [boxU8At, BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl))

def pathAInnerFrameD3Placed {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement] (A_r : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (i : SignalMessage) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKitPlaced A_r y.g.F scopeKit y.g.peer (cliKitStk B)).storeAt
    (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
  dirAt A_r (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  memRegion (y.fut + 0x280#64) 24 ∗ memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
  memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
  memRegion (y.fut + 0x782#64) 6 ∗ (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x279#64) 39 ∗ memRegion (sp + 0x2b0#64) 36 ∗
  memRegion (sp + 0x2e0#64) 36 ∗ memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
  spMidGapsAt sp ∗ sp550P2V1RemAt sp ∗ signalMessageRestVerAt A_r y.g.msgG.msg y.g.msgA i ∗
  pathAMsgRemInnerAtD3 A_r y.g.msgG y.g.msgA y.g.msg ∗
  coinsInstalledPlaced y.g.coinsP y.g.coins ∗ tokenInitPlacedAt

theorem pathAInnerFrameD3Placed_atState_eq_repAlloc {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement] (st : M.σ) (s : State)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFrameD3Placed (A.atState lim st s) y i rngPtr sp =
      pathAInnerFrameD3Placed A.repAlloc y i rngPtr sp := by
  unfold pathAInnerFrameD3Placed
  rw [signalMessageRestVerAt_atState_eq_repAlloc A lim st s y.g.msgG.msg y.g.msgA i,
      pathAMsgRemInnerAtD3_atState_eq_repAlloc A lim st s y.g.msgG y.g.msgA y.g.msg]
  rfl

private theorem dup_pure_sepConj_right {φ : Prop} {P Q : SepProp} (h : Q ⊢ ⌜φ⌝ ∗ Q) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem dup_pure_sepConj_left {φ : Prop} {P Q : SepProp} (h : P ⊢ ⌜φ⌝ ∗ P) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_left h) (by rw [sepConj_assoc]; exact Entails.refl _)

private theorem pull_pure_after1 {A1 Rest : SepProp} {φ : Prop} : A1 ∗ (⌜φ⌝ ∗ Rest) = ⌜φ⌝ ∗ (A1 ∗ Rest) := by
  sep_ac_rfl

private theorem pull_pure_msg_group {M1 M2 M3 Tail : SepProp} {φ : Prop} :
    (M1 ∗ M2 ∗ (⌜φ⌝ ∗ M3)) ∗ Tail = ⌜φ⌝ ∗ ((M1 ∗ M2 ∗ M3) ∗ Tail) := by sep_ac_rfl

private theorem pull_pure_after7 {A1 A2 A3 A4 A5 A6 A7 Rest : SepProp} {φ : Prop} :
    A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ (⌜φ⌝ ∗ Rest))))))) =
      ⌜φ⌝ ∗ (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ Rest))))))) := by sep_ac_rfl

theorem pathAInnerFrameD3_dup_kyberPtr_placed {M : AllocCostModel} {A_b : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement] (A_r : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFrameD3Placed A_r y i rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗ pathAInnerFrameD3Placed A_r y i rngPtr sp := by
  unfold pathAInnerFrameD3Placed
  repeat (first
    | exact dup_pure_sepConj_left (pathAMsgRemInnerAtD3_dup_kyberPtr A_r y.g.msgG y.g.msgA y.g.msg)
    | refine dup_pure_sepConj_right ?_)

private abbrev p2EntryTail {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement] (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (s0 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64) : SepProp :=
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
  coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  ((y.fut + 0x390#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗ (sp ↦₆₄ 0#64) ∗
  ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
  ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
  memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion y.out 48 ∗ A_s.pool ∗
  protocolAddressAt A_s y.g.peer y.g.peerA ∗ protocolAddressAt A_s y.g.me y.g.meA ∗
  coinsInstalledPlaced y.g.coinsP y.g.coins ∗ tokenInitPlacedAt ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B)

private abbrev p2OkCoroChunk {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (w : PathAEntryWords) (rngPtr : BitVec 64) : SepProp :=
  ((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
  processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
  coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
  (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
  memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
  ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
  ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
  memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗ memRegion (y.fut + 0x488#64) 8 ∗
  memRegion (y.fut + 0x4b0#64) 65 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
  p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6

private abbrev p2OkStkChunk {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (sp fp : BitVec 64) : SepProp :=
  (cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
    cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 288 ∗
    memRegion (fp + 0xffffffffffffff80#64) 9 ∗ sp550P2V1RemAt sp) ∗
  (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
  ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗ ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0xbc#64) 4 ∗
  ((sp + 0xd0#64) ↦₆₄ m.spkId.zeroExtend 64) ∗ memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗ memRegion (sp + 0x310#64) 36 ∗
  memRegion (sp + 0x340#64) 36 ∗ spMidGapsAt sp ∗ ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
  ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗ ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
  memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗ memRegion (sp + 0x538#64) 24

private abbrev p2OpenedStoresChunk {M : AllocCostModel} {A_b : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement] (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords) : SepProp :=
  (cliPollSessKitPlaced A_s y.g.F scopeKit y.g.peer (cliKitStk B)).storeAt
    (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
  (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B)).identityAt y.g.stores StoresGhost.opened.identity ∗
  (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B)).storeAt
    (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
  (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B)).storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
  (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId (pmOfE m i).baseKey (cliKitStk B)).storeAt
    (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
  dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub

private theorem stageP2_entry_unpack_pathA_d3_placed_ext {W : PEParams}
    {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_p1 Scope : SessionRecord (List (BitVec 8)) → Prop} [LibsignalPlacement] (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ W Scope y.g.F y.g.peer.val y.g.me.val (pmOfE m i))
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val) (hScope : ∀ r', Scope r' → scopeIn r') :
    stageP2PostP1At A_s y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope_p1 A_s y.fut none ∗ preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A_s y.g.peer y.g.peerA ∗ protocolAddressAt A_s y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A_s y.g.stores StoresGhost.opened ∗
    tokenInitPlacedAt ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords,
        ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        stageP2PreAtPlaced A_s (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8 w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed A_s y i rngPtr sp) := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  rw [hbk_eq]; dsimp only [p1LoadedRecordAt, stageP2PostP1At]
  have hdrEq : CryptoVerification.E2E.Pqxdh.ResponderClosure.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) =
      CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) := rfl
  rw [hdrEq, coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗ storesAt A_s y.g.stores StoresGhost.opened ∗
    (CryptoVerification.E2E.Pqxdh.ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) ∗
      memRegion (y.fut + 0x100#64) 336 ∗ p2EntryTail A_s y s0 sp rngPtr v_a8 v_b8 v_d0)
    by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA_d3 A_s y.g.msgG y.g.msgA m i hpk hmsg_i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun hopkWord => ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (pathAMsgRemInnerAtD3_dup_kyberPtr A_s y.g.msgG y.g.msgA y.g.msg)))) ?_
  rw [pull_pure_msg_group]; refine Entails.pure_left fun hctBuf_nz => ?_
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := A_s) 0#64
    (cliKitStk B) y.g.stores StoresGhost.opened (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdec0) (cliIdInv_opened_peer hFok) (cliPkInv_opened hdec0 opkWord)
    (cliSpkInv_opened hdec0 m.spkId) (cliKpkInvFull_opened hdec0 m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  refine Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
    (Entails.pure_right ⟨hctBuf_nz, hopkWord⟩ ?_)
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt, stageP2PreAtPlaced, p2EntryTail,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2PreAtPlaced, pathAInnerFrameD3Placed]
    rw [hdrEq]; sep_ac_rfl)

theorem stageP2_entry_unpack_pathA_d3_placed {W : PEParams}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_p1 Scope : SessionRecord (List (BitVec 8)) → Prop} {st_b : M.σ} {s1 : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ W Scope y.g.F y.g.peer.val y.g.me.val (pmOfE m i))
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val) (hScope : ∀ r', Scope r' → scopeIn r') :
    let A_s : RustAlloc := A.atState lim st_b s1
    stageP2PostP1At A_s y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope_p1 A.repAlloc y.fut none ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
    LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords,
        ⌜y.g.msgG.kyberPtr ≠ 0#64 ∧ (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        stageP2PreAtPlaced A_s (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8 w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed A.repAlloc y i rngPtr sp) := by
  dsimp only [LsTokenInit]
  have hp1 : p1LoadedRecordAt Scope_p1 A.repAlloc y.fut none =
      p1LoadedRecordAt Scope_p1 (A.atState lim st_b s1) y.fut none := rfl
  rw [hp1, ← preKeyMsgAt_atState_eq_repAlloc A lim st_b s1 y.g.msgG y.g.msgA y.g.msg]
  refine Entails.trans (stageP2_entry_unpack_pathA_d3_placed_ext (A.atState lim st_b s1)
    y m i s0 sp fp rngPtr v_a8 v_b8 v_d0 hpk hmsg_i hfp hdec0 hFok hScope) ?_
  refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
  rw [pathAInnerFrameD3Placed_atState_eq_repAlloc st_b s1 y i rngPtr sp]; exact Entails.refl _

abbrev d3_stageP2PathA_poll_placedBudget := @stageP2_entry_unpack_pathA_d3_placed

set_option maxHeartbeats 800000 in
private theorem p2ErrFrame_fold_pathA_d3_placed_ext {M : AllocCostModel} {A_b : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement] (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i) (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    (decResAt A_s y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B)).storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B)).identityAt y.g.stores StoresGhost.opened.identity ∗
    p2ErrFrameAtPlaced A_s s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed A_s y i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt A_s y.out (.error err) ∗
      storesAt A_s y.g.stores StoresGhost.opened ∗ preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A_s y.g.peer y.g.peerA ∗ protocolAddressAt A_s y.g.me y.g.meA ∗
      lsLogOff ∗ A_s.pool ∗ stackAt sp (dpClosSubStack B) ∗ anyHeap := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  rw [hbk_eq]
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A_s) 0#64
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer) (pid := w.opkWord) (sid := m.spkId)
    (kid := m.kpkId) (kbk := (pmOfE m i).baseKey) (cliKitStk B) y.g.stores StoresGhost.opened
  have hmsgFold : p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A_s y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtD3 A_s y.g.msgG y.g.msgA y.g.msg ⊢
      preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg := by
    refine Entails.trans
      (p2MsgFields_reassemble_slices_d3 A_s y.g.msgG y.g.msgA m i hpk hmsg_i w.opkWord hopk) ?_
    rw [preKeyMsgAt_eq_base_idKey_sep]; exact Entails.of_eq (by sep_ac_rfl)
  have hcoro := p2_coro_err_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstk := p2_stack_err_fold sp fp s0 hfp
  have hany : coinsInstalledPlaced y.g.coinsP y.g.coins ∗ tokenInitPlacedAt ∗ anyHeap ⊢ anyHeap :=
    entails_anyHeap _
  dsimp only [p2ErrFrameAtPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2ErrFrameAtPlaced,
    pathAInnerFrameD3Placed]
  refine Entails.trans (show _ ⊢
    (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 0xe0#64) 368 ∗ cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      memRegion (y.fut + 0x298#64) 20 ∗ memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗ ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗ memRegion (y.fut + 0x488#64) 8 ∗
      memRegion (y.fut + 0x4b0#64) 65 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6) ∗
    ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0x80#64) 88 ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x270#64) 9 ∗
      memRegion (sp + 0x279#64) 39 ∗ memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3a0#64) 8 ∗ memRegion (sp + 0x3ac#64) 1 ∗ memRegion (sp + 0x3b0#64) 48 ∗
      memRegion (sp + 0x3e0#64) 368 ∗ spMidGapsAt sp ∗ cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 288 ∗
      memRegion (fp + 0xffffffffffffff80#64) 9 ∗ sp550P2V1RemAt sp ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) ∗
    decResAt A_s y.out (.error err) ∗
    cliPollStoresKitsAt A_s 0#64 y.g.F scopeKit y.g.peer
      w.opkWord m.spkId m.kpkId (pmOfE m i).baseKey (cliKitStk B) y.g.stores StoresGhost.opened ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A_s y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtD3 A_s y.g.msgG y.g.msgA y.g.msg) ∗
    protocolAddressAt A_s y.g.peer y.g.peerA ∗ protocolAddressAt A_s y.g.me y.g.meA ∗
    lsLogOff ∗ A_s.pool ∗ stackAt sp (dpClosSubStack B) ∗
    (coinsInstalledPlaced y.g.coinsP y.g.coins ∗ tokenInitPlacedAt ∗ anyHeap)
    by exact Entails.of_eq (by dsimp only [cliPollStoresKitsAt]; sep_ac_rfl)) ?_
  exact sepConj_mono hcoro (sepConj_mono hstk (sepConj_mono_right
    (sepConj_mono hstores (sepConj_mono hmsgFold
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hany)))))))))

theorem p2ErrFrame_fold_pathA_d3_placed_rep {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} {stf : M.σ} {sf : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i) (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    let A_s : RustAlloc := A.atState lim stf sf
    (decResAt A.repAlloc y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B)).storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B)).identityAt y.g.stores StoresGhost.opened.identity ∗
    p2ErrFrameAtPlaced A_s s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed A.repAlloc y i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗ memRegion sp 3280 ∗ decResAt A.repAlloc y.out (.error err) ∗
      storesAt A.repAlloc y.g.stores StoresGhost.opened ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      lsLogOff ∗ A.pool lim stf sf ∗ stackAt sp (dpClosSubStack B) ∗ anyHeap := by
  dsimp only
  have hdec := decResAt_err_atState_eq_repAlloc A lim stf sf y.out err
  rw [← hdec, ← pathAInnerFrameD3Placed_atState_eq_repAlloc stf sf y i rngPtr sp]
  refine Entails.trans (p2ErrFrame_fold_pathA_d3_placed_ext (A.atState lim stf sf) y m i w
    s0 sp fp rngPtr err hpk hmsg_i hfp hopk) ?_
  rw [hdec, preKeyMsgAt_atState_eq_repAlloc A lim stf sf y.g.msgG y.g.msgA y.g.msg]; exact Entails.refl _

private theorem p2_coro_ok_with_opk_d3_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (w : PathAEntryWords) (rngPtr : BitVec 64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    p2OkCoroChunk y m w rngPtr ⊢
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) := by
  have hopkSlot := p2_coro_opk_slot_fold y.fut m.opkId w.opkWord hopk
  have hcoro := p2_coro_ok_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
    (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId))
  exact Entails.trans (sepConj_mono_left hopkSlot) (Entails.trans (by sep_frame) hcoro)

set_option maxHeartbeats 800000 in
private theorem p2OkPost_fold_pathA_d3_placed_alloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement] (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64) (recG : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hcoins : y.g.coins.length < 2 ^ 63) (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64) (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut) (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    p2OkPostAtPlaced A_s (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG st_bob (mkPathAHdr m) i.messageVersion 0#8
      w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed A_s y i rngPtr sp) ⊢
      tokenInitPlacedAt ∗
      genP3PrePlaced A_s s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
        y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        recG st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
      stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt A_s y.g.msgG y.g.msgA y.g.msg ∗ storesAt A_s y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hmsgSlices := p2MsgFields_reassemble_slices_d3 A_s y.g.msgG y.g.msgA m i hpk hmsg_i w.opkWord hopk
  rw [hbk_eq, hmsg_i] at hmsgSlices ⊢; unfold genP3PrePlaced; rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _))))
  dsimp only [p2OkPostAtPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2OkPostAtPlaced,
    pathAInnerFrameD3Placed]
  unfold genP3CallFramePlaced stageP3Sub5ExtraPre
  rw [hsp2, hdrOpkIdBv?_mkPathAHdr m, kpkId_shift_or_one_eq_append_d3 m.kpkId]
  have hstkSub : stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ stackAt sp chainCloneStack) := by
    rw [stackAt_sub_eq sp (dpClosSubStack B) rootStack (by unfold rootStack dpClosSubStack; omega)
          (Nat.le_trans hsub (Nat.le_of_lt sp.isLt)), stackAt_root_eq_chainClone sp]
  have h270 : memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 = memRegion (sp + 0x270#64) 48 := by
    rw [memRegion_split (sp + 0x270#64) 9 39 (by decide)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h3e0 : memRegion (sp + 0x3e0#64) 368 = memRegion (sp + 0x3e0#64) 34 ∗
      memRegion (sp + 0x402#64) 70 ∗ memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp, memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
  have hc := coinsInstalledPlaced_entails_coinsAtPlaced y.g.coinsP y.g.coins hcoins
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A_s) 0#64
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer) (pid := w.opkWord) (sid := m.spkId)
    (kid := m.kpkId) (kbk := (pmOfE m i).baseKey) (cliKitStk B) y.g.stores StoresGhost.opened
  dsimp only [cliPollStoresKitsAt] at hstores; rw [hstkSub, h3e0]
  refine Entails.trans (show _ ⊢
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ p2OkCoroChunk y m w rngPtr ∗
    p2OkStkChunk y m sp fp ∗ p2OpenedStoresChunk A_s y m i w ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A_s y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtD3 A_s y.g.msgG y.g.msgA y.g.msg) ∗
    ((memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39) ∗
      tokenInitPlacedAt ∗ sessionStateAt A_s (y.fut + 0xf8#64) recG st_bob ∗ A_s.pool ∗ stackAt sp chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ i.messageVersion.zeroExtend 32) ∗ ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A_s y.g.peer y.g.peerA ∗
      protocolAddressAt A_s y.g.me y.g.meA ∗ lsLogOff ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x448#64) 240 ∗ ((y.fut + 0xe0#64) ↦₆₄ 0#64) ∗
      ((y.fut + 0xe8#64) ↦₆₄ 8#64) ∗ ((y.fut + 0xf0#64) ↦₆₄ 0#64) ∗ ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      memRegion y.out 48 ∗ memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x370#64) 36 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
    by sep_frame) ?_
  rw [h270]
  refine Entails.trans (sepConj_mono hc (sepConj_mono (p2_coro_ok_with_opk_d3_placed y m w rngPtr hopk)
    (sepConj_mono (p2_stk_ok_fold_d3_placed sp fp y.fut y.g.msgA y.g.peerA m.spkId hfp)
      (sepConj_mono hstores (sepConj_mono_left hmsgSlices))))) ?_
  sep_frame

theorem p2OkPost_fold_pathA_d3_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} {st_b : M.σ} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64) (recG : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hcoins : y.g.coins.length < 2 ^ 63) (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64) (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut) (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    let A_s : RustAlloc := A.atState lim st_b s2
    p2OkPostAtPlaced A_s (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG st_bob (mkPathAHdr m) i.messageVersion 0#8
      w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed A.repAlloc y i rngPtr sp) ⊢
      LsTokenInit ∗
      genP3Pre_placed A lim st_b s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
        y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        recG st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
      stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  dsimp only [LsTokenInit, genP3Pre_placed]
  rw [← pathAInnerFrameD3Placed_atState_eq_repAlloc st_b s2 y i rngPtr sp,
      ← preKeyMsgRemBaseIdKeyAt_atState_eq_repAlloc A lim st_b s2 y.g.msgG y.g.msgA y.g.msg]
  exact p2OkPost_fold_pathA_d3_placed_alloc (A.atState lim st_b s2) y m i w s0 s2 sp fp rngPtr
    recG st_bob hpk hmsg_i hcoins hsub hfp hopk hsp2 hx19_2 hx27_2

private theorem stageP2_entry_unpack_pathCOver_d3_placed_ext {W : PEParams}
    {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_dec Scope : SessionRecord (List (BitVec 8)) → Prop} [LibsignalPlacement] (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) (hcur : r.currentSession = some sess)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ W Scope_dec y.g.F y.g.peer.val y.g.me.val (pmOfE m i))
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val) (hScope : ∀ r', Scope r' → scopeIn r') :
    stageP2PostP1At A_s y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A_s y.fut (some r) ∗ preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A_s y.g.peer y.g.peerA ∗ protocolAddressAt A_s y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A_s y.g.stores StoresGhost.opened ∗
    tokenInitPlacedAt ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜scopeKit r ∧ g.cur = some recG ∧ CanonSession recG sess ∧ y.g.msgG.kyberPtr ≠ 0#64 ∧
          (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP2OverPreAtPlaced A_s 0#64
          (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8 w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B) (pathAInnerFrameD3Placed A_s y i rngPtr sp) := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  rw [hbk_eq, sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]; simp only [sepConj_assoc]; refine Entails.pure_left fun hkit => ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun g => ?_
  refine Entails.trans (sepConj_mono_left (sessionRecordAt_some_eq_prev_sess A_s y.fut g r sess hcur)) ?_
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun recG => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun hgcur => ?_; rw [sepConj_assoc]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sessionAt_dup_canonSession A_s (y.fut + 0xf8#64) recG sess))) ?_
  simp only [sepConj_assoc]; rw [pull_pure_after1]; refine Entails.pure_left fun hcanon => ?_
  dsimp only [stageP2PostP1At]; rw [coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗ storesAt A_s y.g.stores StoresGhost.opened ∗
    (CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A_s y.fut g ∗
      sessionStateReprAt A_s (y.fut + 0xf8#64) recG sess ∗
      p2EntryTail A_s y s0 sp rngPtr v_a8 v_b8 v_d0)
    by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA_d3 A_s y.g.msgG y.g.msgA m i hpk hmsg_i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]; refine Entails.pure_left fun hopkWord => ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (pathAMsgRemInnerAtD3_dup_kyberPtr A_s y.g.msgG y.g.msgA y.g.msg)))) ?_
  rw [pull_pure_msg_group]; refine Entails.pure_left fun hctBuf_nz => ?_
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := A_s) 0#64
    (cliKitStk B) y.g.stores StoresGhost.opened (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdec0) (cliIdInv_opened_peer hFok) (cliPkInv_opened hdec0 opkWord)
    (cliSpkInv_opened hdec0 m.spkId) (cliKpkInvFull_opened hdec0 m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  have hprevEq : CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A_s y.fut g =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A_s y.fut g := rfl
  refine Entails.sepExists_right g (Entails.sepExists_right recG
    (Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
      (Entails.pure_right ⟨hkit, hgcur, hcanon, hctBuf_nz, hopkWord⟩ ?_)))
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt, p2EntryTail,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP2OverPreAtPlaced,
      pathAInnerFrameD3Placed, lsLogOff]
    rw [hprevEq]; sep_ac_rfl)

theorem stageP2_entry_unpack_pathCOver_d3_placed {W : PEParams}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_dec Scope : SessionRecord (List (BitVec 8)) → Prop} {st_b : M.σ} {s1 : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) (hcur : r.currentSession = some sess)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ W Scope_dec y.g.F y.g.peer.val y.g.me.val (pmOfE m i))
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val) (hScope : ∀ r', Scope r' → scopeIn r') :
    stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A.repAlloc y.fut (some r) ∗ preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗ protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
    LsTokenInit ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜scopeKit r ∧ g.cur = some recG ∧ CanonSession recG sess ∧ y.g.msgG.kyberPtr ≠ 0#64 ∧
          (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        stageP2OverPreAtPlaced A lim 0#64
          (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
          st_b s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8 w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B)
          (pathAInnerFrameD3Placed A.repAlloc y i rngPtr sp) := by
  dsimp only [LsTokenInit]
  rw [← p1LoadedRecordAt_atState_eq_repAlloc A lim st_b s1 scopeKit y.fut (some r),
      ← preKeyMsgAt_atState_eq_repAlloc A lim st_b s1 y.g.msgG y.g.msgA y.g.msg]
  refine Entails.trans (stageP2_entry_unpack_pathCOver_d3_placed_ext (A.atState lim st_b s1)
    y r sess m i s0 sp fp rngPtr v_a8 v_b8 v_d0 hcur hpk hmsg_i hfp hdec0 hFok hScope) ?_
  refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  refine Entails.sepExists_elim fun recG => Entails.sepExists_right recG ?_
  refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
  dsimp only [stageP2OverPreAtPlaced]
  rw [pathAInnerFrameD3Placed_atState_eq_repAlloc st_b s1 y i rngPtr sp]; exact Entails.refl _

abbrev d3_stageP2PathC_poll_placedBudget := @stageP2_entry_unpack_pathCOver_d3_placed

set_option maxHeartbeats 800000 in
private theorem p2OverOkPost_fold_pathCOver_d3_placed_alloc {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement] (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8))) (hcanon : CanonSession recG sess)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hcoins : y.g.coins.length < 2 ^ 63) (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64) (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut) (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverOkPostAtPlaced A_s 0#64
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed A_s y i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗ tokenInitPlacedAt ∗
        genP3PrePlaced A_s s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 A_s s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (encSession (clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt A_s y.g.msgG y.g.msgA y.g.msg ∗ storesAt A_s y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hmsgSlices := p2MsgFields_reassemble_slices_d3 A_s y.g.msgG y.g.msgA m i hpk hmsg_i w.opkWord hopk
  rw [hbk_eq, hmsg_i] at hmsgSlices ⊢
  dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverOkPostAtPlaced,
    prevArchived1At, pathAInnerFrameD3Placed]
  rw [encSessionMem_clearPending_eq hcanon]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun prevCap' => Entails.sepExists_elim fun prevPtr' => ?_
  simp only [sepConj_assoc]; rw [pull_pure_after7]; refine Entails.pure_left fun hcap_ne => ?_
  refine Entails.sepExists_right prevCap' (Entails.sepExists_right prevPtr' (Entails.pure_right hcap_ne ?_))
  unfold genP3PrePlaced; rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _))))
  unfold genP3CallFramePlaced p2StageP3Sub5ExtraPrePrev1
  rw [hsp2, hdrOpkIdBv?_mkPathAHdr m, kpkId_shift_or_one_eq_append_d3 m.kpkId]
  have hstkSub : stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ stackAt sp chainCloneStack) := by
    rw [stackAt_sub_eq sp (dpClosSubStack B) rootStack (by unfold rootStack dpClosSubStack; omega)
          (Nat.le_trans hsub (Nat.le_of_lt sp.isLt)), stackAt_root_eq_chainClone sp]
  have h270 : memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 = memRegion (sp + 0x270#64) 48 := by
    rw [memRegion_split (sp + 0x270#64) 9 39 (by decide)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h3e0 : memRegion (sp + 0x3e0#64) 368 = memRegion (sp + 0x3e0#64) 34 ∗
      memRegion (sp + 0x402#64) 70 ∗ memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp, memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
  have hc := coinsInstalledPlaced_entails_coinsAtPlaced y.g.coinsP y.g.coins hcoins
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A_s) 0#64
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer) (pid := w.opkWord) (sid := m.spkId)
    (kid := m.kpkId) (kbk := (pmOfE m i).baseKey) (cliKitStk B) y.g.stores StoresGhost.opened
  dsimp only [cliPollStoresKitsAt] at hstores; rw [hstkSub, h3e0]; dsimp only [lsLogOff]
  refine Entails.trans (show _ ⊢
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗ p2OkCoroChunk y m w rngPtr ∗
    p2OkStkChunk y m sp fp ∗ p2OpenedStoresChunk A_s y m i w ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A_s y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtD3 A_s y.g.msgG y.g.msgA y.g.msg) ∗
    ((memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39) ∗
      tokenInitPlacedAt ∗ sessionStateAt A_s (y.fut + 0xf8#64) G_bob st_bob ∗ A_s.pool ∗ stackAt sp chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ i.messageVersion.zeroExtend 32) ∗ ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗ protocolAddressAt A_s y.g.peer y.g.peerA ∗
      protocolAddressAt A_s y.g.me y.g.meA ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x448#64) 240 ∗
      prevVecAt A_s (y.fut + 0xe0#64) prevCap' prevPtr' [encSession (clearPending sess)] ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ memRegion y.out 48 ∗ memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
    by sep_frame) ?_
  rw [h270]
  refine Entails.trans (sepConj_mono hc (sepConj_mono (p2_coro_ok_with_opk_d3_placed y m w rngPtr hopk)
    (sepConj_mono (p2_stk_ok_fold_d3_placed sp fp y.fut y.g.msgA y.g.peerA m.spkId hfp)
      (sepConj_mono hstores (sepConj_mono_left hmsgSlices))))) ?_
  sep_frame

theorem p2OverOkPost_fold_pathCOver_d3_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} {st_b : M.σ} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8))) (hcanon : CanonSession recG sess)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hcoins : y.g.coins.length < 2 ^ 63) (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64) (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut) (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    p2OverOkPostAtPlaced A lim 0#64
      (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      st_b s0 s2 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed A.repAlloc y i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗ LsTokenInit ∗
        genP3Pre_placed A lim st_b s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (encSession (clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗ storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  dsimp only [p2OverOkPostAtPlaced, LsTokenInit, genP3Pre_placed]
  rw [← pathAInnerFrameD3Placed_atState_eq_repAlloc st_b s2 y i rngPtr sp]
  refine Entails.trans (p2OverOkPost_fold_pathCOver_d3_placed_alloc (A.atState lim st_b s2)
    y m i w s0 s2 sp fp rngPtr recG G_bob sess st_bob hcanon hpk hmsg_i hcoins hsub hfp hopk
    hsp2 hx19_2 hx27_2) ?_
  refine Entails.sepExists_elim fun prevCap' => Entails.sepExists_right prevCap' ?_
  refine Entails.sepExists_elim fun prevPtr' => Entails.sepExists_right prevPtr' ?_
  rw [preKeyMsgRemBaseIdKeyAt_atState_eq_repAlloc A lim st_b s2 y.g.msgG y.g.msgA y.g.msg]
  exact Entails.refl _

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonStage2PollPlacedBudget
