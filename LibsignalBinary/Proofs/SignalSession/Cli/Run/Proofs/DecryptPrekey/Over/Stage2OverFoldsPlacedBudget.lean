/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFolds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Placed CLI Poll Stage P2 Over-Path (`Path C`) Spatial Folds

Generalizes the Stage P2 Over-path (`Path C`) inner spatial frame, stack budget bounds, `+0x0868`
entry spatial unpack, and `+0x1778` `Prev1` normal-exit spatial fold to any `RustCliAllocBudget M`
via `A.repAlloc` and `A.atState lim st s`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (PublicKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage Session SessionRecord)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3SpillAll)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  coroOpkIdAtP4 opkOptTag32 p1LoadedRecordAt p2CoroScratchTailAt p2MsgFieldsAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  prevArchived1At stageP2OverV1CallStack stageP2OverV1CallStack4K stageP2OverV1CallStack4K_eq
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (clearPending prevVecAt)
open CryptoVerification.E2E (PEParams PreKeyMessageFields)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyActive10At processPrekeyPostTrustAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stackAt_sub_eq)
open CryptoVerification.E2E.Record (encSession)
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec
)
open CryptoVerification.LibsignalPublicApiRepr (
  PreKeyMsgGhost RecordGhost preKeyMsgAt sessionRecordAt sessionStateReprAt
)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt sessionStateAt
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (
  StoresGhost cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym
  cliSignedPreKeyVtSym dirAt
)
open CryptoVerification.SignalSession.Cli.MainHops (coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOk₀ pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  LsTokenInit PathAEntryWords cliIdInv_opened_peer cliIdOwnInv_opened cliKitStk
  cliKpkInvFull_opened cliPkInv_opened cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced
  cliPollSelfKitPlaced cliPollSessKitPlaced cliPollSpkKitPlaced cliPollStoresKitsAt
  cliPollStoresKitsAt_entails_storesAt cliSessInv_opened_scopeKit cliSpkInv_opened
  closStackUnusedP1OkAt coroCopyAt_eq_head3_tail11 coroCopyTail11At coroUnusedP1At
  coro_unused_split_p2v1 dpClosSubStack genP3CallFramePlaced genP3PrePlaced hdrOpkIdBv?_mkPathAHdr
  mkPathAHdr p2MsgFields_reassemble_slices_ext p2StageP3Sub5ExtraPrePrev1 p2_coro_ok_fold
  p2_coro_opk_slot_fold pathAMsgRemInnerAtExt pathAMsgRemInnerAt_dup_kyberPtr_ext pmOfE_fields
  preKeyMsgAt_unpack_pathA_ext preKeyMsgRemBaseIdKeyAt processPrekeyInnerInitAt_eq_330_388_rem23
  processPrekeyInnerRem23At sessionRecordAt_some_eq_prev_sess signalMessageRestVerAt
  sp550P2V1RemAt spHighGapsAt spMidGapsAt sp_3e0_344_eq_104_240 sp_3e0_368_eq_344_24
  sp_550_1824_split_genP3 sp_550_1824_split_p2v1 stackAt_root_eq_chainClone stack_match_fold
  stack_unused_split_p2v1 stageP2PostP1At stageP3CoroFrameAt stageP3StackFrameAt
  storesAt_entails_cliPollStoresKitsAt
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll.OverP2Inst (
  encSessionMem_clearPending_eq encSessionMem_clearPending_lt_32 p2Over_not_sessMatchesMsg
  p2Over_serBytes_len sessionAt_dup_canonSession stageP2OverV1CallStack_le_subStack
  subroutine_ok_inImage_of_spec_map subroutine_ok_of_spec_map
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  FilesOkPeer coinsInstalledPlaced_entails_coinsAtPlaced scopeIn scopeKit
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget (
  p2OverOkPostAtPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5PlacedBudget (
  stageP2OverPreAtPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4SpatialPlacedBudget (
  overGenP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  genP3Pre_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget (
  p2ErrFrameAtPlaced p2ErrFrame_fold_pathA_placed p2ErrFrame_fold_pathA_placed_ext
  p2ErrFrame_fold_pathA_placed_rep pathAInnerFramePlaced_atState_eq_repAlloc
  pathAInnerFrame_dup_kyberPtr_placed preKeyMsgAt_atState_eq_repAlloc
  preKeyMsgRemBaseIdKeyAt_atState_eq_repAlloc
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)

export CryptoVerification.SignalSession.Cli.RunProofs.Poll.OverP2Inst (
  encSessionMem_clearPending_eq
  encSessionMem_clearPending_lt_32
  p2Over_not_sessMatchesMsg
  p2Over_serBytes_len
)
export CryptoVerification.SignalSession.Cli.RunProofs.Poll.OverP2Inst (
  subroutine_ok_inImage_of_spec_map
  subroutine_ok_of_spec_map
)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget (
  p2ErrFrameAtPlaced
  p2ErrFrame_fold_pathA_placed
  p2ErrFrame_fold_pathA_placed_ext
  p2ErrFrame_fold_pathA_placed_rep
)

/-! ## 1. Stack Budget Bounds & Inner Spatial Frame -/

/-- Placed `Over.stageP2OverV1CallStack` fits within `dpClosSubStack B` for the CLI Poll store kits
under any `A : RustAlloc` (in particular `A_b.repAlloc` and `A_b.atState lim st s`). -/
theorem stageP2OverV1CallStack_le_subStack_placed {A : RustAlloc} [LibsignalPlacement]
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2OverV1CallStack
      (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKitPlaced A F0 opkIdWord (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  stageP2OverV1CallStack_le_subStack (A := A) 0#64 F0 peer spkId kpkId opkIdWord kbk B

/-- Placed `Over.stageP2OverV1CallStack4K` fits within `dpClosSubStack B` for the CLI Poll store
kits under any `A : RustAlloc`. -/
theorem stageP2OverV1CallStack4K_le_subStack_placed {A : RustAlloc} [LibsignalPlacement]
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2OverV1CallStack4K
      (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKitPlaced A F0 opkIdWord (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  rw [stageP2OverV1CallStack4K_eq]
  exact stageP2OverV1CallStack_le_subStack_placed F0 peer spkId kpkId opkIdWord kbk B

/-- Placed inner coroutine/stack/message frame preserved untouched across `stageP2_over_v1_kits`
under `[LibsignalPlacement]`, parameterized by representation allocator `A_r : RustAlloc` and
budget-threaded poll ghost `y`. -/
abbrev pathAInnerFramePlaced :=
  @LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced

abbrev pathCOverInnerFramePlaced :=
  @LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced

/-! ## 2. Representation-Invariance Bridges (`A.atState lim st s` ↔ `A.repAlloc`) -/

theorem sessionRecordAt_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (g : RecordGhost) (rec : SessionRecord (List (BitVec 8))) :
    sessionRecordAt (A.atState lim st s) r g rec = sessionRecordAt A.repAlloc r g rec :=
  rfl

theorem p1LoadedRecordAt_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (fut : BitVec 64)
    (opt : Option (SessionRecord (List (BitVec 8)))) :
    p1LoadedRecordAt Scope (A.atState lim st s) fut opt =
      p1LoadedRecordAt Scope A.repAlloc fut opt := by
  cases opt <;> rfl

theorem p2StageP3Sub5ExtraPrePrev1_atState_eq_repAlloc {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s_pool s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (b_2c0 : BitVec 8) :
    p2StageP3Sub5ExtraPrePrev1 (A.atState lim st s_pool) s0 s
        coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 =
      p2StageP3Sub5ExtraPrePrev1 A.repAlloc s0 s
        coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 :=
  rfl

theorem stageP2OverPreAtPlaced_cliPoll_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : CryptoVerification.E2E.Pqxdh.Initiator.HandshakeHdr)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (kbk : PublicKey)
    (stSpk : (cliPollSpkKitPlaced A.repAlloc F0 signedPreKeyId (cliKitStk B)).SpkState)
    (stKpk : (cliPollKpkKitPlaced A.repAlloc F0 kyberPreKeyId signedPreKeyId kbk (cliKitStk B)).KpkState)
    (stPk : (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B)).PkState)
    (stId : (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B)).IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp) :
    stageP2OverPreAtPlaced A lim 0#64
        (cliPollSpkKitPlaced A.repAlloc F0 signedPreKeyId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kyberPreKeyId signedPreKeyId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        st s0 s
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP2OverPreAtPlaced
        (A.atState lim st s) 0#64
        (cliPollSpkKitPlaced (A.atState lim st s) F0 signedPreKeyId (cliKitStk B))
        (cliPollKpkKitPlaced (A.atState lim st s) F0 kyberPreKeyId signedPreKeyId kbk (cliKitStk B))
        (cliPollPkKitPlaced (A.atState lim st s) F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced (A.atState lim st s) F0 peer (cliKitStk B))
        s0
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame :=
  rfl

theorem p2OverOkPostAtPlaced_cliPoll_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 sf : State)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388 : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (G_bob : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hdr : CryptoVerification.E2E.Pqxdh.Initiator.HandshakeHdr)
    (msgVerByte b_2c0 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (kbk : PublicKey)
    (stSpk' : (cliPollSpkKitPlaced A.repAlloc F0 signedPreKeyId (cliKitStk B)).SpkState)
    (stKpk' : (cliPollKpkKitPlaced A.repAlloc F0 kyberPreKeyId signedPreKeyId kbk (cliKitStk B)).KpkState)
    (stPk' : (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B)).PkState)
    (stId : (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B)).IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    p2OverOkPostAtPlaced A lim 0#64
        (cliPollSpkKitPlaced A.repAlloc F0 signedPreKeyId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kyberPreKeyId signedPreKeyId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        st s0 sf
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
        recG sess G_bob st_bob hdr msgVerByte b_2c0
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk' stKpk' stPk' stId gMe gPeer stk Frame =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverOkPostAtPlaced
        (A.atState lim st sf) 0#64
        (cliPollSpkKitPlaced (A.atState lim st sf) F0 signedPreKeyId (cliKitStk B))
        (cliPollKpkKitPlaced (A.atState lim st sf) F0 kyberPreKeyId signedPreKeyId kbk (cliKitStk B))
        (cliPollPkKitPlaced (A.atState lim st sf) F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced (A.atState lim st sf) F0 peer (cliKitStk B))
        s0
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
        recG sess G_bob st_bob hdr msgVerByte b_2c0
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk' stKpk' stPk' stId gMe gPeer stk Frame :=
  rfl

/-! ## 3. Pure-Fact Duplication Helpers -/

private theorem dup_pure_sepConj_right {φ : Prop} {P Q : SepProp}
    (h : Q ⊢ ⌜φ⌝ ∗ Q) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_right h) (by rw [sepConj_pure_left_comm]; exact Entails.refl _)

private theorem dup_pure_sepConj_left {φ : Prop} {P Q : SepProp}
    (h : P ⊢ ⌜φ⌝ ∗ P) : P ∗ Q ⊢ ⌜φ⌝ ∗ (P ∗ Q) :=
  Entails.trans (sepConj_mono_left h) (by rw [sepConj_assoc]; exact Entails.refl _)

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` to the front of `stageP2OverPreAtPlaced`. -/
theorem stageP2OverPreAt_dup_kyberPtr_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    {A_r : RustAlloc}
    {spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64}
    {kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64}
    {pkKit : PreKeyStoreSpec A.repAlloc 0#64}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (st : M.σ) (s0 s : State)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    stageP2OverPreAtPlaced A lim 0#64 spkKit kpkKit pkKit ikit st s0 s
      sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      stSpk stKpk stPk stId y.g.me y.g.peer g recG sess (dpClosSubStack B)
      (pathAInnerFramePlaced A_r y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2OverPreAtPlaced A lim 0#64 spkKit kpkKit pkKit ikit st s0 s
      sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      stSpk stKpk stPk stId y.g.me y.g.peer g recG sess (dpClosSubStack B)
      (pathAInnerFramePlaced A_r y m i rngPtr sp) := by
  unfold stageP2OverPreAtPlaced pathAInnerFramePlaced
  repeat (first
    | exact pathAInnerFrame_dup_kyberPtr_placed A_r y m i rngPtr sp
    | exact dup_pure_sepConj_left (pathAInnerFrame_dup_kyberPtr_placed A_r y m i rngPtr sp)
    | refine dup_pure_sepConj_right ?_)

private theorem pull_pure_after1 {A1 Rest : SepProp} {φ : Prop} :
    A1 ∗ (⌜φ⌝ ∗ Rest) = ⌜φ⌝ ∗ (A1 ∗ Rest) := by
  sep_ac_rfl

private theorem pull_pure_msg_group {M1 M2 M3 Tail : SepProp} {φ : Prop} :
    (M1 ∗ M2 ∗ (⌜φ⌝ ∗ M3)) ∗ Tail = ⌜φ⌝ ∗ ((M1 ∗ M2 ∗ M3) ∗ Tail) := by
  sep_ac_rfl

private theorem pull_pure_after7 {A1 A2 A3 A4 A5 A6 A7 Rest : SepProp} {φ : Prop} :
    A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ (⌜φ⌝ ∗ Rest))))))) =
      ⌜φ⌝ ∗ (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ Rest))))))) := by
  sep_ac_rfl

/-! ## 4. Placed Stage P2 Over-Path (`Path C`) Entry Spatial Unpack (`+0x0868`) -/

/-- `RustAlloc`-polymorphic Stage P2 Over-path (`Path C`) entry spatial unpack into
`Over.stageP2OverPreAtPlaced A_s`. -/
theorem stageP2_entry_unpack_pathCOver_placed_ext {W : PEParams}
    {M : AllocCostModel} {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_dec Scope : SessionRecord (List (BitVec 8)) → Prop} [LibsignalPlacement]
    (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ W Scope_dec y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → scopeIn r') :
    stageP2PostP1At A_s y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt scopeKit A_s y.fut (some r) ∗
    preKeyMsgAt A_s y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A_s y.g.peer y.g.peerA ∗
    protocolAddressAt A_s y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt A_s y.g.stores StoresGhost.opened ∗
    tokenInitPlacedAt ∗
    lsLogOff ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜scopeKit r ∧ g.cur = some recG ∧
         CanonSession recG sess ∧
         y.g.msgG.kyberPtr ≠ 0#64 ∧
         (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP2OverPreAtPlaced A_s 0#64
          (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B)
          (pathAInnerFramePlaced A_s y m i rngPtr sp) := by
  rw [hmsg]
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]
  simp only [sepConj_assoc]
  refine Entails.pure_left fun hkit => ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => ?_
  refine Entails.trans
    (sepConj_mono_left (sessionRecordAt_some_eq_prev_sess A_s y.fut g r sess hcur)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun recG => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hgcur => ?_
  rw [sepConj_assoc]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (sessionAt_dup_canonSession A_s (y.fut + 0xf8#64) recG sess))) ?_
  simp only [sepConj_assoc]
  rw [pull_pure_after1]
  refine Entails.pure_left fun hcanon => ?_
  dsimp only [stageP2PostP1At]
  rw [coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt A_s y.g.msgG y.g.msgA (pmOfE m i) ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗
    storesAt A_s y.g.stores StoresGhost.opened ∗
    (CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A_s y.fut g ∗
      sessionStateReprAt A_s (y.fut + 0xf8#64) recG sess ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion y.out 48 ∗ A_s.pool ∗
      protocolAddressAt A_s y.g.peer y.g.peerA ∗
      protocolAddressAt A_s y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      tokenInitPlacedAt ∗ lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA_ext A_s y.g.msgG y.g.msgA m i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hopkWord => ?_
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (pathAMsgRemInnerAt_dup_kyberPtr_ext A_s y.g.msgG y.g.msgA m i)))) ?_
  rw [pull_pure_msg_group]
  refine Entails.pure_left fun hctBuf_nz => ?_
  have hdec0' : DecPkOk₀ W Scope_dec y.g.F y.g.peer.val y.g.me.val (pmOfE m i) :=
    hmsg ▸ hdec0
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := A_s) 0#64
    (cliKitStk B) y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdec0')
    (cliIdInv_opened_peer hFok)
    (cliPkInv_opened hdec0' opkWord)
    (cliSpkInv_opened hdec0' m.spkId)
    (cliKpkInvFull_opened hdec0' m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  have hprevEq :
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.prevSessionsEmptyAt A_s y.fut g =
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A_s y.fut g := rfl
  refine Entails.sepExists_right g
    (Entails.sepExists_right recG
      (Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
        (Entails.pure_right ⟨hkit, hgcur, hcanon, hctBuf_nz, hopkWord⟩ ?_)))
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP2OverPreAtPlaced,
      pathAInnerFramePlaced,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced,
      lsLogOff]
    rw [hprevEq]
    sep_ac_rfl)

/-- Budget-threaded placed entry spatial unpack from `StageP2PathCOverQpanCliPlacedStmt`'s
precondition into `Over.stageP2OverPreAtPlaced (A.atState lim st_b s1)` and
`pathAInnerFramePlaced A.repAlloc`. -/
theorem stageP2_entry_unpack_pathCOver_placed_atState {W : PEParams}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_dec Scope : SessionRecord (List (BitVec 8)) → Prop}
    {st_b : M.σ} {s1 : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ W Scope_dec y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → scopeIn r') :
    let A_s : RustAlloc := A.atState lim st_b s1
    stageP2PostP1At A_s y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
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
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜scopeKit r ∧ g.cur = some recG ∧
         CanonSession recG sess ∧
         y.g.msgG.kyberPtr ≠ 0#64 ∧
         (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP2OverPreAtPlaced A_s 0#64
          (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B)
          (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) := by
  dsimp only
  have hp1 := (p1LoadedRecordAt_atState_eq_repAlloc A lim st_b s1 scopeKit y.fut (some r)).symm
  have hpm_eq := (preKeyMsgAt_atState_eq_repAlloc A lim st_b s1 y.g.msgG y.g.msgA y.g.msg).symm
  have hinner := pathAInnerFramePlaced_atState_eq_repAlloc st_b s1 y m i rngPtr sp
  have htok_eq : LsTokenInit = tokenInitPlacedAt := rfl
  rw [hp1, hpm_eq, htok_eq]
  refine Entails.trans
    (stageP2_entry_unpack_pathCOver_placed_ext (A.atState lim st_b s1)
      y r sess m i s0 sp fp rngPtr v_a8 v_b8 v_d0 hcur hmsg hfp hdec0 hFok hScope) ?_
  refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  refine Entails.sepExists_elim fun recG => Entails.sepExists_right recG ?_
  refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
  dsimp only [pathAInnerFramePlaced]
  rw [hinner]
  exact Entails.refl _

/-- Budget-threaded placed entry spatial unpack from `StageP2PathCOverQpanCliPlacedStmt`'s
precondition into `StageP2Sub5PlacedBudget.stageP2OverPreAtPlaced A lim 0#64 ... st_b s0 s1` and
`pathAInnerFramePlaced A.repAlloc`. -/
theorem stageP2_entry_unpack_pathCOver_placed {W : PEParams}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    {Scope_dec Scope : SessionRecord (List (BitVec 8)) → Prop}
    {st_b : M.σ} {s1 : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ W Scope_dec y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → scopeIn r') :
    stageP2PostP1At (A.atState lim st_b s1) y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
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
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜scopeKit r ∧ g.cur = some recG ∧
         CanonSession recG sess ∧
         y.g.msgG.kyberPtr ≠ 0#64 ∧
         (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        stageP2OverPreAtPlaced A lim 0#64
          (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
          st_b s0 s1 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer g recG sess (dpClosSubStack B)
          (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) :=
  stageP2_entry_unpack_pathCOver_placed_atState y r sess m i s0 sp fp rngPtr v_a8 v_b8 v_d0
    hcur hmsg hfp hdec0 hFok hScope

/-! ## 5. Placed Stage P2 Over-Path (`Path C`) `+0x1778` Success-Exit Spatial Fold -/

set_option maxHeartbeats 800000 in
/-- `RustAlloc`-polymorphic Stage P2 Over-path (`Path C`) `+0x1778` normal-exit spatial fold into
`genP3PrePlaced A_s ∗ p2StageP3Sub5ExtraPrePrev1 A_s ∗ stageP3CoroFrameAt ∗ ...`. -/
theorem p2OverOkPost_fold_pathCOver_placed_alloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8)))
    (hcanon : CanonSession recG sess)
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverOkPostAtPlaced A_s 0#64
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A_s y m i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        tokenInitPlacedAt ∗
        genP3PrePlaced A_s s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 A_s s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (encSession (clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
          (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
           ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt A_s y.g.msgG y.g.msgA y.g.msg ∗
        storesAt A_s y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  rw [hmsg]
  have hmsg_inner : (pmOfE m i).message = i := (pmOfE_fields m i).2.2.2.2.2.2.1
  rw [hmsg_inner]
  dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverOkPostAtPlaced,
    prevArchived1At, pathAInnerFramePlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced]
  rw [encSessionMem_clearPending_eq hcanon]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun prevCap' => Entails.sepExists_elim fun prevPtr' => ?_
  simp only [sepConj_assoc]
  rw [pull_pure_after7]
  refine Entails.pure_left fun hcap_ne => ?_
  refine Entails.sepExists_right prevCap' (Entails.sepExists_right prevPtr'
    (Entails.pure_right hcap_ne ?_))
  unfold genP3PrePlaced
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _))))
  unfold genP3CallFramePlaced p2StageP3Sub5ExtraPrePrev1
  have hkpk_or : (m.kpkId.zeroExtend 64 <<< 32) ||| 1#64 = m.kpkId ++ 1#32 := by bv_bits
  rw [hsp2, hdrOpkIdBv?_mkPathAHdr m, hkpk_or]
  have hstkSub : stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
        stackAt sp chainCloneStack) := by
    rw [stackAt_sub_eq sp (dpClosSubStack B) rootStack
          (by unfold rootStack dpClosSubStack; omega)
          (Nat.le_trans hsub (Nat.le_of_lt sp.isLt)),
        stackAt_root_eq_chainClone sp]
  have h270 : memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 =
      memRegion (sp + 0x270#64) 48 := by
    rw [memRegion_split (sp + 0x270#64) 9 39 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h3e0 : memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp,
        memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    sep_ac_rfl
  have h550 :
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp =
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 := by
    rw [← sp_550_1824_split_p2v1 sp fp hfp, sp_550_1824_split_genP3 sp]
    unfold spHighGapsAt
    rw [memRegion_split (sp + 0xa90#64) 48 296 (by decide),
        memRegion_split (sp + 0x550#64) 976 16 (by decide),
        memRegion_split (sp + 0x550#64 + 976#64) 6 10 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    sep_ac_rfl
  have hopkSlot := p2_coro_opk_slot_fold y.fut m.opkId w.opkWord hopk
  have hcoro := p2_coro_ok_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
    (coroOpkIdAtP4 y.fut m.opkId)
    (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId))
  have hstk := stack_match_fold sp y.fut y.g.msgA y.g.peerA (m.spkId.zeroExtend 64)
  have hc := coinsInstalledPlaced_entails_coinsAtPlaced y.g.coinsP y.g.coins hcoins
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A_s) 0#64
    (F0 := y.g.F) (Scope := scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores StoresGhost.opened
  dsimp only [cliPollStoresKitsAt] at hstores
  have hmsgSlices := p2MsgFields_reassemble_slices_ext A_s y.g.msgG y.g.msgA m i w.opkWord hopk
  rw [hmsg_inner] at hmsgSlices
  rw [hstkSub, h3e0]
  dsimp only [lsLogOff]
  refine Entails.trans (show _ ⊢
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    (((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
      processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6) ∗
    ((cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
        cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
        memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
        sp550P2V1RemAt sp) ∗
      (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xd0#64) ↦₆₄ m.spkId.zeroExtend 64) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      spMidGapsAt sp ∗
      ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
      ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x538#64) 24) ∗
    ((cliPollSessKitPlaced A_s y.g.F scopeKit y.g.peer (cliKitStk B)).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B)).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B)).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B)).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId (pmOfE m i).baseKey (cliKitStk B)).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A_s (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A_s y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtExt A_s y.g.msgG y.g.msgA m i) ∗
    ((memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39) ∗
      tokenInitPlacedAt ∗
      sessionStateAt A_s (y.fut + 0xf8#64) G_bob st_bob ∗
      A_s.pool ∗
      stackAt sp chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ i.messageVersion.zeroExtend 32) ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      protocolAddressAt A_s y.g.peer y.g.peerA ∗
      protocolAddressAt A_s y.g.me y.g.meA ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x448#64) 240 ∗
      prevVecAt A_s (y.fut + 0xe0#64) prevCap' prevPtr' [encSession (clearPending sess)] ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      memRegion y.out 48 ∗
      memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x370#64) 36 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
    by sep_frame) ?_
  have hcoro' :
      ((y.fut + 0x298#64) ↦₆₄ ((opkOptTag32 m.opkId).zeroExtend 64 ||| (w.opkWord.zeroExtend 64 <<< 32))) ∗
      processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (y.fut + 0x398#64) 96 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x488#64) 8 ∗ memRegion (y.fut + 0x4b0#64) 65 ∗
      memRegion (y.fut + 0x4f3#64) 5 ∗
      p2CoroScratchTailAt y.fut ∗ memRegion (y.fut + 0x782#64) 6 ⊢
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) := by
    refine Entails.trans (sepConj_mono_left hopkSlot) ?_
    exact Entails.trans (by sep_frame) hcoro
  have hstk' :
      (cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
        cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
        memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
        sp550P2V1RemAt sp) ∗
      (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xd0#64) ↦₆₄ m.spkId.zeroExtend 64) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      spMidGapsAt sp ∗
      ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
      ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x538#64) 24 ⊢
      genP3SpillAll sp ∗ memRegion (sp + 0x3e0#64) 104 ∗
      memRegion (sp + 0xa90#64) 344 ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA := by
    rw [h550]
    exact Entails.trans (by sep_frame) hstk
  rw [h270]
  refine Entails.trans (sepConj_mono hc (sepConj_mono hcoro'
    (sepConj_mono hstk' (sepConj_mono hstores (sepConj_mono_left hmsgSlices))))) ?_
  sep_frame

/-- Budget-threaded placed Stage P2 Over-path (`Path C`) `+0x1778` normal-exit spatial fold at
explicit cost-model state `st_b` and machine state `s2`, from
`StageP2Sub4PlacedBudget.p2OverOkPostAtPlaced A lim 0#64 ... st_b s0 s2` with
`pathAInnerFramePlaced A.repAlloc`. -/
theorem p2OverOkPost_fold_pathCOver_placed_at {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (st_b : M.σ)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8)))
    (hcanon : CanonSession recG sess)
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    p2OverOkPostAtPlaced A lim 0#64
      (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      st_b s0 s2 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        LsTokenInit ∗
        genP3Pre_placed A lim st_b s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (encSession (clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
          (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
           ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) :=
  p2OverOkPost_fold_pathCOver_placed_alloc (A.atState lim st_b s2) y m i w s0 s2 sp fp rngPtr
    recG G_bob sess st_bob hcanon hmsg hcoins hsub hfp hopk hsp2 hx19_2 hx27_2

/-- Budget-threaded placed Stage P2 Over-path (`Path C`) `+0x1778` normal-exit spatial fold into
`hok`'s precondition in `StageP2PathCOverQpanCliPlacedStmt` (with implicit `{st_b : M.σ}`, matching
`Stage2OverInstPlaced`). -/
theorem p2OverOkPost_fold_pathCOver_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} {st_b : M.σ} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8)))
    (hcanon : CanonSession recG sess)
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    p2OverOkPostAtPlaced A lim 0#64
      (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      st_b s0 s2 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        LsTokenInit ∗
        genP3Pre_placed A lim st_b s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (encSession (clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
          (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
           ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) :=
  p2OverOkPost_fold_pathCOver_placed_at st_b y m i w s0 s2 sp fp rngPtr recG G_bob sess st_bob
    hcanon hmsg hcoins hsub hfp hopk hsp2 hx19_2 hx27_2

/-- `A.atState`-indexed variant of `p2OverOkPost_fold_pathCOver_placed` (`rfl`-aligned with
`Over.p2OverOkPostAtPlaced (A.atState lim st_b s2)`). -/
theorem p2OverOkPost_fold_pathCOver_placed_atState {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} {st_b : M.σ} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8)))
    (hcanon : CanonSession recG sess)
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    let A_s : RustAlloc := A.atState lim st_b s2
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverOkPostAtPlaced A_s 0#64
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        LsTokenInit ∗
        overGenP3Pre_placed A lim st_b s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 A.repAlloc s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (encSession (clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
          (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
           ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
        storesAt A.repAlloc y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) :=
  p2OverOkPost_fold_pathCOver_placed_at st_b y m i w s0 s2 sp fp rngPtr recG G_bob sess st_bob
    hcanon hmsg hcoins hsub hfp hopk hsp2 hx19_2 hx27_2

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlacedBudget
