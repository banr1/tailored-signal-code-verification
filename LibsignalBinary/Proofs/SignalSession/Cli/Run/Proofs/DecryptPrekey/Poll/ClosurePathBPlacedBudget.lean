/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Matched-Session Path B Spatial Bridges

Proves budget-threaded Stage P3 error exit fold `stageP3ErrPrevEmpty_entails_exit_placed` and
Stage P3 -> Stage P4 split/fold (`stageP3MidPrevEmpty_eq_p4_placed`,
`stageP4MatchedExit_entails_exit_placed`) over `A.repAlloc` and `A.pool`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp Bytes
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose hiding
  Bytes dpSlotPollKStatePlaced slotFramePlaced decPkSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs.Poll hiding
  cliPollStageP4MatchedStack_placed_le_subStack
  stageP3ErrPrevEmpty_entails_exit_placed
  pathBP4RemAtPlaced
  stageP3MidPrevEmpty_eq_p4_placed
  stageP4MatchedExit_entails_exit_placed
  genP3Pre_placed genP3CallFrame_placed genP3S5PostFrame_placed
  stageP3DispatchOkMid_placed stageP3ErrPost_placed
  stageP3DispatchOkMidPrevEmpty_placed stageP3ErrPostPrevEmpty_placed
  stageP4MatchedSharedPlaced stageP4MatchedPrePlaced stageP4MatchedExitAtPlaced
  StageP4MatchedBranchPlaced StageP4MatchedPlacedStmt
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget (
  genP3S5PostFrame_placed
  stageP3DispatchOkMidPrevEmpty_placed
  stageP3ErrPostPrevEmpty_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  stageP4MatchedSharedPlaced
  stageP4MatchedPrePlaced
  stageP4MatchedExitAtPlaced
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

abbrev cliPollStageP4MatchedStack_placed_le_subStack :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollStageP4MatchedStack_placed_le_subStack

/-! ## 1. Spatial Fold for Stage P3 `Err` / `verNe` Exits on Path B -/

set_option maxHeartbeats 800000 in
theorem stageP3ErrPrevEmpty_entails_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s2 sf : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (msgVer opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (e : SignalProtocolError) (err : ApiError AddrVal Unit)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (_hsp_root : rootStack ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg) :
    let sp := s0.sp - 0xcd0#64
    (((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmpty_placed A lim st_b s0 s2 sf y.fut y.out e ∗
      genP3S5PostFrame_placed A.repAlloc sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost) ∗
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
    preKeyMsgRem ⊢
    decResAt A.repAlloc y.out (.error err) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim st_b sf ∗
      (LsTokenInit ∗ coinsPost) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp rootStack ∗
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let A_s : RustAlloc := A.atState lim st_b sf
  unfold stageP3ErrPostPrevEmpty_placed
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3ErrPostPrevEmpty_placed
    genP3S5PostFrame_placed
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
    stageP3CoroFrameAt stageP3StackFrameAt
  have hrec : recordResultAt A_s = recordResultAt A.repAlloc := rfl
  rw [hs2_sp, hrec, RustCliAllocBudget.atState_pool]
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack =
      stackAt sp rootStack :=
    (stackAt_root_sub_eq sp (by decide)).symm
  have hdec := recordResultAt_err_entails_decResAt A.repAlloc y.out
    (SessionState.recordError .preKey e) err
  have h298 := coro_298_words32_entails_memRegion8 y.fut 2#32 opkHi
  have h2a0 := coro_2a0_words32_entails_memRegion8 y.fut kyberPreKeyId signedPreKeyId
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstack := stageP3Err_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      recordResultAt A.repAlloc y.out (.error (SessionState.recordError .preKey e)) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim st_b sf ∗
      (LsTokenInit ∗ coinsPost) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        memRegion (y.fut + 0xe0#64) 368 ∗
        memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗
        (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi)) ∗
        (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗ ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId)) ∗
        memRegion (y.fut + 0x2a8#64) 4 ∗
        (memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12) ∗
        ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        (memRegion (y.fut + 0x2c8#64) 16 ∗ memRegion (y.fut + 0x2d8#64) 184) ∗
        memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗
        coroPostP2UnusedAt y.fut) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack) ∗
      ((sp ↦₆₄ 0#64) ∗
        genP3S5SpillRem sp ∗
        memRegion (sp + 0x930#64) 48 ∗
        ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
        ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
        ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
        spLowGapsAt sp ∗
        ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
        ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
        ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
        ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
        memRegion (sp + 0xbc#64) 4 ∗
        ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
        ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        memRegion (sp + 0xd8#64) 376 ∗
        memRegion (sp + 0x250#64) 20 ∗
        memRegion (sp + 0x264#64) 12 ∗
        memRegion (sp + 0x270#64) 48 ∗
        memRegion (sp + 0x2a0#64) 16 ∗
        memRegion (sp + 0x2b0#64) 192 ∗
        memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x394#64) 12 ∗
        ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
        memRegion (sp + 0x3a8#64) 4 ∗
        ((sp + 0x3ac#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x3ad#64) 27 ∗
        (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((sp + 0x3d8#64) ↦₆₄ errsLen)) ∗
        memRegion (sp + 0x3e0#64) 344 ∗
        memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗
        spHighGapsAt sp ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by
          dsimp only [sp] at *
          generalize
            (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
              ((s0.sp - 0xcd0#64 + 0x3c8#64) ↦₆₄ errsCap) ∗
              ((s0.sp - 0xcd0#64 + 0x3d0#64) ↦₆₄ errsPtr) ∗
              ((s0.sp - 0xcd0#64 + 0x3d8#64) ↦₆₄ errsLen)) = Perrs
          sep_frame)) ?_
  rw [← coro_2ac_20_eq_8_12 y.fut, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  refine sepConj_mono hdec (sepConj_mono_right (sepConj_mono_right (sepConj_mono hmsg_fold
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono ?_ (sepConj_mono_right ?_))))))))
  · refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) hcoro
  · exact Entails.trans (sepConj_mono_left hsp0) hstack

/-! ## 2. Spatial Split & Exit Fold for Stage P4 (`+0x34dc → x30`) on Path B -/

/-- Caller resources framed across budget-threaded `StageP4MatchedPlacedStmt`
(`+0x34dc → s0.readReg64.x30`), parameterized by `A_r : RustAlloc` (`A.repAlloc`). -/
def pathBP4RemAtPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    (A_r : RustAlloc) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (sp rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (msgVer : BitVec 32) (preKeyMsgRem coinsPost : SepProp) : SepProp :=
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyRemMatchedP4At y.fut y.g.meA
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  memRegion (y.fut + 0x250#64) 48 ∗
  memRegion (y.fut + 0x2a8#64) 4 ∗
  memRegion (y.fut + 0x2b4#64) 12 ∗
  memRegion (y.fut + 0x2d8#64) 184 ∗
  memRegion (y.fut + 0x390#64) 1 ∗
  memRegion (y.fut + 0x398#64) 16 ∗
  memRegion (y.fut + 0x428#64) 64 ∗
  memRegion (y.fut + 0x468#64) 40 ∗
  memRegion (y.fut + 0x490#64) 32 ∗
  memRegion (y.fut + 0x4f2#64) 1 ∗
  coroPostP2UnusedAt y.fut ∗
  (sp ↦₆₄ 0#64) ∗
  genP3S5SpillRem sp ∗
  memRegion (sp + 0x930#64) 48 ∗
  ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
  spLowGapsAt sp ∗
  ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
  ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
  memRegion (sp + 0xbc#64) 4 ∗
  ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
  ((sp + 0xc8#64) ↦₆₄ y.out) ∗
  memRegion (sp + 0xd8#64) 376 ∗
  memRegion (sp + 0x264#64) 12 ∗
  memRegion (sp + 0x2a0#64) 16 ∗
  memRegion (sp + 0x2e0#64) 36 ∗
  memRegion (sp + 0x310#64) 36 ∗
  sp2b0GapsAt sp ∗
  memRegion (sp + 0x394#64) 12 ∗
  ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
  memRegion (sp + 0x3a8#64) 4 ∗
  ((sp + 0x3ac#64) ↦₈ 3#8) ∗
  memRegion (sp + 0x3ad#64) 27 ∗
  memRegion (sp + 0x410#64) 296 ∗
  memRegion (sp + 0x538#64) 24 ∗
  memRegion (sp + 0xa90#64) 344 ∗
  spHighGapsAt sp ∗
  protocolAddressAt A_r y.g.me y.g.meA ∗
  signalMessageAt A_r whisperG whisperMsgPtr y.g.msg.message ∗
  preKeyMsgRem ∗
  LsTokenInit ∗
  coinsPost ∗
  memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
    (dpClosSubStack B - stageP4MatchedCallStack
      (cliPollSessKitPlaced A_r y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
      (cliPollIdKitPlaced A_r y.g.F y.g.peer (cliKitStk B)))

set_option maxHeartbeats 800000 in
theorem stageP3MidPrevEmpty_eq_p4_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s2 s' : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (msgVer opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8))
    (g : RecordGhost) (G' : SessionGhost) (st' : SessionState (List (BitVec 8)))
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    (stageP3DispatchOkMidPrevEmpty_placed A lim st_b s0 s2 s' y.fut y.out 8#64
        ptCap ptPtr g pt 0#8 G' st' ∗
      genP3S5PostFrame_placed A.repAlloc sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost) ∗
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
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) =
    stageP4MatchedPrePlaced A lim st_b kit ikit s0 s' y.fut y.g.msgA y.out y.g.peerA
      (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
      y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
      g G' st' ∗
    pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG msgVer
      preKeyMsgRem coinsPost := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let A_s : RustAlloc := A.atState lim st_b s'
  have hss_vt :
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hid_vt :
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hstk1 :
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack =
      stackAt sp rootStack :=
    (stackAt_root_sub_eq sp (by decide)).symm
  have hstk2 :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        stackAt sp rootStack =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub).symm
  have hstk3 := stackAt_subStack_sub_eq sp B
    (cliPollStageP4MatchedStack_placed_le_subStack A.repAlloc y.g.F Slots.scopeKit y.g.peer B)
    hsp_sub
  have hstk_swap :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4MatchedCallStack
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))) ∗
        stackAt sp (stageP4MatchedCallStack
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))) := by
    rw [hstk1, hstk2, hstk3]
  unfold stageP3DispatchOkMidPrevEmpty_placed
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP3DispatchOkMidPrevEmpty_placed
    genP3S5PostFrame_placed
    CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3S5PostFrame_placed
    stageP3CoroFrameAt stageP3StackFrameAt
    stageP4MatchedPrePlaced stageP4MatchedSharedPlaced pathBP4RemAtPlaced
  have hlive : A_s.live = A.repAlloc.live := rfl
  have hssAt : sessionStateAt A_s = sessionStateAt A.repAlloc := rfl
  have hprevAt : prevSessionsEmptyAt A_s = prevSessionsEmptyAt A.repAlloc := rfl
  rw [hs2_sp, hs'_sp, hlive, hssAt, hprevAt, RustCliAllocBudget.atState_pool,
      coroCopy_eq_matched_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr,
      sp_2b0_192_split sp, sp_3e0_344_eq_48_296 sp, hss_vt, hid_vt]
  trans (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack)) ∗
    (((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗
      ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗
      ((y.fut + 0x90#64) ↦₆₄ (lsρ cliSessionVtSym)) ∗
      ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗
      ((y.fut + 0xa0#64) ↦₆₄ (lsρ cliIdentityVtSym)) ∗
      ((y.fut + 0xb8#64) ↦₆₄ (y.g.stores + 0x50#64)) ∗
      ((y.fut + 0xc0#64) ↦₆₄ (lsρ cliSignedPreKeyVtSym)) ∗
      ((y.fut + 0x298#64) ↦₃₂ 2#32) ∗
      ((y.fut + 0x29c#64) ↦₃₂ opkHi) ∗
      ((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
      ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗
      memRegion (y.fut + 0x2c8#64) 16 ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0x250#64) 20 ∗
      ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((sp + 0x278#64) ↦₆₄ ptCap) ∗
      ((sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
      memRegion (sp + 0x290#64) 16 ∗
      memRegion (sp + 0x2b0#64) 36 ∗
      memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x3e0#64) 48 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim st_b s' ∗
      prevSessionsEmptyAt A.repAlloc y.fut g ∗
      sessionStateAt A.repAlloc (y.fut + 0xf8#64) G' st' ∗
      memRegion (y.fut + 0x280#64) 24 ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A.repAlloc.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion y.out 48 ∗
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B)).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym)
        y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      coroCopyRemMatchedP4At y.fut y.g.meA
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 0x250#64) 48 ∗
      memRegion (y.fut + 0x2a8#64) 4 ∗
      memRegion (y.fut + 0x2b4#64) 12 ∗
      memRegion (y.fut + 0x2d8#64) 184 ∗
      memRegion (y.fut + 0x390#64) 1 ∗
      memRegion (y.fut + 0x398#64) 16 ∗
      memRegion (y.fut + 0x428#64) 64 ∗
      memRegion (y.fut + 0x468#64) 40 ∗
      memRegion (y.fut + 0x490#64) 32 ∗
      memRegion (y.fut + 0x4f2#64) 1 ∗
      coroPostP2UnusedAt y.fut ∗
      (sp ↦₆₄ 0#64) ∗
      genP3S5SpillRem sp ∗
      memRegion (sp + 0x930#64) 48 ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      spLowGapsAt sp ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      memRegion (sp + 0xd8#64) 376 ∗
      memRegion (sp + 0x264#64) 12 ∗
      memRegion (sp + 0x2a0#64) 16 ∗
      memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗
      sp2b0GapsAt sp ∗
      memRegion (sp + 0x394#64) 12 ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0x3a8#64) 4 ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      memRegion (sp + 0x3ad#64) 27 ∗
      memRegion (sp + 0x410#64) 296 ∗
      memRegion (sp + 0x538#64) 24 ∗
      memRegion (sp + 0xa90#64) 344 ∗
      spHighGapsAt sp ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
      preKeyMsgRem ∗
      LsTokenInit ∗
      coinsPost)
  · sep_frame
  · rw [hstk_swap]; sep_frame

set_option maxHeartbeats 800000 in
theorem stageP4MatchedExit_entails_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stf : M.σ)
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (s0 s' sf : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (msgVer opkHi kyberPreKeyId signedPreKeyId pid kid : BitVec 32)
    (pt : List (BitVec 8))
    (sstf : DirGhost) (istf : IdGhost) (g' : StoresGhost)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sstf)
    (hid : g'.identity = istf)
    (hot : g'.oneTime = StoresGhost.opened.oneTime)
    (hspk : g'.signed = StoresGhost.opened.signed)
    (hkpk : g'.kyber = StoresGhost.opened.kyber)
    (hpub : g'.pub = StoresGhost.opened.pub) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced A.repAlloc y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId σ
    let kpkKit := cliPollKpkKitPlaced A.repAlloc y.g.F kid y.g.msg.signedPreKeyId y.g.msg.baseKey σ
    stageP4MatchedExitAtPlaced A lim stf kit ikit s0 s' sf y.fut y.g.msgA y.g.peerA
      (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
      (vecResultAt A.repAlloc y.out (.ok pt)) pt
      y.g.peer y.g.msg.identityKey sstf istf ∗
    pathBP4RemAtPlaced A.repAlloc B y sp rngPtr whisperMsgPtr whisperG msgVer
      preKeyMsgRem coinsPost ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
    decResAt A.repAlloc y.out (.ok pt) ∗
      storesAt A.repAlloc y.g.stores g' ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim stf sf ∗
      (LsTokenInit ∗ coinsPost) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  unfold stageP4MatchedExitAtPlaced stageP4MatchedSharedPlaced pathBP4RemAtPlaced
  rw [hs'_sp]
  have hdec : vecResultAt A.repAlloc y.out (.ok pt) = decResAt A.repAlloc y.out (.ok pt) := rfl
  have hss_vt :
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hid_vt :
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4MatchedCallStack
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)) ∗
      stackAt sp (stageP4MatchedCallStack
        (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)) =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B
      (cliPollStageP4MatchedStack_placed_le_subStack A.repAlloc y.g.F Slots.scopeKit y.g.peer B)
      hsp_sub).symm
  have hstores :
      (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) sstf ∗
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
      (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A.repAlloc y.g.F kid y.g.msg.signedPreKeyId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
      storesAt A.repAlloc y.g.stores g' := by
    rw [← hsess, ← hid, ← hot, ← hspk, ← hkpk, ← hpub]
    exact cliPollStoresKitsAtPlaced_entails_storesAt (A := A.repAlloc) σ y.g.stores g'
  have hcopy_join :=
    (coroCopy_eq_matched_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr).symm
  rw [hss_vt, hid_vt, hdec]
  have h298 := coro_298_words32_entails_memRegion8 y.fut 2#32 opkHi
  have h2a0 := coro_2a0_words32_entails_memRegion8 y.fut kyberPreKeyId signedPreKeyId
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hstack := stageP4Exit_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA
    0xfffffffffffffffe#64 ptCap ptPtr (BitVec.ofNat 64 pt.length) 0#64 8#64 0#64 msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      decResAt A.repAlloc y.out (.ok pt) ∗
      ((cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ).storeAt
          (y.g.stores + 0xf0#64) sstf ∗
        (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
        (cliPollPkKitPlaced A.repAlloc y.g.F pid σ).storeAt
          (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        (cliPollSpkKitPlaced A.repAlloc y.g.F y.g.msg.signedPreKeyId σ).storeAt
          (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
        (cliPollKpkKitPlaced A.repAlloc y.g.F kid y.g.msg.signedPreKeyId y.g.msg.baseKey σ).storeAt
          (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
        dirAt A.repAlloc (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      (signalMessageAt A.repAlloc whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      FromRecordCallees.lsLogOff ∗
      A.pool lim stf sf ∗
      (LsTokenInit ∗ coinsPost) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        ((((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗
          ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
          ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗
          ((y.fut + 0x90#64) ↦₆₄ (lsρ cliSessionVtSym)) ∗
          ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗
          ((y.fut + 0xa0#64) ↦₆₄ (lsρ cliIdentityVtSym)) ∗
          ((y.fut + 0xb8#64) ↦₆₄ (y.g.stores + 0x50#64)) ∗
          ((y.fut + 0xc0#64) ↦₆₄ (lsρ cliSignedPreKeyVtSym))) ∗
          coroCopyRemMatchedP4At y.fut y.g.meA
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr) ∗
        memRegion (y.fut + 0xe0#64) 368 ∗
        memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗
        (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi)) ∗
        (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗ ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId)) ∗
        memRegion (y.fut + 0x2a8#64) 4 ∗
        (memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12) ∗
        ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        (memRegion (y.fut + 0x2c8#64) 16 ∗ memRegion (y.fut + 0x2d8#64) 184) ∗
        memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗
        coroPostP2UnusedAt y.fut) ∗
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
          (dpClosSubStack B - stageP4MatchedCallStack
            (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ)) ∗
        stackAt sp (stageP4MatchedCallStack
          (cliPollSessKitPlaced A.repAlloc y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer σ))) ∗
      ((sp ↦₆₄ 0#64) ∗
        genP3S5SpillRem sp ∗
        memRegion (sp + 0x930#64) 48 ∗
        ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
        ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
        ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
        spLowGapsAt sp ∗
        ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
        ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
        ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
        ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
        memRegion (sp + 0xbc#64) 4 ∗
        ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
        ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        memRegion (sp + 0xd8#64) 376 ∗
        memRegion (sp + 0x250#64) 20 ∗
        memRegion (sp + 0x264#64) 12 ∗
        ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((sp + 0x278#64) ↦₆₄ ptCap) ∗
        ((sp + 0x280#64) ↦₆₄ ptPtr) ∗
        ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (sp + 0x290#64) 16 ∗
        memRegion (sp + 0x2a0#64) 16 ∗
        memRegion (sp + 0x2b0#64) 36 ∗
        memRegion (sp + 0x2e0#64) 36 ∗
        memRegion (sp + 0x310#64) 36 ∗
        memRegion (sp + 0x340#64) 36 ∗
        sp2b0GapsAt sp ∗
        memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x394#64) 12 ∗
        ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
        memRegion (sp + 0x3a8#64) 4 ∗
        ((sp + 0x3ac#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x3ad#64) 27 ∗
        ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
        ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
        ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
        memRegion (sp + 0x3e0#64) 48 ∗
        memRegion (sp + 0x410#64) 296 ∗
        memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗
        spHighGapsAt sp ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by dsimp only [sp, σ] at *; sep_frame)) ?_
  rw [hcopy_join, ← coro_2ac_20_eq_8_12 y.fut, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  refine sepConj_mono_right (sepConj_mono hstores (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono ?_ (sepConj_mono_right ?_)))))))))
  · refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) hcoro
  · exact Entails.trans (sepConj_mono_left hsp0) hstack

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBPlacedBudget
