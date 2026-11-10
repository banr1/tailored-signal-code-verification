/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFoldPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFold
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Path B Stage P3 Match Continuation Fold

Generalizes the Stage P3 match-continuation spatial fold (`matched_match_fold_placed`) at
`dpPollEntryPlaced + 0x1778#64` to `RustCliAllocBudget M` over `A.repAlloc` and
`A.atState lim st s2`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost protocolAddressAt sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure
  (decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyActive10At processPrekeyPostTrustAt)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SignalSession.Cli
  (cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym cliSignedPreKeyVtSym)
open CryptoVerification.SignalSession.Cli.MainHops (coinsInstalledPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (coroCopyTail11At coro_match_fold genP3CallFrame_placed genP3PrePlaced genP3Pre_placed
   preKeyMsgRemBaseIdKeyAt preKeyMsgRemBaseIdKeyAt_eq_ver_sep preKeyMsgRemMatchedAt
   prevSessionsEmptyAt processPrekeyInnerRem23At signalMessageAt_eq_ver_sep
   signalMessageRestVerAt spMidGapsAt stackAt_root_eq_chainClone stack_match_fold
   stageP2MatchedMatchPrePlaced stageP3CoroFrameAt stageP3StackFrameAt
   stageP3Sub5ExtraPrePrevEmpty)
open CryptoVerification.SignalSession.Cli.Slots (coinsInstalledPlaced_entails_coinsAtPlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  renaming genP3Pre_placed → budgetGenP3Pre_placed
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget
  (matchedInnerFramePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpSlotPollKStatePlaced)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- `MatchedMatchFoldPlaced.genP3PrePlaced` and `ClosureStageP2DefsPlaced.genP3Pre_placed`
are definitionally equal for every `A : RustAlloc`. -/
theorem genP3PrePlaced_eq_genP3Pre_placed (A : RustAlloc) [LibsignalPlacement] :
    @genP3PrePlaced A _ = @genP3Pre_placed A _ := rfl

/-- Placed Stage P3 match continuation spatial fold parameterized by an arbitrary representation
allocator `A : RustAlloc` and budget-threaded poll ghost `y`. -/
theorem matched_match_fold_placed_ext {M : AllocCostModel}
    {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement] (A : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (sess : Session (List (BitVec 8))) (s0 s2 : State)
    (sp rngPtr v_d0 : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (F_frame : SepProp)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    stageP2MatchedMatchPrePlaced A s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
      y.g.peerA (y.g.msgA + 0xc8#64) v_d0
      opkHi kyberPreKeyId signedPreKeyId
      y.g.msg.messageVersion y.g.msg.message.messageVersion 0#8
      y.g.msg.baseKey y.g.msg.identityKey g recG sess.state
      (matchedInnerFramePlaced A y rngPtr sp ∗ F_frame) ⊢
      (tokenInitPlacedAt ∗
        genP3Pre_placed A s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        stageP3Sub5ExtraPrePrevEmpty A s0 s2 y.fut y.out 8#64 g 0#8 ∗
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
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A y.g.msgG y.g.msgA y.g.msg)) ∗ F_frame := by
  unfold genP3Pre_placed
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _)))))
  dsimp only [stageP2MatchedMatchPrePlaced, matchedInnerFramePlaced, genP3CallFrame_placed]
  unfold stageP3Sub5ExtraPrePrevEmpty
  have hprev_eq :
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.prevSessionsEmptyAt A y.fut g =
      prevSessionsEmptyAt A y.fut g := rfl
  rw [hsp2, hprev_eq, stackAt_root_eq_chainClone sp,
      signalMessageAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
  have hcoro := coro_match_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr v_d0 opkHi kyberPreKeyId signedPreKeyId
  have hstk := stack_match_fold sp y.fut y.g.msgA y.g.peerA v_d0
  have hc := coinsInstalledPlaced_entails_coinsAtPlaced y.g.coinsP y.g.coins hcoins
  refine Entails.trans (show _ ⊢
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
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
      ((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi) ∗
      ((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗ ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
      ((y.fut + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x3a8#64) 80 ∗ memRegion (y.fut + 0x488#64) 8 ∗
      memRegion (y.fut + 0x4b0#64) 65 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
      memRegion (y.fut + 0x4f8#64) 736) ∗
    ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      spMidGapsAt sp ∗
      ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
      ((sp + 0x3b8#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x538#64) 24 ∗
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136) ∗
    (tokenInitPlacedAt ∗
      sessionStateAt A (y.fut + 0xf8#64) recG sess.state ∗
      A.pool ∗
      stackAt sp chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ y.g.msg.message.messageVersion.zeroExtend 32) ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      ((y.g.msgA + 0x70#64) ↦₈ y.g.msg.message.messageVersion) ∗
      signalMessageRestVerAt A y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      memRegion (sp + 0x270#64) 48 ∗
      lsLogOff ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x448#64) 240 ∗
      prevSessionsEmptyAt A y.fut g ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      memRegion y.out 48 ∗
      memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x370#64) 36 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xf0#64) ↦₈ y.g.msg.messageVersion) ∗
      preKeyMsgRemMatchedAt A y.g.msgG y.g.msgA y.g.msg ∗
      F_frame) by sep_frame) ?_
  refine Entails.trans (sepConj_mono hc (sepConj_mono hcoro (sepConj_mono_left hstk))) ?_
  sep_frame

/-- Budget-threaded placed Stage P3 match continuation spatial fold specialized to
`A.atState lim st s2` (`ClosureStageP2DefsPlacedBudget.genP3Pre_placed A lim st`) with
`matchedInnerFramePlaced A.repAlloc`. -/
theorem matched_match_fold_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st : M.σ) (sess : Session (List (BitVec 8))) (s0 s2 : State)
    (sp rngPtr v_d0 : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (F_frame : SepProp)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    stageP2MatchedMatchPrePlaced (A.atState lim st s2) s0 sp y.fut y.out
      y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
      y.g.peerA (y.g.msgA + 0xc8#64) v_d0
      opkHi kyberPreKeyId signedPreKeyId
      y.g.msg.messageVersion y.g.msg.message.messageVersion 0#8
      y.g.msg.baseKey y.g.msg.identityKey g recG sess.state
      (matchedInnerFramePlaced A.repAlloc y rngPtr sp ∗ F_frame) ⊢
      (tokenInitPlacedAt ∗
        budgetGenP3Pre_placed A lim st s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
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
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg)) ∗ F_frame := by
  have hinner : matchedInnerFramePlaced A.repAlloc y rngPtr sp =
      matchedInnerFramePlaced (A.atState lim st s2) y rngPtr sp := by
    dsimp only [matchedInnerFramePlaced, signalMessageRestVerAt, preKeyMsgRemMatchedAt,
      protocolAddressAt, RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
    cases y.g.msg.message.addresses <;> cases y.g.msg.kyberPayload <;> rfl
  have hrem : preKeyMsgRemBaseIdKeyAt (A.atState lim st s2) y.g.msgG y.g.msgA y.g.msg =
      preKeyMsgRemBaseIdKeyAt A.repAlloc y.g.msgG y.g.msgA y.g.msg := by
    rw [preKeyMsgRemBaseIdKeyAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
    dsimp only [preKeyMsgRemMatchedAt, RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
    cases y.g.msg.kyberPayload <;> rfl
  have hextra :
      stageP3Sub5ExtraPrePrevEmpty (A.atState lim st s2) s0 s2 y.fut y.out 8#64 g 0#8 =
      stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s2 y.fut y.out 8#64 g 0#8 := rfl
  rw [hinner]
  refine Entails.trans
    (matched_match_fold_placed_ext (A.atState lim st s2) y sess s0 s2 sp rngPtr v_d0 g recG
      opkHi kyberPreKeyId signedPreKeyId F_frame hcoins hsp2 hx19_2 hx27_2) ?_
  rw [hrem, hextra]
  exact Entails.refl _

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlacedBudget
