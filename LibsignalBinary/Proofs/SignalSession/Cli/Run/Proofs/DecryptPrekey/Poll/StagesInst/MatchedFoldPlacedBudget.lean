/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFold
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFoldPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Poll Path B Stage P2 Exit Fold

Generalizes the Stage P2 remote-identity mismatch exit spatial fold (`matched_mismatch_fold_placed`)
to `RustCliAllocBudget M` over `A.repAlloc` and `A.atState lim st s`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFoldPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (IdentityKey PublicKey)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  decryptPrekeyCoroInitAt processPrekeyActive10At processPrekeyPostTrustAt
  decryptPrekeySavedRegsAt
)
open CryptoVerification.LibsignalPublicApiRepr (apiDecResultAt preKeyMsgAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SignalSession.Cli (
  cliSessionVtSym cliIdentityVtSym cliPreKeyVtSym cliSignedPreKeyVtSym cliKyberPreKeyVtSym
)
open CryptoVerification.SignalSession.Cli.MainHops (coinsInstalledPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (dpFutDoneAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  MatchedEntryWords spMidGapsAt coroCopyTail11At processPrekeyInnerRem23At
  preKeyMsgAt_eq_base_idKey_sep signalMessageAt_eq_ver_sep
  preKeyMsgRemBaseIdKeyAt_eq_ver_sep
  signalMessageRestVerAt preKeyMsgRemMatchedAt
  stageP2MatchedMismatchPostPlaced coro_mismatch_fold stack_mismatch_fold
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget (
  DpPollGhostStateBudget dpSlotPollKStatePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget (
  matchedInnerFramePlaced
)

set_option linter.unusedSimpArgs false

/-- Placed Stage P2 mismatch exit spatial fold parameterized by an arbitrary representation
allocator `A : RustAlloc` and budget-threaded poll ghost `y`. -/
theorem matched_mismatch_fold_placed_ext {M : AllocCostModel}
    {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement] (A : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (s0 : State) (sp rngPtr : BitVec 64) (u_b8 : BitVec 32) (w : MatchedEntryWords) :
    stageP2MatchedMismatchPostPlaced A s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
      y.g.peerA (y.g.msgA + 0xc8#64)
      w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
      w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
      w.u_2a8 u_b8 y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
      y.g.msg.baseKey y.g.msg.identityKey
      (matchedInnerFramePlaced A y rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      apiDecResultAt A y.out
        (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      tokenInitPlacedAt ∗
      lsLogOff ∗
      A.pool ∗
      stackAt sp rootStack := by
  dsimp only [stageP2MatchedMismatchPostPlaced, matchedInnerFramePlaced]
  have hcoro := coro_mismatch_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr w.u_298 w.u_2a0 w.u_2a8
  have hstk := stack_mismatch_fold s0 sp y.fut y.cx y.out
    w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
    w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8 u_b8 w.b_3ac
  rw [preKeyMsgAt_eq_base_idKey_sep, signalMessageAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
  refine Entails.trans (show _ ⊢
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
      memRegion (y.fut + 0xe0#64) 368 ∗ cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      ((y.fut + 0x298#64) ↦₆₄ w.u_298) ∗ ((y.fut + 0x2a0#64) ↦₆₄ w.u_2a0) ∗
      ((y.fut + 0x2a8#64) ↦₃₂ w.u_2a8) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
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
      ((sp + 0x80#64) ↦₆₄ w.u_80) ∗ ((sp + 0x88#64) ↦₆₄ w.u_88) ∗ ((sp + 0x90#64) ↦₆₄ w.u_90) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₃₂ u_b8) ∗ memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x270#64) 48 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3a0#64) ↦₆₄ w.u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ w.b_3ac) ∗
      ((sp + 0x3b0#64) ↦₆₄ w.u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ w.u_3b8) ∗ ((sp + 0x3c0#64) ↦₆₄ w.u_3c0) ∗
      ((sp + 0x3c8#64) ↦₆₄ w.u_3c8) ∗ ((sp + 0x3d0#64) ↦₆₄ w.u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ w.u_3d8) ∗
      spMidGapsAt sp ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 ∗
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) ∗
    (apiDecResultAt A y.out
        (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
      ((y.g.msgA + 0x70#64) ↦₈ y.g.msg.message.messageVersion) ∗
      signalMessageRestVerAt A y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      ((y.g.msgA + 0xf0#64) ↦₈ y.g.msg.messageVersion) ∗
      preKeyMsgRemMatchedAt A y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      tokenInitPlacedAt ∗
      lsLogOff ∗
      A.pool ∗
      stackAt sp rootStack) by sep_frame) ?_
  refine Entails.trans (sepConj_mono hcoro (sepConj_mono_left hstk)) ?_
  sep_frame

/-- Budget-threaded placed Stage P2 mismatch exit spatial fold specialized to `A.atState lim st s`
with `matchedInnerFramePlaced A.repAlloc`. -/
theorem matched_mismatch_fold_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop} {B : RunBudgets} {S : RunSem}
    [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (st : M.σ) (s0 s : State) (sp rngPtr : BitVec 64) (u_b8 : BitVec 32)
    (w : MatchedEntryWords) :
    stageP2MatchedMismatchPostPlaced (A.atState lim st s) s0 sp y.fut y.out
      y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
      y.g.peerA (y.g.msgA + 0xc8#64)
      w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
      w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
      w.u_2a8 u_b8 y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
      y.g.msg.baseKey y.g.msg.identityKey
      (matchedInnerFramePlaced A.repAlloc y rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      apiDecResultAt A.repAlloc y.out
        (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A.repAlloc y.g.peer y.g.peerA ∗
      protocolAddressAt A.repAlloc y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      tokenInitPlacedAt ∗
      lsLogOff ∗
      A.pool lim st s ∗
      stackAt sp rootStack := by
  have hinner : matchedInnerFramePlaced A.repAlloc y rngPtr sp =
      matchedInnerFramePlaced (A.atState lim st s) y rngPtr sp := by
    dsimp only [matchedInnerFramePlaced, signalMessageRestVerAt, preKeyMsgRemMatchedAt,
      protocolAddressAt, RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
    cases y.g.msg.message.addresses <;> cases y.g.msg.kyberPayload <;> rfl
  have hmsg : preKeyMsgAt (A.atState lim st s) y.g.msgG y.g.msgA y.g.msg =
      preKeyMsgAt A.repAlloc y.g.msgG y.g.msgA y.g.msg := by
    dsimp only [preKeyMsgAt, CryptoVerification.LibsignalTripleRatchetRepr.signalMessageAt,
      CryptoVerification.LibsignalTripleRatchetRepr.optBoxU8At,
      RustCliAllocBudget.atState, RustCliAllocBudget.repAlloc]
    cases y.g.msg.message.addresses <;> cases y.g.msg.kyberPayload <;> rfl
  rw [hinner]
  refine Entails.trans (matched_mismatch_fold_placed_ext (A.atState lim st s) y s0 sp rngPtr u_b8 w) ?_
  rw [hmsg]
  exact Entails.refl _

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFoldPlacedBudget
