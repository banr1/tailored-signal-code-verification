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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFold
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Success-Exit Fold

Generalizes the Stage P2 `+0x1778` normal-exit spatial fold (`p2OkPost_fold_pathA_placed`) into
`StageP3GenStepsVRegsPlacedStmt` to `RustCliAllocBudget M` over `A.repAlloc` and
`A.atState lim st_b s2`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (SessionState SignalMessage)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3SpillAll)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (coroOpkIdAtP4 opkOptTag32 p2CoroScratchTailAt p2MsgFieldsAt)
open CryptoVerification.E2E (PreKeyMessageFields)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeyCoroInitAt decryptPrekeySavedRegsAt processPrekeyActive10At processPrekeyPostTrustAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (stageP3Sub5ExtraPre)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost protocolAddressAt sessionStateAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (cliIdentityVtSym cliKyberPreKeyVtSym cliPreKeyVtSym cliSessionVtSym cliSignedPreKeyVtSym dirAt)
open CryptoVerification.SignalSession.Cli.MainHops (coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (LsTokenInit PathAEntryWords cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessKitPlaced cliPollSpkKitPlaced cliPollStoresKitsAt cliPollStoresKitsAt_entails_storesAt coroCopyTail11At dpClosSubStack genP3CallFramePlaced genP3PrePlaced hdrOpkIdBv?_mkPathAHdr mkPathAHdr p2MsgFields_reassemble_slices_ext p2_coro_ok_fold p2_coro_opk_slot_fold pathAMsgRemInnerAtExt pmOfE_fields preKeyMsgRemBaseIdKeyAt processPrekeyInnerRem23At signalMessageRestVerAt sp550P2V1RemAt spHighGapsAt spMidGapsAt sp_3e0_344_eq_104_240 sp_3e0_368_eq_344_24 sp_550_1824_split_genP3 sp_550_1824_split_p2v1 stack_match_fold stageP3CoroFrameAt stageP3StackFrameAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpSlotPollKStatePlaced)

abbrev p2OkPostAtPlaced :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2OkPostAtPlaced

abbrev pathAInnerFramePlaced :=
  @Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced

abbrev pathAInnerFramePlacedExt :=
  @Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced

/-- `genP3PrePlaced` and `ClosureStageP2DefsPlaced.genP3Pre_placed` are definitionally equal. -/
theorem genP3PrePlaced_eq_genP3Pre_placed (A_s : RustAlloc) [LibsignalPlacement] :
    @genP3PrePlaced A_s _ =
      @CryptoVerification.SignalSession.Cli.RunProofs.Poll.genP3Pre_placed A_s _ := rfl

set_option maxHeartbeats 800000 in
/-- `RustAlloc`-polymorphic Stage P2 `+0x1778` normal-exit spatial fold into `genP3PrePlaced A_s`. -/
theorem p2OkPost_fold_pathA_placed_alloc {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (A_s : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    p2OkPostAtPlaced A_s
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A_s y m i rngPtr sp) ⊢
      tokenInitPlacedAt ∗
      genP3PrePlaced A_s s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
        y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        recG st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
      stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
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
      storesAt A_s y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  rw [hmsg]
  have hmsg_inner : (pmOfE m i).message = i := (pmOfE_fields m i).2.2.2.2.2.2.1
  rw [hmsg_inner]
  unfold genP3PrePlaced
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _))))
  dsimp only [p2OkPostAtPlaced, CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2OkPostAtPlaced,
    pathAInnerFramePlaced, Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced]
  unfold genP3CallFramePlaced stageP3Sub5ExtraPre
  have hkpk_or : (m.kpkId.zeroExtend 64 <<< 32) ||| 1#64 = m.kpkId ++ 1#32 := by bv_bits
  rw [hsp2, hdrOpkIdBv?_mkPathAHdr m, hkpk_or]
  have hstkSub : stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone.chainCloneStack) ∗
        stackAt sp CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone.chainCloneStack) := by
    rw [CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4.stackAt_sub_eq sp (dpClosSubStack B) rootStack
          (by unfold rootStack dpClosSubStack; omega)
          (Nat.le_trans hsub (Nat.le_of_lt sp.isLt)),
        CryptoVerification.SignalSession.Cli.RunProofs.Poll.stackAt_root_eq_chainClone sp]
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
  have hc := CryptoVerification.SignalSession.Cli.Slots.coinsInstalledPlaced_entails_coinsAtPlaced y.g.coinsP y.g.coins hcoins
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A_s) 0#64
    (F0 := y.g.F) (Scope := CryptoVerification.SignalSession.Cli.Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened
  dsimp only [cliPollStoresKitsAt] at hstores
  have hmsgSlices := p2MsgFields_reassemble_slices_ext A_s y.g.msgG y.g.msgA m i w.opkWord hopk
  rw [hmsg_inner] at hmsgSlices
  rw [hstkSub, h3e0]
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
    ((cliPollSessKitPlaced A_s y.g.F CryptoVerification.SignalSession.Cli.Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
        (y.g.stores + 0xf0#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions ∗
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B)).identityAt
        y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity ∗
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B)).storeAt
        (y.g.stores + 0xc8#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B)).storeAt
        (y.g.stores + 0x50#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId (pmOfE m i).baseKey (cliKitStk B)).storeAt
        (y.g.stores + 0x78#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber ∗
      dirAt A_s (y.g.stores + 0x118#64) CryptoVerification.SignalSession.Cli.StoresGhost.opened.pub) ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A_s y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtExt A_s y.g.msgG y.g.msgA m i) ∗
    ((memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39) ∗
      tokenInitPlacedAt ∗
      sessionStateAt A_s (y.fut + 0xf8#64) recG st_bob ∗
      A_s.pool ∗
      stackAt sp CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone.chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ i.messageVersion.zeroExtend 32) ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      protocolAddressAt A_s y.g.peer y.g.peerA ∗
      protocolAddressAt A_s y.g.me y.g.meA ∗
      lsLogOff ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone.chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x448#64) 240 ∗
      ((y.fut + 0xe0#64) ↦₆₄ 0#64) ∗
      ((y.fut + 0xe8#64) ↦₆₄ 8#64) ∗
      ((y.fut + 0xf0#64) ↦₆₄ 0#64) ∗
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

/-- Budget-threaded placed Stage P2 `+0x1778` normal-exit spatial fold into `hok`'s precondition
at explicit cost-model state `st_b` and machine state `s2` (`A.atState lim st_b s2`), with
`pathAInnerFramePlaced A.repAlloc`. -/
theorem p2OkPost_fold_pathA_placed_at {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (st_b : M.σ)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    let A_s : RustAlloc := A.atState lim st_b s2
    p2OkPostAtPlaced A_s
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
      LsTokenInit ∗
      ClosureStageP2DefsPlacedBudget.genP3Pre_placed A lim st_b s2.sp (s2.readReg64 .x29)
        y.fut y.cx y.g.peerA y.g.meA
        y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        recG st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
      stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
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
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  dsimp only [pathAInnerFramePlaced]
  rw [← Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced_atState_eq_repAlloc st_b s2 y m i rngPtr sp,
      ← Stage2V1FoldsPlacedBudget.preKeyMsgRemBaseIdKeyAt_atState_eq_repAlloc
          A lim st_b s2 y.g.msgG y.g.msgA y.g.msg]
  have hstores_eq :
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened =
      storesAt (A.atState lim st_b s2) y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened := rfl
  have htok_eq : LsTokenInit = tokenInitPlacedAt := rfl
  have hgen_eq :
      ClosureStageP2DefsPlacedBudget.genP3Pre_placed A lim st_b s2.sp (s2.readReg64 .x29)
        y.fut y.cx y.g.peerA y.g.meA
        y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        recG st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 =
      genP3PrePlaced (A.atState lim st_b s2) s2.sp (s2.readReg64 .x29)
        y.fut y.cx y.g.peerA y.g.meA
        y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        recG st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 := rfl
  rw [hstores_eq, htok_eq, hgen_eq]
  exact p2OkPost_fold_pathA_placed_alloc (A.atState lim st_b s2) y m i w s0 s2 sp fp rngPtr
    recG st_bob hmsg hcoins hsub hfp hopk hsp2 hx19_2 hx27_2

/-- Budget-threaded placed Stage P2 `+0x1778` normal-exit spatial fold into `hok`'s precondition
in `StageP2PathACliPlacedStmt` (with implicit `{st_b : M.σ}`, matching `Stage2V1InstPlaced`). -/
theorem p2OkPost_fold_pathA_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} {st_b : M.σ} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG : SessionGhost) (st_bob : SessionState (List (BitVec 8)))
    (hmsg : y.g.msg = pmOfE m i)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    let A_s : RustAlloc := A.atState lim st_b s2
    p2OkPostAtPlaced A_s
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
      LsTokenInit ∗
      ClosureStageP2DefsPlacedBudget.genP3Pre_placed A lim st_b s2.sp (s2.readReg64 .x29)
        y.fut y.cx y.g.peerA y.g.meA
        y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
        recG st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
      stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
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
      storesAt A.repAlloc y.g.stores CryptoVerification.SignalSession.Cli.StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) :=
  p2OkPost_fold_pathA_placed_at st_b y m i w s0 s2 sp fp rngPtr recG st_bob
    hmsg hcoins hsub hfp hopk hsp2 hx19_2 hx27_2

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlacedBudget
