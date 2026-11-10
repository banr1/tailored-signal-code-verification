/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Folds
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFoldPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFoldPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv

/-!
# Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Entry and Error-Exit Folds

Defines `pathAInnerFramePlaced`, `stageP2PreAtPlaced`, and `p2ErrFrameAtPlaced` and proves
`stageP2_entry_unpack_pathA_placed` and `p2ErrFrame_fold_pathA_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
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
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst

/-- Placed spatial frame preserved untouched across `stageP2_v1_kits` on Path A. -/
def pathAInnerFramePlaced {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
    (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
  dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
    (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
  memRegion (y.fut + 0x280#64) 24 ∗ memRegion (y.fut + 0x2ac#64) 8 ∗
  memRegion (y.fut + 0x2b4#64) 12 ∗ memRegion (y.fut + 0x2c1#64) 7 ∗
  memRegion (y.fut + 0x391#64) 7 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
  memRegion (y.fut + 0x782#64) 6 ∗
  (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x279#64) 39 ∗
  memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
  memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
  spMidGapsAt sp ∗ sp550P2V1RemAt sp ∗
  signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
  pathAMsgRemInnerAt y.g.msgG y.g.msgA m i ∗
  coinsInstalledPlaced y.g.coinsP y.g.coins ∗
  SpqrV1.GF.Mul2U16.tokenInitPlacedAt

/-- Placed spatial precondition at `+0x0868` for `stageP2_v1_kits` (Path A fresh Bob session). -/
def stageP2PreAtPlaced (A : RustAlloc) [LibsignalPlacement]
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64)
    (ikit : IdentityStoreSpec A 0#64)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk ∗
  kpkKit.storeAt kyberStorePtr stKpk ∗
  pkKit.storeAt preKeyStorePtr stPk ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
  memRegion (coroPtr + 0x100#64) 336 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  memRegion (coroPtr + 0x398#64) 96 ∗
  cells (coroPtr + 0x3f8#64) 6 ∗
  cells (coroPtr + 0x468#64) 4 ∗
  ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
  ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
  memRegion (coroPtr + 0x4b1#64) 64 ∗
  ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2MsgFieldsAt msgPtr ctBufPtr hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ u_90) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
  ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3a0#64) 8 ∗
  memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b0#64) 48 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  cells (sp + 0x930#64) 8 ∗
  memRegion (sp + 0xa90#64) 288 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  FromRecordCallees.lsLogOff ∗
  A.pool ∗
  stackAt sp stk ∗
  Frame

/-- Placed entry spatial unpack from `StageP2PathAQpanCliStmt` into `stageP2PreAtPlaced... pathAInnerFramePlaced`. -/
theorem stageP2_entry_unpack_pathA_placed {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    FromRecordCallees.lsLogOff ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords,
        ⌜∀ id : BitVec 32, m.opkId = some id → w.opkWord = id⌝ ∗
        stageP2PreAtPlaced E2E.HooksE.A0
          (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B)
          (pathAInnerFramePlaced y m i rngPtr sp) := by
  rw [hmsg]
  dsimp only [p1LoadedRecordAt, stageP2PostP1At]
  have hdrEq : ResponderClosure.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) =
      ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) := rfl
  rw [hdrEq, coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA (pmOfE m i) ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    (ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) ∗
      memRegion (y.fut + 0x100#64) 336 ∗
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
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion y.out 48 ∗ E2E.HooksE.A0.pool ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      coinsInstalledPlaced y.g.coinsP y.g.coins ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA y.g.msgG y.g.msgA m i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hopkWord => ?_
  have hdecOk' : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val (pmOfE m i) :=
    hmsg ▸ hdecOk
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := E2E.HooksE.A0) 0#64
    (cliKitStk B) y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdecOk')
    (cliIdInv_opened_peer hFok)
    (cliPkInv_opened hdecOk' opkWord)
    (cliSpkInv_opened hdecOk' m.spkId)
    (cliKpkInvFull_opened hdecOk' m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  refine Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
    (Entails.pure_right hopkWord ?_)
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt, stageP2PreAtPlaced, pathAInnerFramePlaced]
    rw [hdrEq]
    ac_rfl)

/-- Placed common coroutine, stack, message, address, and allocator spatial frame delivered uniformly
at `s0.readReg64.x30` on all 6 Stage-P2 error exits. -/
def p2ErrFrameAtPlaced (A : RustAlloc) [LibsignalPlacement] (s0 : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  memRegion (coroPtr + 0x398#64) 96 ∗
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt ∗
  memRegion (coroPtr + 0x488#64) 8 ∗
  memRegion (coroPtr + 0x4b0#64) 65 ∗
  ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2MsgFieldsAt msgPtr ctBufPtr hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  memRegion (sp + 0x80#64) 88 ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3a0#64) 8 ∗
  memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b0#64) 48 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  cells (sp + 0x930#64) 8 ∗
  memRegion (sp + 0xa90#64) 288 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  FromRecordCallees.lsLogOff ∗
  A.pool ∗
  stackAt sp stk ∗
  Frame

set_option maxHeartbeats 800000 in
/-- Placed full Stage P2 error-exit spatial fold into `StageP2PathAErr`'s postcondition. -/
theorem p2ErrFrame_fold_pathA_placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hmsg : y.g.msg = pmOfE m i)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    (decResAt E2E.HooksE.A0 y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId (cliKitStk B)).storeAt
      (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).identityAt
      y.g.stores StoresGhost.opened.identity ∗
    p2ErrFrameAtPlaced E2E.HooksE.A0 s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFramePlaced y m i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt E2E.HooksE.A0 y.out (.error err) ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap := by
  rw [hmsg]
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := E2E.HooksE.A0) 0#64
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores StoresGhost.opened
  have hmsgFold :
      p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAt y.g.msgG y.g.msgA m i ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA (pmOfE m i) := by
    refine Entails.trans (p2MsgFields_reassemble_slices y.g.msgG y.g.msgA m i w.opkWord hopk) ?_
    rw [preKeyMsgAt_eq_base_idKey_sep]
    exact Entails.of_eq (by ac_rfl)
  have hcoro := p2_coro_err_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hstk := p2_stack_err_fold sp fp s0 hfp
  have hany : coinsInstalledPlaced y.g.coinsP y.g.coins ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ anyHeap ⊢ anyHeap :=
    entails_anyHeap _
  dsimp only [p2ErrFrameAtPlaced, pathAInnerFramePlaced]
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
      memRegion (y.fut + 0xe0#64) 368 ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      memRegion (y.fut + 0x298#64) 20 ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
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
    ((sp ↦₆₄ 0#64) ∗
      memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0x80#64) 88 ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3a0#64) 8 ∗ memRegion (sp + 0x3ac#64) 1 ∗
      memRegion (sp + 0x3b0#64) 48 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      spMidGapsAt sp ∗
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
      cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
      memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
      sp550P2V1RemAt sp ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) ∗
    decResAt E2E.HooksE.A0 y.out (.error err) ∗
    cliPollStoresKitsAt E2E.HooksE.A0 0#64 y.g.F Slots.scopeKit y.g.peer
      w.opkWord m.spkId m.kpkId (pmOfE m i).baseKey (cliKitStk B) y.g.stores StoresGhost.opened ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAt y.g.msgG y.g.msgA m i) ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    FromRecordCallees.lsLogOff ∗
    E2E.HooksE.A0.pool ∗
    stackAt sp (dpClosSubStack B) ∗
    (coinsInstalledPlaced y.g.coinsP y.g.coins ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ anyHeap)
    by exact Entails.of_eq (by dsimp only [cliPollStoresKitsAt]; ac_rfl)) ?_
  exact sepConj_mono hcoro (sepConj_mono hstk (sepConj_mono_right
    (sepConj_mono hstores (sepConj_mono hmsgFold
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hany)))))))))

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
