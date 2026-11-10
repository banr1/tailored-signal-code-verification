/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Poll Matched-Session Path B Spatial Bridges

Spatial exit folds and Stage P3 -> Stage P4 split (`pathBP4RemAtPlaced`) for matched-session
Path B (`opt = some ⟨some sess⟩`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
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
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem cliPollStageP4MatchedStack_placed_le_subStack [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) :
    stageP4MatchedCallStack
      (cliPollSessKitPlaced A F0 Scope peer (cliKitStk B))
      (cliPollIdKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  cliPollStageP4MatchedStack_le_subStack A 0#64 F0 Scope peer B

/-! ## 1. Spatial Fold for Stage P3 `Err` / `verNe` Exits on Path B -/

set_option maxHeartbeats 800000 in
theorem stageP3ErrPrevEmpty_entails_exit_placed [LibsignalPlacement]
    {B : RunBudgets} {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 s2 : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (msgVer opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (e : SignalProtocolError) (err : ApiError AddrVal Unit)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (_hsp_root : rootStack ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) :
    let sp := s0.sp - 0xcd0#64
    (((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmpty_placed E2E.HooksE.A0 s0 s2 y.fut y.out e ∗
      genP3S5PostFrame_placed E2E.HooksE.A0 sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
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
    decResAt E2E.HooksE.A0 y.out (.error err) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      (LsTokenInit ∗ coinsPost) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp rootStack ∗
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  unfold stageP3ErrPostPrevEmpty_placed genP3S5PostFrame_placed stageP3CoroFrameAt stageP3StackFrameAt
  rw [hs2_sp]
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack =
      stackAt sp rootStack :=
    (stackAt_root_sub_eq sp (by decide)).symm
  have hdec := recordResultAt_err_entails_decResAt E2E.HooksE.A0 y.out
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
      recordResultAt E2E.HooksE.A0 y.out (.error (SessionState.recordError .preKey e)) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      (signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
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

/-- Caller resources framed across `StageP4MatchedPlacedStmt` (`+0x34dc → s0.readReg64.x30`). -/
def pathBP4RemAtPlaced [LibsignalPlacement] (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
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
  protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
  signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
  preKeyMsgRem ∗
  LsTokenInit ∗
  coinsPost ∗
  memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
    (dpClosSubStack B - stageP4MatchedCallStack
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)))

set_option maxHeartbeats 800000 in
theorem stageP3MidPrevEmpty_eq_p4_placed [LibsignalPlacement] (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
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
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    (stageP3DispatchOkMidPrevEmpty_placed E2E.HooksE.A0 s0 s2 y.fut y.out 8#64
        ptCap ptPtr g pt 0#8 G' st' ∗
      genP3S5PostFrame_placed E2E.HooksE.A0 sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
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
    stageP4MatchedPrePlaced kit ikit s0 s' y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId 0#8 pt
      y.g.peer y.g.msg.identityKey StoresGhost.opened.sessions StoresGhost.opened.identity
      g G' st' ∗
    pathBP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG msgVer preKeyMsgRem coinsPost := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  have hss_vt :
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hid_vt :
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).id_vt =
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
    (cliPollStageP4MatchedStack_placed_le_subStack E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer B)
    hsp_sub
  have hstk_swap :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4MatchedCallStack
          (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
          (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))) ∗
        stackAt sp (stageP4MatchedCallStack
          (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
          (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))) := by
    rw [hstk1, hstk2, hstk3]
  unfold stageP3DispatchOkMidPrevEmpty_placed genP3S5PostFrame_placed stageP3CoroFrameAt stageP3StackFrameAt
    stageP4MatchedPrePlaced stageP4MatchedSharedPlaced pathBP4RemAtPlaced
  rw [hs2_sp, hs'_sp,
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
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      prevSessionsEmptyAt E2E.HooksE.A0 y.fut g ∗
      sessionStateAt E2E.HooksE.A0 (y.fut + 0xf8#64) G' st' ∗
      memRegion (y.fut + 0x280#64) 24 ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else E2E.HooksE.A0.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion y.out 48 ∗
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
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
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
      preKeyMsgRem ∗
      LsTokenInit ∗
      coinsPost)
  · sep_frame
  · rw [hstk_swap]; sep_frame

set_option maxHeartbeats 800000 in
theorem stageP4MatchedExit_entails_exit_placed [LibsignalPlacement] (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 s' : State)
    (rngPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (msgVer opkHi kyberPreKeyId signedPreKeyId pid kid : BitVec 32)
    (pt : List (BitVec 8))
    (sstf : DirGhost) (istf : IdGhost) (g' : StoresGhost)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sstf)
    (hid : g'.identity = istf)
    (hot : g'.oneTime = StoresGhost.opened.oneTime)
    (hspk : g'.signed = StoresGhost.opened.signed)
    (hkpk : g'.kyber = StoresGhost.opened.kyber)
    (hpub : g'.pub = StoresGhost.opened.pub) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F y.g.msg.signedPreKeyId σ
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid y.g.msg.signedPreKeyId y.g.msg.baseKey σ
    stageP4MatchedExitAtPlaced kit ikit s0 s' y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      ptCap ptPtr 8#64 opkHi kyberPreKeyId signedPreKeyId
      (vecResultAt E2E.HooksE.A0 y.out (.ok pt)) pt
      y.g.peer y.g.msg.identityKey sstf istf ∗
    pathBP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG msgVer preKeyMsgRem coinsPost ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
    decResAt E2E.HooksE.A0 y.out (.ok pt) ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      (LsTokenInit ∗ coinsPost) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  unfold stageP4MatchedExitAtPlaced stageP4MatchedSharedPlaced pathBP4RemAtPlaced
  rw [hs'_sp]
  have hdec : vecResultAt E2E.HooksE.A0 y.out (.ok pt) = decResAt E2E.HooksE.A0 y.out (.ok pt) := rfl
  have hss_vt :
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hid_vt :
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4MatchedCallStack
          (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)) ∗
      stackAt sp (stageP4MatchedCallStack
        (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)) =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B
      (cliPollStageP4MatchedStack_placed_le_subStack E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer B)
      hsp_sub).symm
  have hstores :
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) sstf ∗
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F y.g.msg.signedPreKeyId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid y.g.msg.signedPreKeyId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
      storesAt E2E.HooksE.A0 y.g.stores g' := by
    rw [← hsess, ← hid, ← hot, ← hspk, ← hkpk, ← hpub]
    exact cliPollStoresKitsAtPlaced_entails_storesAt σ y.g.stores g'
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
      decResAt E2E.HooksE.A0 y.out (.ok pt) ∗
      ((cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ).storeAt
          (y.g.stores + 0xf0#64) sstf ∗
        (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
        (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).storeAt
          (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F y.g.msg.signedPreKeyId σ).storeAt
          (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
        (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid y.g.msg.signedPreKeyId y.g.msg.baseKey σ).storeAt
          (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
        dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      (signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
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
            (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)) ∗
        stackAt sp (stageP4MatchedCallStack
          (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ))) ∗
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

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
