/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFold
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFoldPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Poll Path B Stage P3 Match Continuation Fold

Defines `stageP2MatchedMatchPrePlaced` and `genP3PrePlaced` and proves `matched_match_fold_placed`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option linter.unusedSimpArgs false

/-- Placed Stage P2 match-continuation precondition at `+0x1778` (`stageP2MatchedMatchPre` with `lsLogOff`). -/
abbrev stageP2MatchedMatchPrePlaced (A : RustAlloc) [LibsignalPlacement] (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt
      v_330 v_388 v_d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (outerVerByte innerVerByte b_2c0 : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (F : SepProp) : SepProp :=
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  Matched.prevSessionsEmptyAt A coroPtr g ∗
  sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
  ((coroPtr + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
  ((coroPtr + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  ((msgPtr + 0x70#64) ↦₈ innerVerByte) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
  ((msgPtr + 0xf0#64) ↦₈ outerVerByte) ∗
  ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((sp + 0x90#64) ↦₆₄ v_388) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
  ((sp + 0xa8#64) ↦₆₄ v_330) ∗
  ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ innerVerByte.zeroExtend 32) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
  memRegion (sp + 0x370#64) 36 ∗
  ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
  ((sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
  ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
  ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
  ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
  ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x3e0#64) 34 ∗
  memRegion (sp + 0x920#64) 6 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  memRegion outPtr 48 ∗
  FromRecordCallees.lsLogOff ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool ∗
  stackAt sp rootStack ∗
  F

/-- Placed `genP3CallFrame` (`coinsAtPlaced cur rest` + `FromRecordCallees.lsLogOff`). -/
abbrev genP3CallFramePlaced (A : RustAlloc) [LibsignalPlacement] (sp : BitVec 64)
    (remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32)
    (rest : List (BitVec 8)) (rem loc : AddrGhost) (msgG : SignalMessageGhost)
    (msg : SignalMessage) : SepProp :=
  memRegion (sp + 0xa90#64) 344 ∗
    ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
    ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
    ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
    ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
    ((sp + 0x3ac#64) ↦₈ 3#8) ∗
    protocolAddressAt A rem remAddrPtr ∗
    protocolAddressAt A loc locAddrPtr ∗
    signalMessageAt A msgG whisperMsgPtr msg ∗
    memRegion (sp + 0x270#64) 48 ∗
    CryptoVerification.SignalSession.Coins.coinsAtPlaced cur rest ∗
    FromRecordCallees.lsLogOff ∗
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)

/-- Placed `genP3Pre` at `+0x1778`. -/
def genP3PrePlaced (A : RustAlloc) [LibsignalPlacement] (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ⌜s.sp = sp ∧
    s.readReg64 .x19 = coroPtr ∧
    s.readReg64 .x27 = sp + 0x370#64 ∧
    s.readReg64 .x29 = fp⌝ ∗
    sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
    A.pool ∗
    stackAt sp chainCloneStack ∗
    memRegion (sp + 0x3e0#64) 104 ∗
    ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
    genP3SpillAll sp

/-- Placed Stage P3 match continuation fold (`matched_match_fold` under `[LibsignalPlacement]`). -/
theorem matched_match_fold_placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (sess : Session (List (BitVec 8))) (s0 s2 : State)
    (sp rngPtr v_d0 : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (F_frame : SepProp)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    stageP2MatchedMatchPrePlaced E2E.HooksE.A0 s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym)
      y.g.peerA (y.g.msgA + 0xc8#64) v_d0
      opkHi kyberPreKeyId signedPreKeyId
      y.g.msg.messageVersion y.g.msg.message.messageVersion 0#8
      y.g.msg.baseKey y.g.msg.identityKey g recG sess.state
      (matchedInnerFramePlaced y rngPtr sp ∗ F_frame) ⊢
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        genP3PrePlaced E2E.HooksE.A0 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 g 0#8 ∗
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
          preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)) ∗ F_frame := by
  unfold genP3PrePlaced
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _)))))
  dsimp only [stageP2MatchedMatchPrePlaced, matchedInnerFramePlaced, genP3CallFramePlaced]
  unfold stageP3Sub5ExtraPrePrevEmpty
  have hprev_eq :
      Matched.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g =
      Poll.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g := rfl
  rw [hsp2, hprev_eq, stackAt_root_eq_chainClone sp,
      signalMessageAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
  have hcoro := coro_match_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr v_d0 opkHi kyberPreKeyId signedPreKeyId
  have hstk := stack_match_fold sp y.fut y.g.msgA y.g.peerA v_d0
  have hc := Slots.coinsInstalledPlaced_entails_coinsAtPlaced y.g.coinsP y.g.coins hcoins
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
    (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      sessionStateAt E2E.HooksE.A0 (y.fut + 0xf8#64) recG sess.state ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp FromRecordChainClone.chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ y.g.msg.message.messageVersion.zeroExtend 32) ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      ((y.g.msgA + 0x70#64) ↦₈ y.g.msg.message.messageVersion) ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      memRegion (sp + 0x270#64) 48 ∗
      FromRecordCallees.lsLogOff ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x448#64) 240 ∗
      Poll.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      memRegion y.out 48 ∗
      memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x370#64) 36 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xf0#64) ↦₈ y.g.msg.messageVersion) ∗
      preKeyMsgRemMatchedAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      F_frame) by sep_frame) ?_
  refine Entails.trans (sepConj_mono hc (sepConj_mono hcoro (sepConj_mono_left hstk))) ?_
  sep_frame

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
