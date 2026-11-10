/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPre
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFold
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Path B Stage P3 Match Continuation Fold

Proves `matched_match_fold`, folding `stageP2MatchedMatchPre` and `matchedInnerFrame` into
`genP3Pre`, `stageP3Sub5ExtraPrePrevEmpty`, `stageP3CoroFrameAt`, and `stageP3StackFrameAt`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
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

theorem coro_match_fold (fut msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr v_d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) :
    processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
    decryptPrekeyCoroInitAt fut msgPtr remoteAddrPtr localAddrPtr
      sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    ((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
    ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
    coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    cells (fut + 0x250#64) 6 ∗ memRegion (fut + 0x280#64) 24 ∗
    ((fut + 0x298#64) ↦₃₂ 2#32) ∗ ((fut + 0x29c#64) ↦₃₂ opkHi) ∗
    ((fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗ ((fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
    ((fut + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
    memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 ∗
    ((fut + 0x330#64) ↦₆₄ remoteAddrPtr) ∗ ((fut + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
    processPrekeyInnerRem23At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    processPrekeyPostTrustAt fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    ((fut + 0x390#64) ↦₈ 1#8) ∗ cells (fut + 0x398#64) 2 ∗
    ((fut + 0x4f1#64) ↦₈ 0#8) ∗ ((fut + 0x4f2#64) ↦₈ 1#8) ∗
    memRegion (fut + 0x2c1#64) 7 ∗ memRegion (fut + 0x391#64) 7 ∗
    memRegion (fut + 0x3a8#64) 80 ∗ memRegion (fut + 0x488#64) 8 ∗
    memRegion (fut + 0x4b0#64) 65 ∗ memRegion (fut + 0x4f3#64) 5 ∗
    memRegion (fut + 0x4f8#64) 736 ⊢
      stageP3CoroFrameAt fut msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr
        (((fut + 0x298#64) ↦₃₂ 2#32) ∗ ((fut + 0x29c#64) ↦₃₂ opkHi))
        (((fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
         ((fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
         memRegion (fut + 0x2a8#64) 4) := by
  unfold stageP3CoroFrameAt coroPostP2UnusedAt
  rw [coroCopyAt_eq_head3_tail11]
  have h4b0 : memRegion (fut + 0x4b0#64) 65 ∗ ((fut + 0x4f1#64) ↦₈ 0#8) ⊢
      memRegion (fut + 0x4b0#64) 66 := by
    rw [memRegion_split (fut + 0x4b0#64) 65 1 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (ProofLib.pointsTo8_entails_memRegion _ _)
  have h250 : cells (fut + 0x250#64) 6 = memRegion (fut + 0x250#64) 48 :=
    (ProofLib.memRegion_cells (fut + 0x250#64) 6 (by decide)).symm
  have h398 : cells (fut + 0x398#64) 2 = memRegion (fut + 0x398#64) 16 :=
    (ProofLib.memRegion_cells (fut + 0x398#64) 2 (by decide)).symm
  rw [h250, h398]
  refine Entails.trans (show _ ⊢
    (processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
      memRegion (fut + 0x3a8#64) 80 ∗ memRegion (fut + 0x488#64) 8) ∗
    (((fut + 0x330#64) ↦₆₄ remoteAddrPtr) ∗ ((fut + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
      processPrekeyInnerRem23At fut msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt) ∗
    processPrekeyPostTrustAt fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    (memRegion (fut + 0x4b0#64) 65 ∗ ((fut + 0x4f1#64) ↦₈ 0#8)) ∗
    ((fut + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
    ((fut + 0x390#64) ↦₈ 1#8) ∗ ((fut + 0x4f2#64) ↦₈ 1#8) ∗
    (decryptPrekeyCoroInitAt fut msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
      ((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
      coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
      memRegion (fut + 0x250#64) 48 ∗ memRegion (fut + 0x280#64) 24 ∗
      ((fut + 0x298#64) ↦₃₂ 2#32) ∗ ((fut + 0x29c#64) ↦₃₂ opkHi) ∗
      ((fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗ ((fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
      memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 ∗
      memRegion (fut + 0x398#64) 16 ∗ memRegion (fut + 0x2c1#64) 7 ∗
      memRegion (fut + 0x391#64) 7 ∗ memRegion (fut + 0x4f3#64) 5 ∗
      memRegion (fut + 0x4f8#64) 736) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (active10_3a8_488_fold _ _ _ _ _ _ _ _ _ _)
    (sepConj_mono (innerInit_200_fold _ _ _ _ _ _ _ _ _ _ _ _)
      (sepConj_mono (postTrust_64_32_fold _ _ _ _ _ _ _ _ _ _ _ _)
        (sepConj_mono h4b0 (pts32_mr
          (sepConj_mono (ProofLib.pointsTo8_entails_memRegion _ _)
            (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)))))))) ?_
  rw [coro_2c8_16_184_eq fut]
  sep_frame

theorem stack_match_fold (sp fut msgPtr remoteAddrPtr v_d0 : BitVec 64) :
    (sp ↦₆₄ 0#64) ∗
    memRegion (sp + 0x8#64) 120 ∗
    ((sp + 0x90#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
    ((sp + 0x98#64) ↦₆₄ (fut + 0x398#64)) ∗
    ((sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
    memRegion (sp + 0xbc#64) 4 ∗
    ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
    memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
    spMidGapsAt sp ∗
    ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
    ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
    ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
    memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
    memRegion (sp + 0x538#64) 24 ∗
    memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
    memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
    memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 ⊢
      genP3SpillAll sp ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      memRegion (sp + 0xa90#64) 344 ∗
      stageP3StackFrameAt sp (msgPtr + 0xc8#64) remoteAddrPtr := by
  unfold stageP3StackFrameAt spMidGapsAt spHighGapsAt
  have hd8 : memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x234#64) 28 =
      memRegion (sp + 0xd8#64) 376 := by
    rw [memRegion_split (sp + 0xd8#64) 348 28 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h2b0 :
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2d4#64) 12 ∗
      memRegion (sp + 0x2e0#64) 36 ∗ memRegion (sp + 0x304#64) 12 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x334#64) 12 ∗
      memRegion (sp + 0x340#64) 36 ∗ memRegion (sp + 0x364#64) 12 =
      memRegion (sp + 0x2b0#64) 192 := by
    rw [sp_2b0_192_split sp]
    unfold sp2b0GapsAt
    ac_rfl
  have h3ad :
      memRegion (sp + 0x3ad#64) 3 ∗
      (((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
        ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
        ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64))) ⊢
      memRegion (sp + 0x3ad#64) 27 := by
    rw [memRegion_split (sp + 0x3ad#64) 3 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (words3_off_mr sp 0x3b0#64 0x3b8#64 0x3c0#64 _ _ _)
  have h3e0 : memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 =
      memRegion (sp + 0x3e0#64) 104 := by
    rw [memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h992 : memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 =
      memRegion (sp + 0x550#64) 992 := by
    rw [memRegion_split (sp + 0x550#64) 976 16 (by decide),
        memRegion_split (sp + 0x550#64 + 976#64) 6 10 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have ha90 : memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 =
      memRegion (sp + 0xa90#64) 344 := by
    rw [memRegion_split (sp + 0xa90#64) 48 296 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [← hd8, ← h2b0, ← h3e0, ← h992, ← ha90]
  refine Entails.trans (show _ ⊢
    (memRegion (sp + 0x8#64) 120 ∗ ((sp + 0x98#64) ↦₆₄ (fut + 0x398#64)) ∗
      ((sp + 0xd0#64) ↦₆₄ v_d0) ∗ memRegion (sp + 0x930#64) 96) ∗
    (memRegion (sp + 0x3ad#64) 3 ∗
      (((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
        ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
        ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)))) ∗
    (memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗
      (sp ↦₆₄ 0#64) ∗ ((sp + 0x90#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗ memRegion (sp + 0xbc#64) 4 ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x234#64) 28 ∗
      memRegion (sp + 0x264#64) 12 ∗ memRegion (sp + 0x2a0#64) 16 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2d4#64) 12 ∗
      memRegion (sp + 0x2e0#64) 36 ∗ memRegion (sp + 0x304#64) 12 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x334#64) 12 ∗
      memRegion (sp + 0x340#64) 36 ∗ memRegion (sp + 0x364#64) 12 ∗
      memRegion (sp + 0x394#64) 12 ∗ memRegion (sp + 0x3a8#64) 4 ∗
      memRegion (sp + 0x538#64) 24 ∗ memRegion (sp + 0x550#64) 976 ∗
      memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x990#64) 256 ∗ memRegion (sp + 0xbe8#64) 136) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (sp_8_120_to_genP3SpillAll sp (fut + 0x398#64) v_d0)
    (sepConj_mono_left h3ad)) ?_
  sep_frame

theorem matched_match_fold_ext {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (sess : Session (List (BitVec 8))) (s0 s2 : State)
    (sp rngPtr v_d0 : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (F_frame : SepProp)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    stageP2MatchedMatchPre A img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x78#64) (kyberVt img)
      y.g.peerA (y.g.msgA + 0xc8#64) v_d0
      opkHi kyberPreKeyId signedPreKeyId
      y.g.msg.messageVersion y.g.msg.message.messageVersion 0#8
      y.g.msg.baseKey y.g.msg.identityKey g recG sess.state
      (matchedInnerFrameExt img y rngPtr sp ∗ F_frame) ⊢
      (TokenInit img ∗
        genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        stageP3Sub5ExtraPrePrevEmpty A s0 s2 y.fut y.out 8#64 g 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr
          (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
          (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
           ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
           memRegion (y.fut + 0x2a8#64) 4) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A y.g.msgG y.g.msgA y.g.msg)) ∗ F_frame := by
  unfold genP3Pre
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _)))))
  dsimp only [stageP2MatchedMatchPre, matchedInnerFrameExt]
  unfold genP3CallFrame stageP3Sub5ExtraPrePrevEmpty
  have hprev_eq :
      Matched.prevSessionsEmptyAt A y.fut g =
      Poll.prevSessionsEmptyAt A y.fut g := rfl
  rw [hsp2, hprev_eq, stackAt_root_eq_chainClone sp,
      signalMessageAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
  have hcoro := coro_match_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr v_d0 opkHi kyberPreKeyId signedPreKeyId
  have hstk := stack_match_fold sp y.fut y.g.msgA y.g.peerA v_d0
  have hc := coinsInstalled_to_coinsAt img y.g.coinsP y.g.coins hcoins
  refine Entails.trans (show _ ⊢
    coinsInstalled img y.g.coinsP y.g.coins ∗
    (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x78#64) (kyberVt img) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      ((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi) ∗
      ((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗ ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
      ((y.fut + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
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
    (TokenInit img ∗
      sessionStateAt A (y.fut + 0xf8#64) recG sess.state ∗
      A.pool ∗
      stackAt sp FromRecordChainClone.chainCloneStack ∗
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
      logOff img ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
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

theorem matched_match_fold {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (sess : Session (List (BitVec 8))) (s0 s2 : State)
    (sp rngPtr v_d0 : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (F_frame : SepProp)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    stageP2MatchedMatchPre E2E.HooksE.A0 img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x78#64) (kyberVt img)
      y.g.peerA (y.g.msgA + 0xc8#64) v_d0
      opkHi kyberPreKeyId signedPreKeyId
      y.g.msg.messageVersion y.g.msg.message.messageVersion 0#8
      y.g.msg.baseKey y.g.msg.identityKey g recG sess.state
      (matchedInnerFrame img y rngPtr sp ∗ F_frame) ⊢
      (TokenInit img ∗
        genP3Pre E2E.HooksE.A0 img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          recG sess.state y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 g 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr
          (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
          (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
           ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
           memRegion (y.fut + 0x2a8#64) 4) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)) ∗ F_frame :=
  matched_match_fold_ext img y sess s0 s2 sp rngPtr v_d0 g recG
    opkHi kyberPreKeyId signedPreKeyId F_frame hcoins hsp2 hx19_2 hx27_2

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
