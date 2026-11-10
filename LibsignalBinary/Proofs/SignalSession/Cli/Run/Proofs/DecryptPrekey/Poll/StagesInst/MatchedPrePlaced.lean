/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPre
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Poll Path B Stage P2 Spatial Entry Unpack

Defines `matchedInnerFramePlaced` and `stageP2MatchedPrePlaced` and proves
`matched_entry_unpack_placed` under `[LibsignalPlacement]`.
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

/-- Placed inner coroutine/stack/message frame untouched by `stageP2_matched_ok_framed_placed`. -/
def matchedInnerFramePlaced {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (rngPtr sp : BitVec 64) : SepProp :=
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
  cells (y.fut + 0x398#64) 2 ∗
  memRegion (y.fut + 0x280#64) 24 ∗
  memRegion (y.fut + 0x2ac#64) 8 ∗
  memRegion (y.fut + 0x2b4#64) 12 ∗
  memRegion (y.fut + 0x2c1#64) 7 ∗
  memRegion (y.fut + 0x391#64) 7 ∗
  memRegion (y.fut + 0x3a8#64) 80 ∗
  memRegion (y.fut + 0x488#64) 8 ∗
  memRegion (y.fut + 0x4b0#64) 65 ∗
  memRegion (y.fut + 0x4f3#64) 5 ∗
  memRegion (y.fut + 0x4f8#64) 736 ∗
  (sp ↦₆₄ 0#64) ∗
  memRegion (sp + 0x8#64) 120 ∗
  memRegion (sp + 0xbc#64) 4 ∗
  ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
  memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x250#64) 20 ∗
  memRegion (sp + 0x270#64) 48 ∗
  memRegion (sp + 0x2b0#64) 36 ∗
  memRegion (sp + 0x2e0#64) 36 ∗
  memRegion (sp + 0x310#64) 36 ∗
  memRegion (sp + 0x340#64) 36 ∗
  spMidGapsAt sp ∗
  memRegion (sp + 0x402#64) 70 ∗
  memRegion (sp + 0x448#64) 240 ∗
  memRegion (sp + 0x538#64) 24 ∗
  memRegion (sp + 0x550#64) 976 ∗
  memRegion (sp + 0x926#64) 10 ∗
  memRegion (sp + 0x930#64) 96 ∗
  memRegion (sp + 0x990#64) 256 ∗
  memRegion (sp + 0xac0#64) 296 ∗
  memRegion (sp + 0xbe8#64) 136 ∗
  signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
  preKeyMsgRemMatchedAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
  protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
  protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
  coinsInstalledPlaced y.g.coinsP y.g.coins ∗
  SpqrV1.GF.Mul2U16.tokenInitPlacedAt

/-- Placed Stage P2 matched-session entry precondition (`stageP2MatchedPre` with `lsLogOff`). -/
abbrev stageP2MatchedPrePlaced (A : RustAlloc) [LibsignalPlacement] (s0 : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (F : SepProp) : SepProp :=
  cells (coroPtr + 0x3f8#64) 6 ∗
  cells (coroPtr + 0x468#64) 4 ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  sessionRecordAt A (coroPtr + 0xe0#64) g r ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  ((msgPtr + 0x70#64) ↦₈ innerVerByte) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
  ((msgPtr + 0xf0#64) ↦₈ outerVerByte) ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ u_90) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
  ((sp + 0xb8#64) ↦₃₂ u_b8) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
  memRegion (sp + 0x370#64) 36 ∗
  ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
  ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
  ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
  ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
  ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
  ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
  ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
  ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
  memRegion (sp + 0x3e0#64) 34 ∗
  memRegion (sp + 0x920#64) 6 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  memRegion outPtr 48 ∗
  FromRecordCallees.lsLogOff ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool ∗
  stackAt sp rootStack ∗
  F

/-- Placed entry spatial unpack from `StageP2MatchedFramedCliStmt` into `stageP2MatchedPrePlaced... matchedInnerFramePlaced`. -/
theorem matched_entry_unpack_placed {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (sess : Session (List (BitVec 8))) (s0 : State)
    (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Scope E2E.HooksE.A0 y.fut (some ⟨some sess⟩) ∗
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    FromRecordCallees.lsLogOff ∗
    stackAt sp rootStack ⊢
      ∃∗ g : RecordGhost, ∃∗ w : MatchedEntryWords,
        stageP2MatchedPrePlaced E2E.HooksE.A0 s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
          y.g.peerA (y.g.msgA + 0xc8#64)
          w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
          w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
          w.u_2a8 (v_b8.extractLsb' 0 32)
          y.g.msg.messageVersion y.g.msg.message.messageVersion
          w.b_4f1 0#8 0#8 0#8 w.b_3ac
          y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩
          (matchedInnerFramePlaced y rngPtr sp) := by
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]
  simp only [sepConj_assoc]
  refine Entails.pure_left fun _ => ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => ?_
  dsimp only [stageP2PostP1At]
  rw [coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23,
      preKeyMsgAt_eq_base_idKey_sep, signalMessageAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
  have h250 : memRegion (y.fut + 0x250#64) 48 = cells (y.fut + 0x250#64) 6 :=
    ProofLib.memRegion_cells (y.fut + 0x250#64) 6 (by decide)
  rw [h250]
  refine Entails.trans (show _ ⊢
      coroUnusedP1At y.fut ∗
      (((sp + 0xb8#64) ↦₆₄ v_b8) ∗ memRegion (sp + 0x3e0#64) 368 ∗ closStackUnusedP1OkAt sp) ∗
      (sessionRecordAt E2E.HooksE.A0 (y.fut + 0xe0#64) g ⟨some sess⟩ ∗
        decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗
        ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
        ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
        coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        cells (y.fut + 0x250#64) 6 ∗
        ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
        ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗
        ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
        processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
          y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
          (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
        processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
          y.g.stores (lsρ cliIdentityVtSym) (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
          (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) ∗
        ((y.fut + 0x390#64) ↦₈ 0#8) ∗
        cells (y.fut + 0x398#64) 2 ∗
        ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
        (sp ↦₆₄ 0#64) ∗
        ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
        ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
        ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
        ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
        ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
        memRegion (sp + 0xd8#64) 348 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        memRegion y.out 48 ∗
        E2E.HooksE.A0.pool ∗
        ((y.g.msgA + 0x70#64) ↦₈ y.g.msg.message.messageVersion) ∗
        signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        ((y.g.msgA + 0xf0#64) ↦₈ y.g.msg.messageVersion) ∗
        preKeyMsgRemMatchedAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (coro_unused_split_matched y.fut)
    (sepConj_mono_left (stack_unused_split_matched sp v_b8))) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun u298 => Entails.sepExists_elim fun u2a0 =>
    Entails.sepExists_elim fun u2a8 => Entails.sepExists_elim fun b4f1 => ?_
  rw [sepConj_comm _ (∃∗ u_80 : BitVec 64, _), ← sepConj_assoc]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u3a0 =>
    Entails.sepExists_elim fun b3ac => Entails.sepExists_elim fun u3b0 =>
    Entails.sepExists_elim fun u3b8 => Entails.sepExists_elim fun u3c0 =>
    Entails.sepExists_elim fun u3c8 => Entails.sepExists_elim fun u3d0 =>
    Entails.sepExists_elim fun u3d8 => ?_
  exact Entails.sepExists_right g (Entails.sepExists_right
    ⟨u80, u88, u90, u298, u2a0, u3a0, u3b0, u3b8, u3c0, u3c8, u3d0, u3d8, u2a8, b4f1, b3ac⟩
    (by dsimp only [stageP2MatchedPrePlaced, matchedInnerFramePlaced]; sep_frame))

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
