/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonStage2PathAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFoldsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Over-Path (`Path C`) Stage P2 for Non-Canonical `PreKeySignalMessage` Wire Encodings

Re-exports Path-A Stage P2 contracts from `D3NonCanonStage2PathAPlaced` and proves
relocatable Over-Path (`Path C`) Stage P2 contracts for arbitrary `pm : PreKeySignalMessage`
satisfying `pkToE? pm = some m` (`pm.serialized` unconstrained).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Coins.Placed

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Over-Path (`Path C`) Stage P2 Spatial Entry Unpack & Exit Fold -/

/-- Placed entry spatial unpack from `StageP2PathCOverQpanCliD3MemInvPlacedStmt` into
`Over.stageP2OverPreAtPlaced ... pathAInnerFrameD3Placed`. -/
theorem stageP2_entry_unpack_pathCOver_d3_placed {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hcur : r.currentSession = some sess)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hfp : fp = sp + 0xc70#64)
    (hdec0 : DecPkOk₀ ⟨W.C, W.Q⟩ (fun _ => False) y.g.F y.g.peer.val y.g.me.val (pmOfE m i))
    (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some r) ∗
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    coinsInstalledPlaced y.g.coinsP y.g.coins ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    LsTokenInit ∗
    FromRecordCallees.lsLogOff ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ g : RecordGhost, ∃∗ recG : SessionGhost, ∃∗ w : PathAEntryWords,
        ⌜Slots.scopeKit r ∧ g.cur = some recG ∧
         E2E.Record.Serialization.CanonSession recG sess ∧
         y.g.msgG.kyberPtr ≠ 0#64 ∧
         (∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)⌝ ∗
        Over.stageP2OverPreAtPlaced E2E.HooksE.A0 0#64
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
          y.g.me y.g.peer g recG sess (dpClosSubStack B)
          (pathAInnerFrameD3Placed y i rngPtr sp) := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  rw [hbk_eq]
  rw [sepConj_comm (stageP2PostP1At _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _, ← sepConj_assoc]
  dsimp only [p1LoadedRecordAt]
  simp only [sepConj_assoc]
  refine Entails.pure_left fun hkit => ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g => ?_
  refine Entails.trans
    (sepConj_mono_left (sessionRecordAt_some_eq_prev_sess E2E.HooksE.A0 y.fut g r sess hcur)) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun recG => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hgcur => ?_
  rw [sepConj_assoc]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (OverP2Inst.sessionAt_dup_canonSession E2E.HooksE.A0 (y.fut + 0xf8#64) recG sess))) ?_
  simp only [sepConj_assoc]
  rw [pull_pure_after1_d3]
  refine Entails.pure_left fun hcanon => ?_
  dsimp only [stageP2PostP1At]
  rw [coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    (Poll.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g ∗
      sessionStateReprAt E2E.HooksE.A0 (y.fut + 0xf8#64) recG sess ∗
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
      LsTokenInit ∗ FromRecordCallees.lsLogOff ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA_d3 y.g.msgG y.g.msgA m i hpk hmsg_i)
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
      (pathAMsgRemInnerAtD3_dup_kyberPtr y.g.msgG y.g.msgA y.g.msg)))) ?_
  rw [pull_pure_msg_group_d3]
  refine Entails.pure_left fun hctBuf_nz => ?_
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := E2E.HooksE.A0) 0#64
    (cliKitStk B) y.g.stores StoresGhost.opened
    (cliSessInv_opened_scopeKit hScope hFok)
    (cliIdOwnInv_opened hdec0)
    (cliIdInv_opened_peer hFok)
    (cliPkInv_opened hdec0 opkWord)
    (cliSpkInv_opened hdec0 m.spkId)
    (cliKpkInvFull_opened hdec0 m.kpkId m.spkId (pmOfE m i).baseKey)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores)))) ?_
  have hprevEq :
      Poll.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g =
        Matched.prevSessionsEmptyAt E2E.HooksE.A0 y.fut g := rfl
  refine Entails.sepExists_right g
    (Entails.sepExists_right recG
      (Entails.sepExists_right ⟨opkWord, u488, u80, u88, u90, b4b0, b4f1⟩
        (Entails.pure_right ⟨hkit, hgcur, hcanon, hctBuf_nz, hopkWord⟩ ?_)))
  exact Entails.of_eq (by
    dsimp only [cliPollStoresKitsAt, Over.stageP2OverPreAtPlaced, pathAInnerFrameD3Placed,
      FromRecordCallees.lsLogOff, LsTokenInit]
    rw [hprevEq]
    ac_rfl)

private theorem pull_pure_after7_d3_placed {A1 A2 A3 A4 A5 A6 A7 Rest : SepProp} {φ : Prop} :
    A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ (⌜φ⌝ ∗ Rest))))))) =
      ⌜φ⌝ ∗ (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ Rest))))))) := by
  ac_rfl

set_option maxHeartbeats 800000 in
/-- Placed full Stage P2 Over-path (`Path C`) `+0x1778` normal-exit spatial fold into `hok`'s
precondition for arbitrary `pm.serialized`. -/
theorem p2OverOkPost_fold_pathCOver_d3_placed {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 s2 : State) (sp fp rngPtr : BitVec 64)
    (recG G_bob : SessionGhost) (sess : Session (List (BitVec 8)))
    (st_bob : SessionState (List (BitVec 8)))
    (hcanon : E2E.Record.Serialization.CanonSession recG sess)
    (hpk : pkToE? y.g.msg = some m) (hmsg_i : y.g.msg.message = i)
    (hcoins : y.g.coins.length < 2 ^ 63) (hsub : dpClosSubStack B ≤ sp.toNat)
    (hfp : fp = sp + 0xc70#64) (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id)
    (hsp2 : s2.sp = sp) (hx19_2 : s2.readReg64 .x19 = y.fut)
    (hx27_2 : s2.readReg64 .x27 = sp + 0x370#64) :
    Over.p2OverOkPostAtPlaced E2E.HooksE.A0 0#64
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) recG sess G_bob st_bob
      (mkPathAHdr m) i.messageVersion 0#8 w.opkWord m.kpkId m.regId m.spkId
      StoresGhost.opened.signed StoresGhost.opened.kyber
      StoresGhost.opened.oneTime StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameD3Placed y i rngPtr sp) ⊢
      ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
        ⌜prevCap' ≠ 0#64⌝ ∗
        LsTokenInit ∗
        genP3PrePlaced E2E.HooksE.A0 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
          y.g.msgA y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
          G_bob st_bob y.g.peer y.g.me y.g.msgG.msg y.g.msg.message s2 ∗
        p2StageP3Sub5ExtraPrePrev1 E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 prevCap' prevPtr'
          (E2E.Record.encSession (OverP2.clearPending sess)) 0#8 ∗
        stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
          (coroOpkIdAtP4 y.fut m.opkId)
          (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
        stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
        memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) := by
  have hbk_eq : y.g.msg.baseKey = (pmOfE m i).baseKey :=
    (pm_fields_of_pkToE hpk hmsg_i).2.2.2.2.1.trans (pmOfE_fields m i).2.2.2.2.1.symm
  have hmsgSlices := p2MsgFields_reassemble_slices_d3 y.g.msgG y.g.msgA m i hpk hmsg_i w.opkWord hopk
  rw [hbk_eq, hmsg_i] at hmsgSlices ⊢
  dsimp only [Over.p2OverOkPostAtPlaced, Over.prevArchived1At, pathAInnerFrameD3Placed, LsTokenInit]
  rw [OverP2Inst.encSessionMem_clearPending_eq hcanon]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun prevCap' => Entails.sepExists_elim fun prevPtr' => ?_
  simp only [sepConj_assoc]
  rw [pull_pure_after7_d3_placed]
  refine Entails.pure_left fun hcap_ne => ?_
  refine Entails.sepExists_right prevCap' (Entails.sepExists_right prevPtr'
    (Entails.pure_right hcap_ne ?_))
  unfold genP3PrePlaced
  rw [hsp2]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left
      (Entails.pure_right ⟨rfl, hx19_2, hx27_2, rfl⟩ (Entails.refl _))))
  unfold genP3CallFramePlaced p2StageP3Sub5ExtraPrePrev1
  rw [hsp2, hdrOpkIdBv?_mkPathAHdr m, kpkId_shift_or_one_eq_append_d3 m.kpkId]
  have hstkSub : stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
        stackAt sp FromRecordChainClone.chainCloneStack) := by
    rw [P3P4.stackAt_sub_eq sp (dpClosSubStack B) rootStack
          (by unfold rootStack dpClosSubStack; omega)
          (Nat.le_trans hsub (Nat.le_of_lt sp.isLt)),
        Poll.stackAt_root_eq_chainClone sp]
  have h270 : memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 =
      memRegion (sp + 0x270#64) 48 := by
    rw [memRegion_split (sp + 0x270#64) 9 39 (by decide)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h3e0 : memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp,
        memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  have hc := Slots.coinsInstalledPlaced_entails_coinsAtPlaced y.g.coinsP y.g.coins hcoins
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := E2E.HooksE.A0) 0#64
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores StoresGhost.opened
  dsimp only [cliPollStoresKitsAt] at hstores
  rw [hstkSub, h3e0]
  dsimp only [FromRecordCallees.lsLogOff]
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
    ((cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId (cliKitStk B)).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId (pmOfE m i).baseKey (cliKitStk B)).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtD3 y.g.msgG y.g.msgA y.g.msg) ∗
    ((memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      sessionStateAt E2E.HooksE.A0 (y.fut + 0xf8#64) G_bob st_bob ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp FromRecordChainClone.chainCloneStack ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ y.g.msgA) ∗
      ((sp + 0xb8#64) ↦₃₂ i.messageVersion.zeroExtend 32) ∗
      ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - FromRecordChainClone.chainCloneStack) ∗
      ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x448#64) 240 ∗
      OverP2.prevVecAt E2E.HooksE.A0 (y.fut + 0xe0#64) prevCap' prevPtr'
        [E2E.Record.encSession (OverP2.clearPending sess)] ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      memRegion y.out 48 ∗
      memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x370#64) 36 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
    by sep_frame) ?_
  rw [h270]
  refine Entails.trans (sepConj_mono hc (sepConj_mono (p2_coro_ok_with_opk_d3_placed y m w rngPtr hopk)
    (sepConj_mono (p2_stk_ok_fold_d3_placed sp fp y.fut y.g.msgA y.g.peerA m.spkId hfp)
      (sepConj_mono hstores (sepConj_mono_left hmsgSlices))))) ?_
  sep_frame

/-! ## 2. Over-Path (`Path C`) Stage P2 Pure Model-Rejection Witness & Error Postcondition -/

/-- Pure model-rejection witness discharged on all 6 Stage P2 error arms on Path C (`Over`)
for arbitrary `pm.serialized` under `[LibsignalPlacement]`. -/
def StageP2PathCOverModelRejD3Placed (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (F : FsFiles) (pm : PreKeySignalMessage) : Prop :=
  ∃ (m : PreKeyMessageFields) (i : SignalMessage),
    pkToE? pm = some m ∧
    SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i ∧
    pm.message = i ∧
    ((pkStoreKeys F m = none ∨
      StoresGhost.opened.identity.keyPair cliIo.rd F = .error () ∨
      StoresGhost.opened.identity.regId cliIo.rd F = .error ()) ∨
     (∃ (k : ResponderPreKeySecrets) (kp : RecordCodecs.IdentityKeyPair),
       pkStoreKeys F m = some k ∧
       StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp ∧
       ∀ reg : BitVec 32,
         SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
           (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none))

/-- Exit postcondition of all 6 Stage P2 store-error and PQXDH-rejection arms on Path C (`Over`)
for arbitrary `pm.serialized` under `[LibsignalPlacement]`. -/
def StageP2PathCOverErrD3Placed [LibsignalPlacement] (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (B : RunBudgets) (x : DecPkGhost) (fut out : BitVec 64)
    (s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop :=
  ∃ err : ApiError AddrVal Unit,
    err ≠ .panic ∧
    err ≠ .store () ∧
    sf.trace = s1.trace ∧
    StageP2PathCOverModelRejD3Placed X W x.F x.msg ∧
    (Pf ⊢
      dpFutDoneAt fut ∗
      memRegion sp 3280 ∗
      decResAt E2E.HooksE.A0 out (.error err) ∗
      storesAt E2E.HooksE.A0 x.stores StoresGhost.opened ∗
      preKeyMsgAt E2E.HooksE.A0 x.msgG x.msgA x.msg ∗
      protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
      protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap)

end LibsignalBinary.Proofs.SignalSession.Cli.D3
