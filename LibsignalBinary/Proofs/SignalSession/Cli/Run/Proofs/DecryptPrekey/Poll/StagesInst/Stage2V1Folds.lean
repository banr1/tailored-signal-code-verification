/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Msg
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Trans
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFold

/-!
# CLI Poll Stage P2 V1 Entry and Error-Exit Spatial Folds

Defines `pathAInnerFrame` and proves the Stage P2 entry spatial unpack (`stageP2_entry_unpack_pathA`)
and error-exit spatial fold (`p2ErrFrame_fold_pathA`) on Path A.
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

private theorem step_mr8 {a : BitVec 64} {Rest Acc Q : SepProp}
    (h : ∀ u : BitVec 64, Rest ∗ ((a ↦₆₄ u) ∗ Acc) ⊢ Q) :
    (memRegion a 8 ∗ Rest) ∗ Acc ⊢ Q := by
  rw [ProofLib.memRegion_cells a 1 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left]
  exact Entails.sepExists_elim fun u => Entails.trans (by sep_frame) (h u)

private theorem step_mr1 {a : BitVec 64} {Rest Acc Q : SepProp}
    (h : ∀ b : BitVec 8, Rest ∗ ((a ↦₈ b) ∗ Acc) ⊢ Q) :
    (memRegion a 1 ∗ Rest) ∗ Acc ⊢ Q := by
  rw [memRegion_eq_exists_bytes a 1 (by decide), sepExists_sepConj_left, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun bs => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun hlen => ?_
  rcases bs with _ | ⟨b, _ | _⟩ <;> try (simp at hlen; done)
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  exact Entails.trans (by sep_frame) (h b)

private theorem elim_mr1 {a : BitVec 64} {Acc Q : SepProp}
    (h : ∀ b : BitVec 8, (a ↦₈ b) ∗ Acc ⊢ Q) :
    memRegion a 1 ∗ Acc ⊢ Q := by
  rw [memRegion_eq_exists_bytes a 1 (by decide), sepExists_sepConj_left]
  refine Entails.sepExists_elim fun bs => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hlen => ?_
  rcases bs with _ | ⟨b, _ | _⟩ <;> try (simp at hlen; done)
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  exact h b

/-- Bundled entry witness words unpacked from `stageP2PostP1At` + `preKeyMsgAt` on Path A. -/
structure PathAEntryWords where
  opkWord : BitVec 32
  u_488 : BitVec 64
  u_80 : BitVec 64
  u_88 : BitVec 64
  u_90 : BitVec 64
  b_4b0 : BitVec 8
  b_4f1 : BitVec 8

/-- Spatial frame preserved untouched across `stageP2_v1_kits` on Path A. -/
def pathAInnerFrame {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKit E2E.HooksE.A0 img.base y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
    (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
  dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
    (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
    (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
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
  coinsInstalled img y.g.coinsP y.g.coins ∗
  TokenInit img

/-- `A`-polymorphic generalization of `pathAInnerFrame` over `(A : RustAlloc)`. -/
def pathAInnerFrameExt {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) : SepProp :=
  (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer (cliKitStk B)).storeAt
    (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
  dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
  coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
  processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
    (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
  processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
    y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
    (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
  memRegion (y.fut + 0x280#64) 24 ∗ memRegion (y.fut + 0x2ac#64) 8 ∗
  memRegion (y.fut + 0x2b4#64) 12 ∗ memRegion (y.fut + 0x2c1#64) 7 ∗
  memRegion (y.fut + 0x391#64) 7 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
  memRegion (y.fut + 0x782#64) 6 ∗
  (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x279#64) 39 ∗
  memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
  memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
  spMidGapsAt sp ∗ sp550P2V1RemAt sp ∗
  signalMessageRestVerAt A y.g.msgG.msg y.g.msgA i ∗
  pathAMsgRemInnerAtExt A y.g.msgG y.g.msgA m i ∗
  coinsInstalled img y.g.coinsP y.g.coins ∗
  TokenInit img

theorem pathAInnerFrame_eq_A0 {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFrame img y m i rngPtr sp = pathAInnerFrameExt img y m i rngPtr sp :=
  rfl

theorem coro_unused_split_p2v1 (fut : BitVec 64) :
    cells (fut + 0x398#64) 2 ∗ memRegion (fut + 0x250#64) 48 ∗ coroUnusedP1At fut ⊢
      ∃∗ u_488 : BitVec 64, ∃∗ b_4b0 : BitVec 8, ∃∗ b_4f1 : BitVec 8,
        cells (fut + 0x250#64) 6 ∗ memRegion (fut + 0x298#64) 20 ∗
        memRegion (fut + 0x398#64) 96 ∗ cells (fut + 0x3f8#64) 6 ∗ cells (fut + 0x468#64) 4 ∗
        ((fut + 0x488#64) ↦₆₄ u_488) ∗ ((fut + 0x4b0#64) ↦₈ b_4b0) ∗
        memRegion (fut + 0x4b1#64) 64 ∗ ((fut + 0x4f1#64) ↦₈ b_4f1) ∗
        p2CoroScratchTailAt fut ∗
        memRegion (fut + 0x280#64) 24 ∗ memRegion (fut + 0x2ac#64) 8 ∗
        memRegion (fut + 0x2b4#64) 12 ∗ memRegion (fut + 0x2c1#64) 7 ∗
        memRegion (fut + 0x391#64) 7 ∗ memRegion (fut + 0x4f3#64) 5 ∗
        memRegion (fut + 0x782#64) 6 := by
  unfold coroUnusedP1At
  have h398_96 : memRegion (fut + 0x398#64) 16 ∗ memRegion (fut + 0x3a8#64) 80 =
      memRegion (fut + 0x398#64) 96 := by
    rw [memRegion_split (fut + 0x398#64) 16 80 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_cells (fut + 0x250#64) 6 (by decide),
      ← ProofLib.memRegion_cells (fut + 0x398#64) 2 (by decide),
      memRegion_split (fut + 0x280#64) 24 40 (by decide),
      memRegion_split (fut + 0x280#64 + 24#64) 20 20 (by decide),
      memRegion_split (fut + 0x280#64 + 24#64 + 20#64) 8 12 (by decide),
      memRegion_split (fut + 0x3a8#64) 80 48 (by decide),
      memRegion_split (fut + 0x468#64) 32 8 (by decide),
      memRegion_split (fut + 0x4b0#64) 1 65 (by decide),
      memRegion_split (fut + 0x4b0#64 + 1#64) 64 1 (by decide),
      coro_scratch_736_split fut]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_cells (fut + 0x3f8#64) 6 (by decide),
      ProofLib.memRegion_cells (fut + 0x468#64) 4 (by decide)]
  refine Entails.trans (show _ ⊢
    (memRegion (fut + 0x488#64) 8 ∗ memRegion (fut + 0x4b0#64) 1 ∗ memRegion (fut + 0x4f1#64) 1) ∗
    (memRegion (fut + 0x398#64) 16 ∗ memRegion (fut + 0x3a8#64) 80) ∗
    (cells (fut + 0x250#64) 6 ∗ memRegion (fut + 0x298#64) 20 ∗
      cells (fut + 0x3f8#64) 6 ∗ cells (fut + 0x468#64) 4 ∗ memRegion (fut + 0x4b1#64) 64 ∗
      p2CoroScratchTailAt fut ∗ memRegion (fut + 0x280#64) 24 ∗ memRegion (fut + 0x2ac#64) 8 ∗
      memRegion (fut + 0x2b4#64) 12 ∗ memRegion (fut + 0x2c1#64) 7 ∗
      memRegion (fut + 0x391#64) 7 ∗ memRegion (fut + 0x4f3#64) 5 ∗
      memRegion (fut + 0x782#64) 6) by sep_frame) ?_
  rw [h398_96]
  refine step_mr8 fun u488 => step_mr1 fun b4b0 => elim_mr1 fun b4f1 => ?_
  exact Entails.sepExists_right u488
    (Entails.sepExists_right b4b0 (Entails.sepExists_right b4f1 (by sep_frame)))

theorem stack_unused_split_p2v1 (sp fp : BitVec 64) (hfp : fp = sp + 0xc70#64) :
    closStackUnusedP1OkAt sp ⊢
      ∃∗ u_80 : BitVec 64, ∃∗ u_88 : BitVec 64, ∃∗ u_90 : BitVec 64,
        ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x90#64) ↦₆₄ u_90) ∗
        memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3a0#64) 8 ∗ memRegion (sp + 0x3ac#64) 1 ∗
        memRegion (sp + 0x3b0#64) 48 ∗
        cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗
        cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
        memRegion (sp + 0xa90#64) 288 ∗ memRegion (fp + 0xffffffffffffff80#64) 9 ∗
        memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0x250#64) 20 ∗
        memRegion (sp + 0x279#64) 39 ∗ memRegion (sp + 0x2b0#64) 36 ∗
        memRegion (sp + 0x2e0#64) 36 ∗ memRegion (sp + 0x310#64) 36 ∗
        memRegion (sp + 0x340#64) 36 ∗ spMidGapsAt sp ∗ sp550P2V1RemAt sp := by
  unfold closStackUnusedP1OkAt
  have h3b0_48 : memRegion (sp + 0x3b0#64) 24 ∗ memRegion (sp + 0x3c8#64) 24 =
      memRegion (sp + 0x3b0#64) 48 := by
    rw [memRegion_split (sp + 0x3b0#64) 24 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sp_8_144_split_120_words3 sp, sp_234_428_split sp,
      memRegion_split (sp + 0x270#64) 9 39 (by decide), sp_550_1824_split_p2v1 sp fp hfp]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => ?_
  refine Entails.sepExists_right u80 (Entails.sepExists_right u88 (Entails.sepExists_right u90 ?_))
  rw [← h3b0_48]
  sep_frame

/-- `(W : PEParams) (A : RustAlloc)` generalization of `stageP2_entry_unpack_pathA`. -/
theorem stageP2_entry_unpack_pathA_ext {W : PEParams} {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdecOk : DecPkOk₀ W Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit A y.fut none ∗
    preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt A y.g.peer y.g.peerA ∗
    protocolAddressAt A y.g.me y.g.meA ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗
    storesAt A y.g.stores StoresGhost.opened ∗
    TokenInit img ∗
    logOff img ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords,
        ⌜∀ id : BitVec 32, m.opkId = some id → w.opkWord = id⌝ ∗
        stageP2PreAt A img
          (cliPollSpkKit A img.base y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKit A img.base y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B)
          (pathAInnerFrameExt img y m i rngPtr sp) := by
  rw [hmsg]
  dsimp only [p1LoadedRecordAt, stageP2PostP1At]
  have hdrEq : ResponderClosure.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) =
      ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) := rfl
  rw [hdrEq, coroCopyAt_eq_head3_tail11, processPrekeyInnerInitAt_eq_330_388_rem23]
  refine Entails.trans (show _ ⊢
    preKeyMsgAt A y.g.msgG y.g.msgA (pmOfE m i) ∗
    (cells (y.fut + 0x398#64) 2 ∗ memRegion (y.fut + 0x250#64) 48 ∗ coroUnusedP1At y.fut) ∗
    closStackUnusedP1OkAt sp ∗
    storesAt A y.g.stores StoresGhost.opened ∗
    (ResponderStore.sessionRecordEmptyHeaderAt (y.fut + 0xe0#64) ∗
      memRegion (y.fut + 0x100#64) 336 ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      ((y.fut + 0x390#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 0#8) ∗
      (sp ↦₆₄ 0#64) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ memRegion y.out 48 ∗ A.pool ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗ logOff img ∗ stackAt sp (dpClosSubStack B)) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (preKeyMsgAt_unpack_pathA_ext A y.g.msgG y.g.msgA m i)
    (sepConj_mono (coro_unused_split_p2v1 y.fut)
      (sepConj_mono_left (stack_unused_split_p2v1 sp fp hfp)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun u80 => Entails.sepExists_elim fun u88 =>
    Entails.sepExists_elim fun u90 => Entails.sepExists_elim fun u488 =>
    Entails.sepExists_elim fun b4b0 => Entails.sepExists_elim fun b4f1 =>
    Entails.sepExists_elim fun opkWord => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hopkWord => ?_
  have hdecOk' : DecPkOk₀ W Scope y.g.F y.g.peer.val y.g.me.val (pmOfE m i) :=
    hmsg ▸ hdecOk
  have hstores := storesAt_entails_cliPollStoresKitsAt (A := A) img.base
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
    dsimp only [cliPollStoresKitsAt, stageP2PreAt, pathAInnerFrameExt]
    rw [hdrEq]
    ac_rfl)

/-- Entry spatial unpack from `StageP2PathAQpanCliStmt` into `stageP2PreAt... pathAInnerFrame`. -/
theorem stageP2_entry_unpack_pathA {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (s0 : State)
    (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (hmsg : y.g.msg = pmOfE m i) (hfp : fp = sp + 0xc70#64)
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hFok : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hScope : ∀ r', Scope r' → Slots.scopeIn r') :
    stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
    p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
    preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
    protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
    protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
    coinsInstalled img y.g.coinsP y.g.coins ∗
    storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
    TokenInit img ∗
    logOff img ∗
    stackAt sp (dpClosSubStack B) ⊢
      ∃∗ w : PathAEntryWords,
        ⌜∀ id : BitVec 32, m.opkId = some id → w.opkWord = id⌝ ∗
        stageP2PreAt E2E.HooksE.A0 img
          (cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId (cliKitStk B))
          (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
          (cliPollPkKit E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B))
          (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B))
          s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
          y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
          y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
          (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
          w.opkWord m.kpkId m.regId m.spkId
          StoresGhost.opened.signed StoresGhost.opened.kyber
          StoresGhost.opened.oneTime StoresGhost.opened.identity
          y.g.me y.g.peer (dpClosSubStack B)
          (pathAInnerFrame img y m i rngPtr sp) :=
  stageP2_entry_unpack_pathA_ext img y m i s0 sp fp rngPtr v_a8 v_b8 v_d0
    hmsg hfp hdecOk hFok hScope

/-- Fold Stage P2 error-exit coroutine slots + `pathAInnerFrame` coroutine regions into `dpFutDoneAt`. -/
theorem p2_coro_err_fold (fut msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64) :
    processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
    decryptPrekeyCoroInitAt fut msgPtr remoteAddrPtr localAddrPtr
      sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    ((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
    ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
    coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    memRegion (fut + 0xe0#64) 368 ∗
    cells (fut + 0x250#64) 6 ∗ memRegion (fut + 0x280#64) 24 ∗
    memRegion (fut + 0x298#64) 20 ∗
    memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 ∗
    ((fut + 0x2c0#64) ↦₈ 1#8) ∗
    ((fut + 0x330#64) ↦₆₄ remoteAddrPtr) ∗ ((fut + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
    processPrekeyInnerRem23At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    processPrekeyPostTrustAt fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    ((fut + 0x390#64) ↦₈ 1#8) ∗ memRegion (fut + 0x398#64) 96 ∗
    ((fut + 0x4f1#64) ↦₈ 0#8) ∗ ((fut + 0x4f2#64) ↦₈ 1#8) ∗
    memRegion (fut + 0x2c1#64) 7 ∗ memRegion (fut + 0x391#64) 7 ∗
    memRegion (fut + 0x488#64) 8 ∗ memRegion (fut + 0x4b0#64) 65 ∗
    memRegion (fut + 0x4f3#64) 5 ∗
    p2CoroScratchTailAt fut ∗ memRegion (fut + 0x782#64) 6 ⊢ dpFutDoneAt fut := by
  have h398 : memRegion (fut + 0x398#64) 96 =
      cells (fut + 0x398#64) 2 ∗ memRegion (fut + 0x3a8#64) 80 := by
    rw [memRegion_split (fut + 0x398#64) 16 80 (by decide),
        ProofLib.memRegion_cells (fut + 0x398#64) 2 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h4f8 : p2CoroScratchTailAt fut ∗ memRegion (fut + 0x782#64) 6 =
      memRegion (fut + 0x4f8#64) 736 :=
    (coro_scratch_736_split fut).symm
  have h298 : memRegion (fut + 0x298#64) 20 =
      memRegion (fut + 0x298#64) 8 ∗ memRegion (fut + 0x2a0#64) 8 ∗
      memRegion (fut + 0x2a8#64) 4 := by
    rw [memRegion_split (fut + 0x298#64) 8 12 (by decide),
        memRegion_split (fut + 0x298#64 + 8#64) 8 4 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h398, h298]
  refine Entails.trans (show _ ⊢
    (memRegion (fut + 0x298#64) 8 ∗ memRegion (fut + 0x2a0#64) 8 ∗
      memRegion (fut + 0x2a8#64) 4) ∗
    ((p2CoroScratchTailAt fut ∗ memRegion (fut + 0x782#64) 6) ∗
      processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
      decryptPrekeyCoroInitAt fut msgPtr remoteAddrPtr localAddrPtr
        sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
      ((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
      coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
      memRegion (fut + 0xe0#64) 368 ∗
      cells (fut + 0x250#64) 6 ∗ memRegion (fut + 0x280#64) 24 ∗
      memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 ∗
      ((fut + 0x2c0#64) ↦₈ 1#8) ∗
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
      memRegion (fut + 0x4b0#64) 65 ∗ memRegion (fut + 0x4f3#64) 5)
    by exact Entails.of_eq (by ac_rfl)) ?_
  rw [h4f8]
  refine step_mr8 fun u298 => step_mr8 fun u2a0 => ?_
  rw [memRegion_4_eq_exists_pointsTo32 (fut + 0x2a8#64), sepExists_sepConj_left]
  refine Entails.sepExists_elim fun u2a8 => ?_
  refine Entails.trans ?_ (coro_mismatch_fold fut msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr u298 u2a0 u2a8)
  exact Entails.of_eq (by ac_rfl)

/-- Fold Stage P2 error-exit stack slots + `pathAInnerFrame` stack regions into `memRegion sp 3280`. -/
theorem p2_stack_err_fold (sp fp : BitVec 64) (s0 : State) (hfp : fp = sp + 0xc70#64) :
    (sp ↦₆₄ 0#64) ∗
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
    decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ⊢ memRegion sp 3280 := by
  have h80 : memRegion (sp + 0x80#64) 88 =
      memRegion (sp + 0x80#64) 24 ∗
      memRegion (sp + 0x98#64) 8 ∗ memRegion (sp + 0xa0#64) 8 ∗
      memRegion (sp + 0xa8#64) 8 ∗ memRegion (sp + 0xb0#64) 8 ∗
      memRegion (sp + 0xb8#64) 8 ∗ memRegion (sp + 0xc0#64) 8 ∗
      memRegion (sp + 0xc8#64) 8 ∗ memRegion (sp + 0xd0#64) 8 := by
    rw [memRegion_split (sp + 0x80#64) 24 64 (by decide),
        memRegion_split (sp + 0x80#64 + 24#64) 8 56 (by decide),
        memRegion_split (sp + 0x80#64 + 24#64 + 8#64) 8 48 (by decide),
        memRegion_split (sp + 0x80#64 + 24#64 + 8#64 + 8#64) 8 40 (by decide),
        memRegion_split (sp + 0x80#64 + 24#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
        memRegion_split (sp + 0x80#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
        memRegion_split (sp + 0x80#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
        memRegion_split (sp + 0x80#64 + 24#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h144 : memRegion (sp + 0x8#64) 120 ∗ memRegion (sp + 0x80#64) 24 =
      memRegion (sp + 0x8#64) 144 := by
    rw [memRegion_split (sp + 0x8#64) 120 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h270 : memRegion (sp + 0x270#64) 9 ∗ memRegion (sp + 0x279#64) 39 =
      memRegion (sp + 0x270#64) 48 := by
    rw [memRegion_split (sp + 0x270#64) 9 39 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h3b0 : memRegion (sp + 0x3b0#64) 48 =
      memRegion (sp + 0x3b0#64) 24 ∗ memRegion (sp + 0x3c8#64) 24 := by
    rw [memRegion_split (sp + 0x3b0#64) 24 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h550 := (sp_550_1824_split_p2v1 sp fp hfp).symm
  have hclos := clos_stack_3280_of_regions (sp + 0xcd0#64) s0
  have hsp_sub : sp + 0xcd0#64 - 0xcd0#64 = sp := by bv_omega
  dsimp only at hclos
  rw [hsp_sub] at hclos
  refine Entails.trans ?_ hclos
  rw [h80, h3b0]
  refine Entails.trans (ProofLib.pointsTo64_entails_memRegion sp 0#64 |> sepConj_mono_left) ?_
  exact Entails.of_eq (by
    rw [sp_234_428_split sp, ← h144, ← h270, ← h550]
    ac_rfl)

set_option maxHeartbeats 800000 in
/-- `A`-polymorphic Stage P2 error-exit spatial fold into `StageP2PathAErr`'s postcondition. -/
theorem p2ErrFrame_fold_pathA_ext {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hmsg : y.g.msg = pmOfE m i)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    (decResAt A y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKit A img.base y.g.F m.spkId (cliKitStk B)).storeAt
      (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    (cliPollPkKit A img.base y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B)).identityAt
      y.g.stores StoresGhost.opened.identity ∗
    p2ErrFrameAt A img s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x78#64) (kyberVt img) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrameExt img y m i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt A y.out (.error err) ∗
      storesAt A y.g.stores StoresGhost.opened ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      logOff img ∗
      A.pool ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap := by
  rw [hmsg]
  have hstores := cliPollStoresKitsAt_entails_storesAt (A := A) img.base
    (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
    (pid := w.opkWord) (sid := m.spkId) (kid := m.kpkId) (kbk := (pmOfE m i).baseKey)
    (cliKitStk B) y.g.stores StoresGhost.opened
  have hmsgFold :
      p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtExt A y.g.msgG y.g.msgA m i ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA (pmOfE m i) := by
    refine Entails.trans (p2MsgFields_reassemble_slices_ext A y.g.msgG y.g.msgA m i w.opkWord hopk) ?_
    rw [preKeyMsgAt_eq_base_idKey_sep]
    exact Entails.of_eq (by ac_rfl)
  have hcoro := p2_coro_err_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr
  have hstk := p2_stack_err_fold sp fp s0 hfp
  have hany : coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img ∗ anyHeap ⊢ anyHeap :=
    entails_anyHeap _
  dsimp only [p2ErrFrameAt, pathAInnerFrameExt]
  refine Entails.trans (show _ ⊢
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
      memRegion (y.fut + 0xe0#64) 368 ∗
      cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      memRegion (y.fut + 0x298#64) 20 ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
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
    decResAt A y.out (.error err) ∗
    cliPollStoresKitsAt A img.base y.g.F Slots.scopeKit y.g.peer
      w.opkWord m.spkId m.kpkId (pmOfE m i).baseKey (cliKitStk B) y.g.stores StoresGhost.opened ∗
    (p2MsgFieldsAt y.g.msgA y.g.msgG.kyberPtr (mkPathAHdr m) i.messageVersion
        w.opkWord m.kpkId m.regId m.spkId ∗
      signalMessageRestVerAt A y.g.msgG.msg y.g.msgA i ∗
      pathAMsgRemInnerAtExt A y.g.msgG y.g.msgA m i) ∗
    protocolAddressAt A y.g.peer y.g.peerA ∗
    protocolAddressAt A y.g.me y.g.meA ∗
    logOff img ∗
    A.pool ∗
    stackAt sp (dpClosSubStack B) ∗
    (coinsInstalled img y.g.coinsP y.g.coins ∗ TokenInit img ∗ anyHeap)
    by exact Entails.of_eq (by dsimp only [cliPollStoresKitsAt]; ac_rfl)) ?_
  exact sepConj_mono hcoro (sepConj_mono hstk (sepConj_mono_right
    (sepConj_mono hstores (sepConj_mono hmsgFold
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hany)))))))))

/-- Full Stage P2 error-exit spatial fold into `StageP2PathAErr`'s postcondition. -/
theorem p2ErrFrame_fold_pathA {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (hmsg : y.g.msg = pmOfE m i)
    (hfp : fp = sp + 0xc70#64)
    (hopk : ∀ id : BitVec 32, m.opkId = some id → w.opkWord = id) :
    (decResAt E2E.HooksE.A0 y.out (.error err) ∗ anyHeap) ∗
    (cliPollSpkKit E2E.HooksE.A0 img.base y.g.F m.spkId (cliKitStk B)).storeAt
      (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    (cliPollKpkKit E2E.HooksE.A0 img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B)).storeAt
      (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    (cliPollPkKit E2E.HooksE.A0 img.base y.g.F w.opkWord (cliKitStk B)).storeAt
      (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    (cliPollIdKit E2E.HooksE.A0 img.base y.g.F y.g.peer (cliKitStk B)).identityAt
      y.g.stores StoresGhost.opened.identity ∗
    p2ErrFrameAt E2E.HooksE.A0 img s0 sp fp y.fut y.g.msgA y.g.msgG.kyberPtr
      y.g.peerA y.g.meA y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x78#64) (kyberVt img) y.g.peerA (y.g.msgA + 0xc8#64)
      (mkPathAHdr m) i.messageVersion w.opkWord m.kpkId m.regId m.spkId
      y.g.me y.g.peer (dpClosSubStack B) (pathAInnerFrame img y m i rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      decResAt E2E.HooksE.A0 y.out (.error err) ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      logOff img ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp (dpClosSubStack B) ∗
      anyHeap :=
  p2ErrFrame_fold_pathA_ext img y m i w s0 sp fp rngPtr err hmsg hfp hopk

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
