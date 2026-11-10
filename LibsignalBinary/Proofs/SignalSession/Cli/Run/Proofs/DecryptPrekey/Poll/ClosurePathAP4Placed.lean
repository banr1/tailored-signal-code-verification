/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Poll New-Session Path A Stage P4 Exit Fold

Proves `stageP4PathAExit_entails_exit_placed`, folding `stageP4ExitAtPlaced` and
`pathAP4RemAtPlaced` for both the `.ok pt` and `.kyberMarkErr` arms of Path A Stage P4.
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
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
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

set_option maxHeartbeats 800000 in
theorem stageP4PathAExit_entails_exit_placed [LibsignalPlacement] (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 s' : State)
    (rngPtr initErrsPtr prevStatesPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (outSlot preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32)
    (pt : List (BitVec 8))
    (res : Except (ApiError AddrVal Unit) E2E.Bytes)
    (sstf pstf : DirGhost) (istf : IdGhost) (kstf : KyberGhost) (g' : StoresGhost)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout : outSlot ⊢ decResAt E2E.HooksE.A0 y.out res ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sstf)
    (hid : g'.identity = istf)
    (hot : g'.oneTime = pstf)
    (hspk : g'.signed = StoresGhost.opened.signed)
    (hkpk : g'.kyber = kstf)
    (hpub : g'.pub = StoresGhost.opened.pub) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ
    stageP4ExitAtPlaced kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      prevStatesPtr ptCap ptPtr initErrsPtr
      (coroOpkIdAtP4 y.fut opkId?) outSlot
      kpkId spkId pt y.g.peer y.g.msg.identityKey y.g.msg.baseKey
      sstf istf pstf kstf ∗
    pathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId preKeyMsgRem coinsPost ⊢
    decResAt E2E.HooksE.A0 y.out res ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  unfold stageP4ExitAtPlaced stageP4SharedPlaced pathAP4RemAtPlaced
  rw [hs'_sp]
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
          (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ)
          (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
      stackAt sp (stageP4CallStack
        (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
        (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ)
        (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ)) =
      stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B
      (cliPollStageP4Stack_placed_le_subStack E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer
        pid kpkId spkId y.g.msg.baseKey B)
      hsp_sub).symm
  have hstores :
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) sstf ∗
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) pstf ∗
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) kstf ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
      storesAt E2E.HooksE.A0 y.g.stores g' := by
    rw [← hsess, ← hid, ← hot, ← hspk, ← hkpk, ← hpub]
    exact cliPollStoresKitsAtPlaced_entails_storesAt σ y.g.stores g'
  have hss_vt :
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hid_vt :
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hpk_vt :
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).pk_vt =
      lsρ cliPreKeyVtSym := rfl
  have hkpk_vt :
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt =
      lsρ cliKyberPreKeyVtSym := rfl
  have hcopy_join :=
    (coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr).symm
  rw [hss_vt, hid_vt, hpk_vt, hkpk_vt]
  have he0 := coro_e0_3w_344_entails_368 y.fut 0#64 prevStatesPtr 0#64
  have h298 := coroOpkIdAtP4_entails_memRegion8 y.fut opkId?
  have h2a0 := coro_2a0_2a8_entails y.fut (kpkId ++ 1#32) spkId
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hstack := stageP4Exit_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA
    0xfffffffffffffffe#64 ptCap ptPtr (BitVec.ofNat 64 pt.length) 0#64 initErrsPtr 0#64 msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      outSlot ∗
      ((cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ).storeAt
          (y.g.stores + 0xf0#64) sstf ∗
        (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
        (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).storeAt
          (y.g.stores + 0xc8#64) pstf ∗
        (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F spkId σ).storeAt
          (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
        (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
          (y.g.stores + 0x78#64) kstf ∗
        dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub) ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      (signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
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
          ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗
          ((y.fut + 0xb0#64) ↦₆₄ (lsρ cliPreKeyVtSym)) ∗
          ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗
          ((y.fut + 0xd0#64) ↦₆₄ (lsρ cliKyberPreKeyVtSym))) ∗
          coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) rngPtr) ∗
        (((y.fut + 0xe0#64) ↦₆₄ 0#64) ∗ ((y.fut + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((y.fut + 0xf0#64) ↦₆₄ 0#64) ∗ memRegion (y.fut + 0xf8#64) 344) ∗
        memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗
        coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗
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
          (dpClosSubStack B - stageP4CallStack
            (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
            (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ)
            (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
          (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ)
          (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗
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
        ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
        memRegion (sp + 0x3e0#64) 48 ∗
        memRegion (sp + 0x410#64) 296 ∗
        memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗
        spHighGapsAt sp ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by sep_frame)) ?_
  rw [hcopy_join, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  have hcoro_fold :
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        (((y.fut + 0xe0#64) ↦₆₄ 0#64) ∗ ((y.fut + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((y.fut + 0xf0#64) ↦₆₄ 0#64) ∗ memRegion (y.fut + 0xf8#64) 344) ∗
        memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗
        coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗
        ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        memRegion (y.fut + 0x2c8#64) 200 ∗
        memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗
        coroPostP2UnusedAt y.fut) ⊢
      dpFutDoneAt y.fut := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono he0
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) ?_
    rw [sepConj_assoc (memRegion (y.fut + 0x2a0#64) 8) (memRegion (y.fut + 0x2a8#64) 4)]
    exact hcoro
  have hstack_fold := Entails.trans (sepConj_mono_left hsp0) hstack
  exact Entails.trans
    (sepConj_mono hout (sepConj_mono hstores (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hcoro_fold (sepConj_mono_right hstack_fold))))))))))
    (Entails.of_eq (by sep_frame))

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
