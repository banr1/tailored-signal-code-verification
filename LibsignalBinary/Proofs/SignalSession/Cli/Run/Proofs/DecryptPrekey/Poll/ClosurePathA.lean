/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP3ExitFold
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll New-Session Path A Spatial and Exit Bridges

Allocator-parametric (`{A : RustAlloc}`) spatial and exit-packaging bridges for new-session Path A
(`opt = none` at `+0x0868`, `trusted = .ok true`), folding Stage P3 error exits and splitting the
Stage P3 `Ok` mid-state (`+0x34dc`) into 4-kit `Kits.stageP4Pre ∗ pathAP4RemAt`.
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
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
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

/-! ## 1. Coroutine `opk_id` Collapse Helper -/

/-- Collapse `coroOpkIdAtP4 coroPtr opkId?` into `memRegion (coroPtr + 0x298#64) 8`. -/
theorem coroOpkIdAtP4_entails_memRegion8 (coroPtr : BitVec 64) (opkId? : Option (BitVec 32)) :
    coroOpkIdAtP4 coroPtr opkId? ⊢ memRegion (coroPtr + 0x298#64) 8 := by
  cases opkId? with
  | none =>
    unfold coroOpkIdAtP4
    exact Entails.sepExists_elim fun u => coro_298_words32_entails_memRegion8 coroPtr 0#32 u
  | some opkId =>
    exact coro_298_words32_entails_memRegion8 coroPtr 1#32 opkId

/-! ## 2. Spatial Fold for Stage P3 `Err` / `verNe` Exits on Path A -/

set_option maxHeartbeats 800000 in
theorem stageP3ErrPathA_entails_exit {A : RustAlloc} (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s2 : State)
    (rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer kpkId spkId : BitVec 32)
    (e : SignalProtocolError) (err : ApiError AddrVal Unit)
    (g1 : StoresGhost)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hmsg_fold :
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg) :
    let sp := s0.sp - 0xcd0#64
    (((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      memRegion (sp + 0x3e0#64) 344 ∗
      stageP3ErrPost A img.base s0 s2 y.fut y.out 8#64 e ∗
      genP3S5PostFrame A img sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
        ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    storesAt A y.g.stores g1 ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
    decResAt A y.out (.error err) ∗
      storesAt A y.g.stores g1 ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗
      A.pool ∗
      (TokenInit img ∗ coinsPost) ∗
      dpFutDoneAt y.fut ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  unfold stageP3ErrPost genP3S5PostFrame stageP3CoroFrameAt stageP3StackFrameAt
  rw [hs2_sp]
  have hlog :
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) =
      logOff img := rfl
  rw [hlog]
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
  have hstk_join :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
      stackAt sp (dpClosSubStack B) := by
    rw [hstk1, hstk2]
  have hdec := recordResultAt_err_entails_decResAt A y.out
    (SessionState.recordError .preKey e) err
  have he0 := coro_e0_3w_344_entails_368 y.fut 0#64 8#64 0#64
  have h298 := coroOpkIdAtP4_entails_memRegion8 y.fut opkId?
  have h2a0 := coro_2a0_2a8_entails y.fut (kpkId ++ 1#32) spkId
  have hsp0 := ProofLib.pointsTo64_entails_memRegion sp 0#64
  have hcoro := stageP3Err_coro_entails_dpFutDoneAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr
  have hstack := stageP3Err_stack_entails_3280 s0
    (y.fut + 0xf8#64) (y.fut + 0xe0#64) (y.g.msgA + 0xc8#64)
    y.g.meA y.g.peerA whisperMsgPtr y.cx y.out y.g.peerA msgVer
  dsimp only at hstack
  refine Entails.trans
    (Entails.of_eq (show _ =
      recordResultAt A y.out (.error (SessionState.recordError .preKey e)) ∗
      storesAt A y.g.stores g1 ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      (signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem) ∗
      logOff img ∗
      A.pool ∗
      (TokenInit img ∗ coinsPost) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
        decryptPrekeyCoroCopyAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
          (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
          (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
        (((y.fut + 0xe0#64) ↦₆₄ 0#64) ∗ ((y.fut + 0xe8#64) ↦₆₄ 8#64) ∗
          ((y.fut + 0xf0#64) ↦₆₄ 0#64) ∗ memRegion (y.fut + 0xf8#64) 344) ∗
        memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗
        coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
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
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack)) ∗
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
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by sep_frame)) ?_
  rw [← coro_2ac_20_eq_8_12 y.fut, coro_2c8_16_184_eq_200 y.fut, hstk_join]
  refine sepConj_mono hdec (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono ?_ (sepConj_mono_right ?_)))))))))
  · refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono he0
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) ?_
    rw [sepConj_assoc (memRegion (y.fut + 0x2a0#64) 8) (memRegion (y.fut + 0x2a8#64) 4)]
    exact hcoro
  · exact Entails.trans (sepConj_mono_left hsp0) hstack

abbrev stageP3ErrPathA_entails_exit_ext := @stageP3ErrPathA_entails_exit

/-! ## 3. Spatial Split & Exit Fold for 4-Kit Stage P4 (`+0x34dc → x30`) on Path A -/

/-- Caller resources framed across 4-kit `Kits.stageP4_v1_vregs_kits_ok` and
`Kits.stageP4_kyber_refused_vregs_kits_ok` (`+0x34dc → s0.readReg64.x30`). -/
def pathAP4RemAt {A : RustAlloc} (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (sp rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (msgVer pid kid spkId : BitVec 32)
    (preKeyMsgRem coinsPost : SepProp) : SepProp :=
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
  coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (signedVt img) rngPtr ∗
  memRegion (y.fut + 0x250#64) 48 ∗
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
  ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
  spLowGapsAt sp ∗
  ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
  ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
  memRegion (sp + 0xbc#64) 4 ∗
  ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
  ((sp + 0xc8#64) ↦₆₄ y.out) ∗
  memRegion (sp + 0xd8#64) 376 ∗
  memRegion (sp + 0x264#64) 12 ∗
  ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
  memRegion (sp + 0x290#64) 16 ∗
  memRegion (sp + 0x2a0#64) 16 ∗
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
  protocolAddressAt A y.g.me y.g.meA ∗
  signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
  preKeyMsgRem ∗
  TokenInit img ∗
  coinsPost ∗
  (cliPollSpkKit A img.base y.g.F spkId (cliKitStk B)).storeAt
    (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
  dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
  memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
    (dpClosSubStack B - stageP4CallStack
      (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
      (cliPollIdKit A img.base y.g.F y.g.peer (cliKitStk B))
      (cliPollPkKit A img.base y.g.F pid (cliKitStk B))
      (cliPollKpkKit A img.base y.g.F kid spkId y.g.msg.baseKey (cliKitStk B)))

abbrev pathAP4RemAtExt := @pathAP4RemAt

/-- When `pkStoreKeys F m = some k` and `m.opkId = some opkId`, `OneTimePreKeyFiles::remove_pre_key`
at `opkId` cannot fail with a read error (`removeRel... (.error e)` is uninhabited). -/
theorem cliPk_removeRel_not_err_of_pkStoreKeys {A : RustAlloc} {b : BitVec 64}
    {F : FsFiles} {m : PreKeyMessageFields} {k : ResponderPreKeySecrets}
    {pid opkId : BitVec 32} {σ : DpKitStk} {e : CliReadErr}
    (hk : pkStoreKeys F m = some k)
    (hopk : m.opkId = some opkId)
    (hrem : (cliPollPkKit A b F pid σ).removeRel StoresGhost.opened.oneTime opkId (.error e)) :
    False := by
  have hrem_err :
      (removePreKey cliIo.rd F StoresGhost.opened.oneTime opkId).1 = .error () := by
    simpa [cliPollPkKit, cliPreKeyStoreSpec] using hrem
  have hd_err :
      StoresGhost.opened.oneTime.get cliIo.rd F (keyName opkId) = .error () := by
    unfold removePreKey at hrem_err
    rcases hg : StoresGhost.opened.oneTime.get cliIo.rd F (keyName opkId) with _ | (_ | ⟨_, _⟩)
    · rfl
    · rw [hg] at hrem_err; cases hrem_err
    · rw [hg] at hrem_err; cases hrem_err
  have hget_err :
      getPreKey cliIo.rd F StoresGhost.opened.oneTime opkId = .error () := by
    unfold getPreKey
    rw [hd_err]
    rfl
  have hk_none : pkStoreKeys F m = none := by
    clear hk
    dsimp only [pkStoreKeys]
    rcases getSignedPreKey cliIo.rd F StoresGhost.opened.signed m.spkId with _ | sr <;>
      rcases StoresGhost.opened.kyber.get cliIo.rd F m.kpkId with _ | kr <;> try rfl
    dsimp only
    rcases pkVec? 32 sr.signedPreKey.privateKey with _ | spk <;>
      rcases pkVecTag? 8 1568 kr.signedPreKey.publicKey with _ | kpub <;>
      rcases pkVecTag? 8 3168 kr.signedPreKey.privateKey with _ | ksec <;> try rfl
    dsimp only
    rw [hopk]
    dsimp only
    rw [hget_err]
    rfl
  rw [hk_none] at hk
  cases hk

set_option maxHeartbeats 800000 in
theorem stageP3MidPathA_eq_p4 {A : RustAlloc} (img : Obj.Image) (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s2 s' : State)
    (rngPtr initErrsPtr prevStatesPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32)
    (pt : List (BitVec 8))
    (G' : SessionGhost) (st' : SessionState (List (BitVec 8)))
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    let pkKit := cliPollPkKit A img.base y.g.F pid σ
    let spkKit := cliPollSpkKit A img.base y.g.F spkId σ
    let kpkKit := cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ
    (stageP3DispatchOkMid A img.base s0 s2 y.fut y.out initErrsPtr prevStatesPtr
        ptCap ptPtr pt 0#8 G' st' ∗
      genP3S5PostFrame A img sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
      (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
      (y.g.stores + 0x78#64) (kyberVt img) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) =
    Kits.stageP4Pre img kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      prevStatesPtr ptCap ptPtr initErrsPtr
      opkId? kpkId spkId 0#8 pt
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey
      StoresGhost.opened.sessions StoresGhost.opened.identity
      StoresGhost.opened.oneTime StoresGhost.opened.kyber
      G' st' ∗
    pathAP4RemAt img B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId preKeyMsgRem coinsPost := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  have hlog :
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) =
      logOff img := rfl
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
    (cliPollStageP4Stack_le_subStack A img.base y.g.F Slots.scopeKit y.g.peer
      pid kpkId spkId y.g.msg.baseKey B)
    hsp_sub
  have hstk_swap :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
        (dpClosSubStack B - stageP4CallStack
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKit A img.base y.g.F y.g.peer σ)
          (cliPollPkKit A img.base y.g.F pid σ)
          (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
        stackAt sp (stageP4CallStack
          (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
          (cliPollIdKit A img.base y.g.F y.g.peer σ)
          (cliPollPkKit A img.base y.g.F pid σ)
          (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) := by
    rw [hstk1, hstk2, hstk3]
  unfold stageP3DispatchOkMid genP3S5PostFrame stageP3CoroFrameAt stageP3StackFrameAt
    Kits.stageP4Pre Kits.stageP4RawPre Kits.stageP4Shared pathAP4RemAt
  rw [hs2_sp, hs'_sp, hlog,
      coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr,
      sp_2b0_192_split sp, sp_3e0_344_eq_48_296 sp,
      sessVt_eq_cliPollSessKit A img y.g.F Slots.scopeKit y.g.peer σ,
      idVt_eq_cliPollIdKit A img y.g.F y.g.peer σ,
      oneTimeVt_eq_cliPollPkKit A img y.g.F pid σ,
      kyberVt_eq_cliPollKpkKit A img y.g.F kpkId spkId y.g.msg.baseKey σ]
  have hswap_all :
      ∀ (Rest : SepProp),
        (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
          (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
            stackAt sp growOneSpeStack)) ∗ Rest =
        (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
          (dpClosSubStack B - stageP4CallStack
            (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKit A img.base y.g.F y.g.peer σ)
            (cliPollPkKit A img.base y.g.F pid σ)
            (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ)) ∗
          stackAt sp (stageP4CallStack
            (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ)
            (cliPollIdKit A img.base y.g.F y.g.peer σ)
            (cliPollPkKit A img.base y.g.F pid σ)
            (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗ Rest := by
    intro Rest; rw [hstk_swap]
  trans ((memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack)) ∗
    (((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗
      ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗
      ((y.fut + 0x90#64) ↦₆₄ (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ).ss_vt) ∗
      ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗
      ((y.fut + 0xa0#64) ↦₆₄ (cliPollIdKit A img.base y.g.F y.g.peer σ).id_vt) ∗
      ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗
      ((y.fut + 0xb0#64) ↦₆₄ (cliPollPkKit A img.base y.g.F pid σ).pk_vt) ∗
      ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗
      ((y.fut + 0xd0#64) ↦₆₄ (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt) ∗
      ((y.fut + 0xe0#64) ↦₆₄ 0#64) ∗
      ((y.fut + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
      ((y.fut + 0xf0#64) ↦₆₄ 0#64) ∗
      ((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗
      ((y.fut + 0x2a8#64) ↦₃₂ spkId) ∗
      memRegion (y.fut + 0x2c8#64) 16 ∗
      ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0x250#64) 20 ∗
      ((sp + 0x278#64) ↦₆₄ ptCap) ∗
      ((sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
      memRegion (sp + 0x2b0#64) 36 ∗
      memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗
      memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
      ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x3e0#64) 48 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      logOff img ∗
      A.pool ∗
      sessionStateAt A (y.fut + 0xf8#64) G' st' ∗
      memRegion (y.fut + 0x280#64) 24 ∗
      coroOpkIdAtP4 y.fut opkId? ∗
      (memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12) ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗
      (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion y.out 48 ∗
      (cliPollIdKit A img.base y.g.F y.g.peer σ).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      (cliPollPkKit A img.base y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ).ss_vt
        y.g.stores (cliPollIdKit A img.base y.g.F y.g.peer σ).id_vt
        (y.g.stores + 0xc8#64) (cliPollPkKit A img.base y.g.F pid σ).pk_vt
        (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (cliPollKpkKit A img.base y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt
        rngPtr ∗
      coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (signedVt img) rngPtr ∗
      memRegion (y.fut + 0x250#64) 48 ∗
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
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
      spLowGapsAt sp ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗
      ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
      memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗
      ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      memRegion (sp + 0xd8#64) 376 ∗
      memRegion (sp + 0x264#64) 12 ∗
      ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
      memRegion (sp + 0x290#64) 16 ∗
      memRegion (sp + 0x2a0#64) 16 ∗
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
      protocolAddressAt A y.g.me y.g.meA ∗
      signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
      preKeyMsgRem ∗
      TokenInit img ∗
      coinsPost ∗
      (cliPollSpkKit A img.base y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub))
  · sep_frame
  · rw [← coro_2ac_20_eq_8_12 y.fut, hswap_all]; sep_frame

abbrev stageP3MidPathA_eq_p4_ext := @stageP3MidPathA_eq_p4

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
