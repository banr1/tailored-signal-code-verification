/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4Spatial
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseStepsBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.ClosureOver
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize

/-!
# Placed CLI Poll Overwrite-Path (`Path C`) Stage P4 Spatial Bridges

Relocatable (`[LibsignalPlacement]`) counterpart of `Over/PollOverP4Spatial.lean`, proving
`pathC_recPrev1Ok_of_tryDecrypt_placed` and `cliPollPrev1StoresKitsAtPlaced_entails_storesAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
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

/-! ## 1. Placed `RecPrev1Ok` Bound (`pathC_recPrev1Ok_of_tryDecrypt_placed`) -/

theorem pathC_recPrev1Ok_of_tryDecrypt_placed [LibsignalPlacement] {A : RustAlloc}
    {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {σ : DpKitStk}
    {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {s_old : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {G' : SessionGhost} {ss : BitVec 64} {Rest : SepProp} {mem : Memory}
    (hs_old : Slots.scopeIn ⟨some s_old⟩)
    (hd : DecPkOkD2c W Scope F peer.val me.val pm)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hex' : SessionExtraRel G'
      { pathAInitSession W ⟨kp.privateKey.bytes, reg⟩ k m dk with
        state := (genP3S5Model W.C W.Q.K peer me pm.message coins
          (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
        pendingPreKey := none
        pendingKyberPreKey := none })
    (hmem : mem ⊨ sessionStateAt A ss G'
      (genP3S5Model W.C W.Q.K peer me pm.message coins
        (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗ Rest) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins (pathAInitState W meE k m dk)).2
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    (cliPollStorePrev1OpsPlaced (A := A) (F0 := F) (peer := peer) (σ := σ)).RecPrev1Ok
      G' ses' (E2E.Record.encSession (Over.clearPending s_old)) :=
  pathC_recPrev1Ok_of_tryDecrypt (b := 0#64) (σ := σ) hs_old hd hver hok hex' hmem

/-! ## 2. Placed `Prev1` Stores Entailment (`cliPollPrev1StoresKitsAtPlaced_entails_storesAt`) -/

theorem cliPollPrev1StoresKitsAtPlaced_entails_storesAt [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (peer : AddrGhost) (pid spkId kpkId : BitVec 32) (kbk : PublicKey)
    (σ : DpKitStk) (ptr : BitVec 64) (g : StoresGhost) :
    (cliPollSessPrev1KitPlaced A F0 peer σ).storeAt (ptr + 0xf0#64) g.sessions ∗
    (cliPollIdKitPlaced A F0 peer σ).identityAt ptr g.identity ∗
    (cliPollPkKitPlaced A F0 pid σ).storeAt (ptr + 0xc8#64) g.oneTime ∗
    (cliPollSpkKitPlaced A F0 spkId σ).storeAt (ptr + 0x50#64) g.signed ∗
    (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ).storeAt (ptr + 0x78#64) g.kyber ∗
    dirAt A (ptr + 0x118#64) g.pub ⊢
    storesAt A ptr g :=
  cliPollPrev1StoresKitsAt_entails_storesAt 0#64 F0 peer pid spkId kpkId kbk σ ptr g

/-! ## 3. Placed GenP3 / Exit / Stage P4 Frame Definitions -/

def overGenP3CallFrame_placed (A : RustAlloc) [LibsignalPlacement] (sp : BitVec 64)
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
    Coins.coinsAtPlaced cur rest ∗
    FromRecordCallees.lsLogOff ∗
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)

def overGenP3Pre_placed (A : RustAlloc) [LibsignalPlacement] (sp fp coroPtr ctxPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32)
    (rest : List (BitVec 8)) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
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
    overGenP3CallFrame_placed A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc
      msgG msg ∗
    genP3SpillAll sp

def overGenP3S5PostFrame_placed (A : RustAlloc) [LibsignalPlacement]
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64) (msgVer : BitVec 32)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) : SepProp :=
  LsTokenInit ∗
    ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
    ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
    ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
    ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
    ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
    protocolAddressAt A rem remAddrPtr ∗
    protocolAddressAt A loc locAddrPtr ∗
    signalMessageAt A msgG whisperMsgPtr msg ∗
    coinsPost ∗
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
    genP3S5SpillRem sp

def overStageP3ErrPostPrevEmpty_placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr : BitVec 64) (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  FromRecordCallees.lsLogOff ∗
  recordResultAt A outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

def overPathAP4RemAtPlaced [LibsignalPlacement] (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (sp rngPtr whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (msgVer pid kid spkId : BitVec 32)
    (preKeyMsgRem coinsPost : SepProp) : SepProp :=
  decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
    (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
    (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
  coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) rngPtr ∗
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
  protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
  signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
  preKeyMsgRem ∗
  LsTokenInit ∗
  coinsPost ∗
  (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F spkId (cliKitStk B)).storeAt
    (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
  dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
  memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B))
    (dpClosSubStack B - stageP4CallStack
      (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer (cliKitStk B))
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B))
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid (cliKitStk B))
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid spkId y.g.msg.baseKey (cliKitStk B)))

theorem overStackAt_poll_exit_join (sp0 : BitVec 64) (B : RunBudgets) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63) :
    memRegion (sp0 - 0xcd0#64) 3280 ∗
      stackAt (sp0 - 0xcd0#64) (dpClosSubStack B) ∗
      memRegion (sp0 - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
    stackAt sp0 stk' := by
  rw [stackAt_poll_entry_split sp0 B stk' hneed hstk63]
  sep_frame

theorem overExit_entails_dpPollPost_placed [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 sf : State)
    (g' : StoresGhost) (res : Except (ApiError AddrVal Unit) E2E.Bytes)
    (Leftover : SepProp)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hsteps : Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' res s0.trace sf.trace) :
    let sp := s0.sp - 0xcd0#64
    decResAt E2E.HooksE.A0 y.out res ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗
      E2E.HooksE.A0.pool ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      memRegion sp 3280 ∗
      stackAt sp (dpClosSubStack B) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ⊢
      (StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk')).post y s0 sf := by
  dsimp only
  have hstk_back := overStackAt_poll_exit_join s0.sp B stk' hneed hstk63
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right hstk_back)))))))))) ?_
  exact dpPollPost_of_decResAt_placed B S stk' y s0 sf g' res Leftover hh hsteps htr hout

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
theorem stageP3MidPathC_entails_p4_placed [LibsignalPlacement] (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S))
    (s0 s2 s' : State)
    (rngPtr initErrsPtr prevCap prevPtr whisperMsgPtr ptCap ptPtr : BitVec 64)
    (whisperG : SignalMessageGhost)
    (preKeyMsgRem coinsPost : SepProp)
    (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32)
    (enc pt : List (BitVec 8))
    (G' : SessionGhost) (st' : SessionState (List (BitVec 8)))
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
    let prev1Kit := cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
    let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F spkId σ
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ
    (Over.stageP3DispatchOkMidPrev1Placed E2E.HooksE.A0 s0 s2 y.fut y.out initErrsPtr
        prevCap prevPtr ptCap ptPtr enc pt 0#8 G' st' ∗
      overGenP3S5PostFrame_placed E2E.HooksE.A0 sp y.fut y.cx y.g.peerA y.g.meA whisperMsgPtr msgVer
        y.g.peer y.g.me whisperG y.g.msg.message coinsPost ∗
      Over.overScratch s2.sp) ∗
    stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
      (coroOpkIdAtP4 y.fut opkId?)
      (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
    stageP3OverStackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
    ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
    ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
    preKeyMsgRem ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ⊢
    Over.stageP4Prev1PrePlaced 0#64 prev1Kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.out y.g.peerA (y.g.msgA + 0xc8#64)
      (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64)
      prevCap prevPtr ptCap ptPtr initErrsPtr
      opkId? kpkId spkId 0#8 pt enc
      y.g.peer y.g.msg.identityKey y.g.msg.baseKey
      StoresGhost.opened.sessions StoresGhost.opened.identity
      StoresGhost.opened.oneTime StoresGhost.opened.kyber
      G' st' ∗
    overPathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId
      preKeyMsgRem coinsPost := by
  dsimp only
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left
          (cliPollSessKit_storeAt_entails_prev1 (A := E2E.HooksE.A0) (b := 0#64)
            (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer) (σ := cliKitStk B)
            (y.g.stores + 0xf0#64) StoresGhost.opened.sessions)))))))) ?_
  unfold Over.stageP3DispatchOkMidPrev1Placed overGenP3S5PostFrame_placed stageP3CoroFrameAt
    stageP3OverStackFrameAt Over.stageP4Prev1PrePlaced Over.stageP4Prev1RawPrePlaced
    Over.stageP4Prev1SharedPlaced overPathAP4RemAtPlaced
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  have hstk1 : memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      stackAt sp growOneSpeStack = stackAt sp rootStack :=
    (stackAt_root_sub_eq sp (by decide)).symm
  have hstk2 : memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      stackAt sp rootStack = stackAt sp (dpClosSubStack B) :=
    (stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub).symm
  have hstk3 := stackAt_subStack_sub_eq sp B
    (cliPollStageP4Stack_le_subStack E2E.HooksE.A0 0#64 y.g.F Slots.scopeKit y.g.peer
      pid kpkId spkId y.g.msg.baseKey B) hsp_sub
  have hstk_swap :
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack) =
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
          (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ)) := by
    rw [hstk1, hstk2]; exact hstk3
  have hvt_s : (cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hvt_i : (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hvt_p : (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).pk_vt =
      lsρ cliPreKeyVtSym := rfl
  have hvt_k : (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt =
      lsρ cliKyberPreKeyVtSym := rfl
  have hcall_eq :
      stageP4CallStack
        (cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
        (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
        (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ)
        (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ) =
      stageP4CallStack
        (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
        (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ)
        (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ) := rfl
  rw [hs2_sp, hs'_sp, hvt_s, hvt_i, hvt_p, hvt_k, hcall_eq,
      overScratch_eq_sp538_spHighGaps sp, coro_2ac_20_eq_8_12 y.fut,
      coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr,
      sp_2b0_192_split sp, sp_3e0_344_eq_48_296 sp]
  apply Entails.of_eq
  have hswap_all : ∀ (Rest : SepProp),
      (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
          stackAt sp growOneSpeStack)) ∗ Rest =
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
          (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ))) ∗ Rest := by
    intro Rest; rw [hstk_swap]
  trans ((memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
      (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
        stackAt sp growOneSpeStack)) ∗
    (((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗
      ((y.fut + 0x90#64) ↦₆₄ (lsρ cliSessionVtSym)) ∗
      ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗
      ((y.fut + 0xa0#64) ↦₆₄ (lsρ cliIdentityVtSym)) ∗
      ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗
      ((y.fut + 0xb0#64) ↦₆₄ (lsρ cliPreKeyVtSym)) ∗
      ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗
      ((y.fut + 0xd0#64) ↦₆₄ (lsρ cliKyberPreKeyVtSym)) ∗
      prevVecAt E2E.HooksE.A0 (y.fut + 0xe0#64) prevCap prevPtr [enc] ∗
      ((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId) ∗
      memRegion (y.fut + 0x2c8#64) 16 ∗ ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0x250#64) 20 ∗
      ((sp + 0x278#64) ↦₆₄ ptCap) ∗ ((sp + 0x280#64) ↦₆₄ ptPtr) ∗
      ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
      ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x3e0#64) 48 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ E2E.HooksE.A0.pool ∗
      sessionStateAt E2E.HooksE.A0 (y.fut + 0xf8#64) G' st' ∗
      memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
      (memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12) ∗
      ((y.fut + 0x2c0#64) ↦₈ 0#8) ∗ (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else E2E.HooksE.A0.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
      memRegion y.out 48 ∗
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).identityAt
        y.g.stores StoresGhost.opened.identity ∗
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).storeAt
        (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      (cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).storeAt
        (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym)
        y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym)
        (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
      coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) rngPtr ∗
      memRegion (y.fut + 0x250#64) 48 ∗ memRegion (y.fut + 0x2d8#64) 184 ∗
      memRegion (y.fut + 0x390#64) 1 ∗ memRegion (y.fut + 0x398#64) 16 ∗
      memRegion (y.fut + 0x428#64) 64 ∗ memRegion (y.fut + 0x468#64) 40 ∗
      memRegion (y.fut + 0x490#64) 32 ∗ memRegion (y.fut + 0x4f2#64) 1 ∗
      coroPostP2UnusedAt y.fut ∗ (sp ↦₆₄ 0#64) ∗ genP3S5SpillRem sp ∗
      memRegion (sp + 0x930#64) 48 ∗ ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗
      ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗ spLowGapsAt sp ∗
      ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((sp + 0xb8#64) ↦₃₂ msgVer) ∗ memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
      memRegion (sp + 0xd8#64) 376 ∗ memRegion (sp + 0x264#64) 12 ∗
      ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
      memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 16 ∗ sp2b0GapsAt sp ∗
      memRegion (sp + 0x394#64) 12 ∗ ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗
      memRegion (sp + 0x3a8#64) 4 ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗
      memRegion (sp + 0x3ad#64) 27 ∗ memRegion (sp + 0x410#64) 296 ∗
      memRegion (sp + 0x538#64) 24 ∗ memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
      preKeyMsgRem ∗ LsTokenInit ∗ coinsPost ∗
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub))
  · sep_frame
  · rw [hswap_all]; sep_frame

set_option maxRecDepth 200000 in
set_option maxHeartbeats 800000 in
theorem stageP4PathCExit_entails_exit_placed [LibsignalPlacement] (B : RunBudgets) {S : RunSem}
    (y : DpPollGhostState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S)) (s0 s' : State)
    (rngPtr initErrsPtr whisperMsgPtr ptCap ptPtr : BitVec 64) (whisperG : SignalMessageGhost)
    (outSlot preKeyMsgRem coinsPost : SepProp) (opkId? : Option (BitVec 32))
    (msgVer pid kpkId spkId : BitVec 32) (pt : List (BitVec 8))
    (res : Except (ApiError AddrVal Unit) E2E.Bytes)
    (sstf pstf : DirGhost) (istf : IdGhost) (kstf : KyberGhost) (g' : StoresGhost)
    (hs'_sp : s'.sp = s0.sp - 0xcd0#64) (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hout : outSlot ⊢ decResAt E2E.HooksE.A0 y.out res ∗ anyHeap)
    (hmsg_fold :
      signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
    (hsess : g'.sessions = sstf) (hid : g'.identity = istf) (hot : g'.oneTime = pstf)
    (hspk : g'.signed = StoresGhost.opened.signed) (hkpk : g'.kyber = kstf)
    (hpub : g'.pub = StoresGhost.opened.pub) :
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let prev1Kit := cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ
    Over.stageP4Prev1ExitAtPlaced 0#64 prev1Kit ikit pkKit kpkKit s0 s'
      y.fut y.g.msgA y.g.peerA (y.g.msgA + 0xc8#64) (y.g.stores + 0xf0#64) y.g.stores
      (y.g.stores + 0xc8#64) (y.g.stores + 0x78#64) ptCap ptPtr initErrsPtr
      (coroOpkIdAtP4 y.fut opkId?) outSlot kpkId spkId pt y.g.peer y.g.msg.identityKey
      y.g.msg.baseKey sstf istf pstf kstf ∗
    overPathAP4RemAtPlaced B y sp rngPtr whisperMsgPtr whisperG msgVer pid kpkId spkId
      preKeyMsgRem coinsPost ⊢
    decResAt E2E.HooksE.A0 y.out res ∗ storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗ (LsTokenInit ∗ coinsPost ∗ anyHeap) ∗
      dpFutDoneAt y.fut ∗ stackAt sp (dpClosSubStack B) ∗ memRegion sp 3280 := by
  dsimp only
  unfold Over.stageP4Prev1ExitAtPlaced Over.stageP4Prev1SharedPlaced overPathAP4RemAtPlaced
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  have hvt_s : (cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).ss_vt =
      lsρ cliSessionVtSym := rfl
  have hvt_i : (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).id_vt =
      lsρ cliIdentityVtSym := rfl
  have hvt_p : (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).pk_vt =
      lsρ cliPreKeyVtSym := rfl
  have hvt_k : (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ).kpk_vt =
      lsρ cliKyberPreKeyVtSym := rfl
  have hcall_eq :
      stageP4CallStack (cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
        (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
        (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ)
        (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ) =
      stageP4CallStack (cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ)
        (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ)
        (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ)
        (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ) := rfl
  rw [hs'_sp, hvt_s, hvt_i, hvt_p, hvt_k, hcall_eq]
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
      (cliPollStageP4Stack_le_subStack E2E.HooksE.A0 0#64 y.g.F Slots.scopeKit y.g.peer
        pid kpkId spkId y.g.msg.baseKey B) hsp_sub).symm
  have hstores :
      (cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).storeAt (y.g.stores + 0xf0#64) sstf ∗
      (cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).identityAt y.g.stores istf ∗
      (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).storeAt (y.g.stores + 0xc8#64) pstf ∗
      (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F spkId σ).storeAt
        (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
      (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kpkId spkId y.g.msg.baseKey σ).storeAt
        (y.g.stores + 0x78#64) kstf ∗
      dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ⊢
      storesAt E2E.HooksE.A0 y.g.stores g' := by
    rw [← hsess, ← hid, ← hot, ← hspk, ← hkpk, ← hpub]
    exact cliPollPrev1StoresKitsAtPlaced_entails_storesAt y.g.F y.g.peer pid spkId kpkId
      y.g.msg.baseKey σ y.g.stores g'
  have hcopy_join :=
    (coroCopy_eq_p4_sep y.fut y.g.msgA y.g.peerA y.g.meA
      (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
      (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
      (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr).symm
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
      ((cliPollSessPrev1KitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ).storeAt (y.g.stores + 0xf0#64) sstf ∗
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
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      E2E.HooksE.A0.pool ∗
      (LsTokenInit ∗ coinsPost) ∗
      (decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr ∗
        ((((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
          ((y.fut + 0x88#64) ↦₆₄ (y.g.stores + 0xf0#64)) ∗ ((y.fut + 0x90#64) ↦₆₄ (lsρ cliSessionVtSym)) ∗
          ((y.fut + 0x98#64) ↦₆₄ y.g.stores) ∗ ((y.fut + 0xa0#64) ↦₆₄ (lsρ cliIdentityVtSym)) ∗
          ((y.fut + 0xa8#64) ↦₆₄ (y.g.stores + 0xc8#64)) ∗ ((y.fut + 0xb0#64) ↦₆₄ (lsρ cliPreKeyVtSym)) ∗
          ((y.fut + 0xc8#64) ↦₆₄ (y.g.stores + 0x78#64)) ∗ ((y.fut + 0xd0#64) ↦₆₄ (lsρ cliKyberPreKeyVtSym))) ∗
          coroCopyRemP4At y.fut y.g.meA (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym) rngPtr) ∗
        memRegion (y.fut + 0xe0#64) 368 ∗ memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        (memRegion (y.fut + 0x2c8#64) 16 ∗ memRegion (y.fut + 0x2d8#64) 184) ∗
        memRegion (y.fut + 0x390#64) 1 ∗ memRegion (y.fut + 0x398#64) 16 ∗
        memRegion (y.fut + 0x428#64) 64 ∗ memRegion (y.fut + 0x468#64) 40 ∗
        memRegion (y.fut + 0x490#64) 32 ∗ memRegion (y.fut + 0x4f2#64) 1 ∗
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
      ((sp ↦₆₄ 0#64) ∗ genP3S5SpillRem sp ∗ memRegion (sp + 0x930#64) 48 ∗
        ((sp + 0x80#64) ↦₆₄ (y.fut + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (y.fut + 0xe0#64)) ∗
        ((sp + 0x90#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗ spLowGapsAt sp ∗
        ((sp + 0xa0#64) ↦₆₄ y.g.meA) ∗ ((sp + 0xa8#64) ↦₆₄ y.g.peerA) ∗
        ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
        memRegion (sp + 0xbc#64) 4 ∗ ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗
        memRegion (sp + 0xd8#64) 376 ∗ memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x264#64) 12 ∗
        ((sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp + 0x278#64) ↦₆₄ ptCap) ∗
        ((sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
        memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 16 ∗
        memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
        memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ sp2b0GapsAt sp ∗
        memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x394#64) 12 ∗
        ((sp + 0x3a0#64) ↦₆₄ y.g.peerA) ∗ memRegion (sp + 0x3a8#64) 4 ∗
        ((sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (sp + 0x3ad#64) 27 ∗
        ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x3e0#64) 48 ∗
        memRegion (sp + 0x410#64) 296 ∗ memRegion (sp + 0x538#64) 24 ∗
        memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
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
        memRegion (y.fut + 0xe0#64) 368 ∗ memRegion (y.fut + 0x250#64) 48 ∗
        memRegion (y.fut + 0x280#64) 24 ∗ coroOpkIdAtP4 y.fut opkId? ∗
        (((y.fut + 0x2a0#64) ↦₆₄ (kpkId ++ 1#32)) ∗ ((y.fut + 0x2a8#64) ↦₃₂ spkId)) ∗
        memRegion (y.fut + 0x2ac#64) 20 ∗ ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
        memRegion (y.fut + 0x2c8#64) 200 ∗ memRegion (y.fut + 0x390#64) 1 ∗
        memRegion (y.fut + 0x398#64) 16 ∗ memRegion (y.fut + 0x428#64) 64 ∗
        memRegion (y.fut + 0x468#64) 40 ∗ memRegion (y.fut + 0x490#64) 32 ∗
        memRegion (y.fut + 0x4f2#64) 1 ∗ coroPostP2UnusedAt y.fut) ⊢
      dpFutDoneAt y.fut := by
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h298 (sepConj_mono_left h2a0))))))) ?_
    rw [sepConj_assoc (memRegion (y.fut + 0x2a0#64) 8) (memRegion (y.fut + 0x2a8#64) 4)]
    exact hcoro
  have hstack_fold := Entails.trans (sepConj_mono_left hsp0) hstack
  exact Entails.trans
    (sepConj_mono hout (sepConj_mono hstores (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hmsg_fold (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hcoro_fold (sepConj_mono_right hstack_fold))))))))))
    (Entails.of_eq (by dsimp only [FromRecordCallees.lsLogOff]; sep_frame))

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
