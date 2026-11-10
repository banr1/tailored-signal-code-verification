/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Poll Stage P2 and Stage P3 Interfaces

Defines `[LibsignalPlacement]` Stage P3 spatial frames (`genP3Pre_placed`,
`stageP3DispatchOkMid_placed`, `stageP3ErrPost_placed`), `CliTryDecryptPqV1PlacedStmt`, and
`StageP3PrevEmptyVRegsPlacedStmt` / `StageP3GenStepsVRegsPlacedStmt` (plus `LibsignalFrozen`
variants).
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
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem cliPollStageP2Stack_placed_le_subStack [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (peer : AddrGhost) (pid sid kid ksid : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2CallStack
      (cliPollSpkKitPlaced A F0 sid (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kid ksid kbk (cliKitStk B))
      (cliPollPkKitPlaced A F0 pid (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  cliPollStageP2Stack_le_subStack A 0#64 F0 peer pid sid kid ksid kbk B

/-- Relocatable `[LibsignalPlacement]` `genP3CallFrame` (`coinsAtPlaced cur rest` +
`FromRecordCallees.lsLogOff`). -/
def genP3CallFrame_placed (A : RustAlloc) [LibsignalPlacement] (sp : BitVec 64)
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
    coinsAtPlaced cur rest ∗
    FromRecordCallees.lsLogOff ∗
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)

/-- Relocatable `[LibsignalPlacement]` `genP3Pre` at `dpPollEntryPlaced + 0x1778#64`. -/
def genP3Pre_placed (A : RustAlloc) [LibsignalPlacement] (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
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
    genP3CallFrame_placed A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
    genP3SpillAll sp

/-- Relocatable `[LibsignalPlacement]` `genP3S5PostFrame` (`LsTokenInit`). -/
def genP3S5PostFrame_placed (A : RustAlloc) [LibsignalPlacement]
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32)
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

/-- Relocatable `[LibsignalPlacement]` `stageP3DispatchOkMid` (`FromRecordCallees.lsLogOff`). -/
def stageP3DispatchOkMid_placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ FromRecordCallees.lsLogOff ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Relocatable `[LibsignalPlacement]` `stageP3ErrPost` (`FromRecordCallees.lsLogOff`). -/
def stageP3ErrPost_placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr prevStatesPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ FromRecordCallees.lsLogOff ∗
  recordResultAt A outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Relocatable `[LibsignalPlacement]` `stageP3DispatchOkMidPrevEmpty` (`FromRecordCallees.lsLogOff`). -/
def stageP3DispatchOkMidPrevEmpty_placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr ptCap ptPtr : BitVec 64) (g : RecordGhost)
    (pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗
  prevSessionsEmptyAt A coroPtr g ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  FromRecordCallees.lsLogOff ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Relocatable `[LibsignalPlacement]` `stageP3ErrPostPrevEmpty` (`FromRecordCallees.lsLogOff`). -/
def stageP3ErrPostPrevEmpty_placed [LibsignalPlacement] (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
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

/-- Relocatable `[LibsignalPlacement]` CLI `tryDecryptPlacedSpec` weakened to `DistinctSid`
(`remoteIdentity ≠ some localIdentity ∨ DistinctSid`), with `LsTokenInit` and tight `onPanic`
(matching `TightPTrapPlaced.tryDecryptPlacedSpecTPTight` without importing `TightPTrapPlaced`). -/
def pollTryDecryptPlacedSpecP [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
      s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
      (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
      (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
        DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧
      SeedsLen32 x.st ∧
      x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
    sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
    memRegion x.ret 48 ∗ CryptoVerification.Cli.CoinsTape.cliTapeAt ctl x.cur x.rest ∗
    FromRecordCallees.lsLogOff ∗
    stackAt s.sp rootStack ∗ A.pool
  post := (_root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S).post
  onPanic := (_root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S).onPanic

/-- Relocatable `[LibsignalPlacement]` `tryDecryptPlacedSpecTPTight` for `StageP3*PlacedStmt`. -/
def pollTryDecryptPlacedSpecTPTight [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { pollTryDecryptPlacedSpecP C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        LsTokenInit ∗
        (pollTryDecryptPlacedSpecP C A ctl uuidParse S).pre x s
    post := fun x s0 sf =>
      LsTokenInit ∗
        (pollTryDecryptPlacedSpecP C A ctl uuidParse S).post x s0 sf
    onPanic := _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight C S uuidParse }

/-- Relocatable `[LibsignalPlacement]` `cliTryDecryptPqV1_ok` contract on `dpPollProgPlaced`. -/
def CliTryDecryptPqV1PlacedStmt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ (ctl : BitVec 64),
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C E2E.HooksE.A0 ctl uuidTryParse
          (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)))

/-- Relocatable `[LibsignalPlacement]` `StageP3PrevEmptyVRegsStmt`. -/
def StageP3PrevEmptyVRegsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    AllocContractsXCliPlaced A ext →
    ChainClone3OkPlaced A ext →
    SenderChainClone3OkPlaced A ext →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A ctl
          uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))) →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmpty_placed A s0 s coroPtr outPtr initErrsPtr
            ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A s0 s coroPtr outPtr e ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

/-- Relocatable `[LibsignalPlacement]` `StageP3GenStepsVRegsStmt`. -/
def StageP3GenStepsVRegsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    AllocContractsXCliPlaced A ext →
    ChainClone3OkPlaced A ext →
    SenderChainClone3OkPlaced A ext →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A ctl
          uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMid_placed A s0 s coroPtr outPtr initErrsPtr prevStatesPtr
            ptCap ptPtr pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

/-- Relocatable `[LibsignalFullPlacement]` `StageP3PrevEmptyVRegsStmt` with `LibsignalFrozen`. -/
def StageP3PrevEmptyVRegsFrozenPlacedStmt [LibsignalFullPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    AllocContractsXCliPlaced A ext →
    ChainClone3OkPlaced A ext →
    SenderChainClone3OkPlaced A ext →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A ctl
          uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))) →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmpty_placed A s0 s coroPtr outPtr initErrsPtr
            ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A s0 s coroPtr outPtr e ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty_placed A s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

/-- Relocatable `[LibsignalFullPlacement]` `StageP3GenStepsVRegsStmt` with `LibsignalFrozen`. -/
def StageP3GenStepsVRegsFrozenPlacedStmt [LibsignalFullPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    AllocContractsXCliPlaced A ext →
    ChainClone3OkPlaced A ext →
    SenderChainClone3OkPlaced A ext →
    subroutine_ok (dpPollProgPlaced ext)
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight C A ctl
          uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K))) →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      LibsignalFrozen lsmpl s.mem →
      s.pc = dpPollEntryPlaced + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (dpPollProgPlaced ext) s s' →
        s'.pc = dpPollEntryPlaced + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMid_placed A s0 s coroPtr outPtr initErrsPtr prevStatesPtr
            ptCap ptPtr pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (coinsAfterPlaced cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame_placed A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (dpPollProgPlaced ext) (s0.readReg64 .x30) s
        (LsTokenInit ∗
          genP3Pre_placed A s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
