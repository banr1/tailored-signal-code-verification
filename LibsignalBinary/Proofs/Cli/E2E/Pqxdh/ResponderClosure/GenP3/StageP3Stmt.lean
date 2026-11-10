/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Stmts
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3c
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3c -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# General Stage P3 Statement

Defines `StageP3GenStmt` for general-state Stage P3 (`+0x1778 → +0x34dc` on `Ok pt`;
`+0x1778 → s0.readReg64 .x30` on `Err e` or `st.version ≠ msgVer`) of
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`, together with its
model, panic, and spatial frame predicates (`genP3S5*`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SignalSession

/-! Guard against `HkdfToSliceProof` global `@[arm64_norm]` simp pollution
(`sp_sub_688_eq_hsp` rewrites every `sp - k#64` to `(sp - 688#64) + (688 - k)#64`, breaking
`stackAt_sub`). Imported transitively via `DecryptPq.DefsP`; downstream proof modules importing
`StageP3Stmt` must repeat this `attribute [-arm64_norm]` block after their `open` lines. -/
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Model, Panic, and Spatial Frame Predicates (`genP3S5*`) -/

/-- Pure `SessionState.tryDecryptWithState` model evaluation at SPQR v1 (`spqrV1 C.F K`) and
`.preKey` message type. Definitionally equal (`rfl`) to `(x.model C (spqrV1 C.F K) uuidTryParse)`
when `x.msgType = .preKey`, and to `pqxdhTryDecryptModel C (spqrV1 C.F K) uuidTryParse`. -/
abbrev genP3S5Model (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (rem loc : AddrGhost) (msg : SignalMessage) (rest : List (BitVec 8))
    (st : SessionState (List (BitVec 8))) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState (List (BitVec 8)) :=
  Mut.exec (SessionState.tryDecryptWithState C (LibsignalSpqrV1.spqrV1 C.F K).spqr
    (serializeAddresses (serviceIdParse uuidTryParse) rem loc) msg .preKey (coinsOf rest)) st

/-- Frame-polymorphic model-panic postcondition delivered at the `+0x1cd4` junction by the left
disjunct `(x.model C (spqrV1 C.F K) uuidTryParse).1 = .error .panic` of
`Decrypt.tryDecryptOnPanicTight` (under the live branch guard `st.version = msgVer`). -/
def genP3S5ModelPanicProp (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (rem loc : AddrGhost) (st : SessionState (List (BitVec 8)))
    (msg : SignalMessage) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (s0 sf : State) (Pf : SepProp) : Prop :=
  ∀ R : SepProp, (sf.mem ⊨ Pf ∗ R) →
    sf.mem ⊨
      (⌜st.version = msgVer ∧
          (genP3S5Model C K rem loc msg rest st).1 = .error .panic ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R

/-- Full Stage P3 panic postcondition: either allocator OOM (`P3P4.PanicOomProp s0`) or the tight
model-panic disjunct of `tryDecryptPqOnPanicTight` at `(st, msg, rest)` with `st.version = msgVer`. -/
def genP3S5PanicProp (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (rem loc : AddrGhost) (st : SessionState (List (BitVec 8)))
    (msg : SignalMessage) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (s0 sf : State) (Pf : SepProp) : Prop :=
  P3P4.PanicOomProp s0 sf Pf ∨
    genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0 sf Pf

/-- Existential witness for the six low front-spill stack slots `[+0x48, +0x50, +0x5c, +0x7c, +0x98, +0xd0]`
preserved untouched across Stage P3 Sub5 after splitting `memRegion (sp + 0x930#64) 48` out of
`genP3SpillAll sp`. -/
structure GenP3S5FrontRem where
  u48 : BitVec 64
  u50 : BitVec 64
  u98 : BitVec 64
  ud0 : BitVec 64
  u5c : BitVec 32
  u7c : BitVec 32

/-- Stack spill slots from `genP3SpillAll sp` untouched after splitting off
`memRegion (sp + 0x930#64) 48` for `stageP3DispatchPre`. -/
def genP3S5SpillRem (sp : BitVec 64) : SepProp :=
  genP3PendSpillScratch sp ∗
    genP3TailSpillScratch sp ∗
    genP3ChainsSpillScratch sp ∗
    (∃∗ w : GenP3S5FrontRem,
      ((sp + 0x48#64) ↦₆₄ w.u48) ∗
      ((sp + 0x50#64) ↦₆₄ w.u50) ∗
      ((sp + 0x5c#64) ↦₃₂ w.u5c) ∗
      ((sp + 0x7c#64) ↦₃₂ w.u7c) ∗
      ((sp + 0x98#64) ↦₆₄ w.u98) ∗
      ((sp + 0xd0#64) ↦₆₄ w.ud0)) ∗
    memRegion (sp + 0x960#64) 48

/-- Untouched closure/caller resources preserved across Stage P3 Sub5 (`+0x1cd8 → +0x34dc / x30`)
and across the version-mismatch exit (`+0x1e04 → x30`), parameterized by the post-branch coins
resource (`Coins.coinsAfter …` when `st.version = msgVer`; `Coins.coinsAt …` when `st.version ≠ msgVer`). -/
def genP3S5PostFrame (A : RustAlloc) (img : Obj.Image)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) : SepProp :=
  TokenInit img ∗
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

/-! ## 2. `StageP3GenStmt` (`+0x1778 → +0x34dc` / `s0.readReg64 .x30`) -/

/-- General Stage P3 (`+0x1778 → +0x34dc` / `s0.readReg64 .x30`):
Executes general `SessionState` cloning (`CloneGenStmt`), branches on `st.version = msgVer`, calls
`try_decrypt_with_state::<Coins>` via `hroot` at `spqrV1 C.F K` with tight model-panic handling,
and dispatches:
- `Ok pt` (`st.version = msgVer`): stores updated `SessionState` into `coroPtr + 0xf8#64` and
  reaches Stage P4 entry `+0x34dc#64` (`hOk`);
- `Err e` (`st.version = msgVer`, `e ≠ .panic`): drops both states, writes `recordResultAt` into
  `outPtr`, restores callee-saved registers, and returns to `s0.readReg64 .x30` (`hErr`);
- `st.version ≠ msgVer`: logs mismatch, drops both states, writes
  `recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed))` via `stageP3ErrPost`,
  restores callee-saved registers, and returns to `s0.readReg64 .x30` (`hVerNe`). -/
def StageP3GenStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    (hA : AllocContracts img.base A ext) →
    (hcc : ChainClone3OkExt img.base A ext) →
    (hscc : SenderChainClone3OkExt img.base A ext) →
    (hroot : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img)) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      (hOk : ∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        s'.pc = closureEntry img ext + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        img.FrozenLoaded s' →
        s'.symtab = img.symtab →
        (P_s' ⊢
          stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
            ptCap ptPtr pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s' P_s' Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (hErr : ∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf P_f) →
      (hVerNe : ∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (Coins.coinsAt img.base cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf P_f) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

/-- 4K-stack (`AllocContractsMem4K`) generalization of `StageP3GenStmt`, eliminating the 0-stack
`memcpyRegionSpec` requirement so `CliExternsOk` (`allocHookStack = 4096`) instantiates directly. -/
def StageP3GenStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    (hA : AllocContractsMem4K img.base A ext) →
    (hcc : ChainClone3OkExt img.base A ext) →
    (hscc : SenderChainClone3OkExt img.base A ext) →
    (hroot : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img)) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.trace = s0.trace →
      (hOk : ∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        s'.pc = closureEntry img ext + 0x34dc#64 →
        s'.status = .Running →
        s'.sp = s.sp →
        s'.trace = s0.trace →
        s'.readReg64 .x19 = coroPtr →
        s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 →
        s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr →
        s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        img.FrozenLoaded s' →
        s'.symtab = img.symtab →
        (P_s' ⊢
          stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
            ptCap ptPtr pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s' P_s' Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (hErr : ∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr e ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf P_f) →
      (hVerNe : ∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (Coins.coinsAt img.base cur rest)) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf P_f) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

theorem StageP3GenStmt4K.toStageP3GenStmt (h : StageP3GenStmt4K) : StageP3GenStmt :=
  fun img ext C ctl K hA => h img ext C ctl K (AllocContractsMem4K.of_AllocContracts hA)

/-! ## 3. Non-Vacuity and Composability Checks -/

-- Instantiating `StageP3GenStmt` at `tripleRatchetExterns C ctl abs` recovers the `tripleRatchetProgAt` instance.
example (hGen : StageP3GenStmt)
    {A : RustAlloc} (img : Obj.Image) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA' : AllocHooks A abs)
    (hcc : ChainClone3Ok img.base C A ctl abs)
    (hscc : SenderChainClone3Ok img.base C A ctl abs)
    (hroot : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img))
    (himg : Obj.Loads libsignalSessionImage img)
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st)
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace)
    (hOk : ∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
        (s' : State) (P_s' : SepProp),
      st.version = msgVer →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      (pqxdhTryDecryptModel C (LibsignalSpqrV1.spqrV1 C.F K) uuidTryParse rem loc msg rest st).1 =
        .ok pt →
      pt.length ≤ ptCap.toNat →
      ptCap.toNat < 2 ^ 63 →
      ptPtr ≠ 0#64 →
      s'.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x27 = ctxPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' →
      s'.symtab = img.symtab →
      (P_s' ⊢
        stageP3DispatchOkMid A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          ptCap ptPtr pt b_2c0 G'
          (pqxdhTryDecryptModel C (LibsignalSpqrV1.spqrV1 C.F K) uuidTryParse rem loc msg rest st).2 ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (Coins.coinsAfter img.base cur rest
            (decryptDraws C st msg.senderRatchetKey rest))) →
      SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s' P_s' Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0))
    (hErr : ∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
      st.version = msgVer →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt false G' →
      (pqxdhTryDecryptModel C (LibsignalSpqrV1.spqrV1 C.F K) uuidTryParse rem loc msg rest st).1 =
        .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr e ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (Coins.coinsAfter img.base cur rest
            (decryptDraws C st msg.senderRatchetKey rest))) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      Q sf P_f)
    (hVerNe : ∀ (sf : State) (P_f : SepProp),
      st.version ≠ msgVer →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (Coins.coinsAt img.base cur rest)) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .x30) s
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)
      Q
      (genP3S5PanicProp C K rem loc st msg msgVer rest s0) :=
  hGen img (tripleRatchetExterns C ctl abs) C ctl K
    (AllocContracts.of_tripleRatchetProgAt' hA') hcc hscc hroot himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer b_2c0 rest recG st rem loc msgG msg Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt hF hsym hpc hrun hsp_align hsp_root htr
    hOk hErr hVerNe

-- `hroot` matches `TryDecryptPqV1RunStmtP` on `.pre`/`.post`, `tryDecryptSpecTPTight`, and `tryDecryptPqOnPanicTight` by `rfl`.
example (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (img : Obj.Image) (x : TryDecryptGhost) (hpreKey : x.msgType = .preKey) :
    let specGen := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A 0#64
      uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) img
    let specCtl := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl
      uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) img
    let specTP := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl
      uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) img
    specGen = specCtl ∧
    specGen.pre = specTP.pre ∧
    specGen.post = specTP.post ∧
    specGen.onPanic =
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight C
        (LibsignalSpqrV1.spqrV1 C.F K) uuidTryParse ∧
    (x.model C (LibsignalSpqrV1.spqrV1 C.F K) uuidTryParse =
      genP3S5Model C K x.rem x.loc x.msg x.rest x.st) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  cases x
  cases hpreKey
  rfl

-- `CloneGenStmt` composes as the prefix of `StageP3GenStmt` by `SepWPp` framing and `Or.inl` panic lifting.
example (hClone : CloneGenStmt)
    {A : RustAlloc} (img : Obj.Image) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hcc : ChainClone3OkExt img.base A ext)
    (hscc : SenderChainClone3OkExt img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (Q : State → SepProp → Prop)
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = closureEntry img ext + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = cloneExitPC img ext st msgVer →
      s1.status = .Running →
      s1.trace = s0.trace →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      (P1 ⊢
        genP3Post A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (TokenInit img ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)
      Q
      (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := hClone img ext hA hcc hscc himg s0 s s.sp (s.readReg64 .x29)
    coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc_lt hsp_align hsp_root hF hsym hpc hrun htr
  let F : SepProp :=
    TokenInit img ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
  have hP :
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) =
      genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    dsimp only [F]
    ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps,
      ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hF1, hsym1⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hCont s1 (P1 ∗ F) hpc1 hrun1 htr1 hF1 hsym1 (sepConj_mono_left hent1)
        R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨s1, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
