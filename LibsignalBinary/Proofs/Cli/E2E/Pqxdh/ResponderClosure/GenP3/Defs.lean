/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneFetch
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Junction Predicates

Shared `SepProp` junction state predicates for cloning an arbitrary `SessionState` inside
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}` (frame `0xcd0`):
- `genP3Pre` at `+0x1778` (entry of `SessionState` field-by-field clone);
- `genP3J1` at `+0x19b0` (after `local_identity_public`, `remote_identity_public`, `root_key`, `sender_chain`);
- `genP3J2` at `+0x1a5c` (after `receiver_chains` clone loop);
- `genP3J3` at `+0x1b20` (after `pending_pre_key` and `pending_kyber_pre_key`);
- `genP3J4` at `+0x1bac` (after `alice_base_key` and `pq_ratchet_state`);
- `genP3PostEq` / `genP3PostNe` / `genP3Post` at `+0x1cd4` (`st.version = msgVer`) and `+0x1e04` (`st.version ≠ msgVer`).
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.ChainClone3

/-- Ghost relation between original and cloned optional `SenderChainGhost`:
preserves `none`/`some` alignment and, when present, preserves serialized ratchet key bytes. -/
def OptSenderChainCloneRel :
    Option SenderChainGhost → Option SenderChain → Option SenderChainGhost → Prop
  | none, none, none => True
  | some sg, some _, some sg' => sg'.srk.bytes = sg.srk.bytes ∧ sg'.priv.bytes = sg.priv.bytes
  | _, _, _ => False

/-- Untouched caller/callee-setup frame threaded intact across `J0..J3` and consumed/split in
`ClonePackStmt` (`+0x1bac → +0x1cd4 / +0x1e04`):
- `memRegion (sp + 0xa90#64) 344`: destination `SessionStructure` slot packed in `ClonePackStmt`;
- `[sp + 0xa0]`, `[sp + 0xb0]`, `[sp + 0xb8]`, `[sp + 0x3a0]`, `[sp + 0x3ac]`: call-arg spill slots;
- `protocolAddressAt` (`rem`, `loc`), `signalMessageAt`, `memRegion (sp + 0x270#64) 48`,
  `coinsAt img.base cur rest`, `logOff img`, and the `rootStack - chainCloneStack` stack extension
  below `chainCloneStack` so `stackAt sp rootStack` forms directly at `+0x1cd4 / +0x1e04`. -/
def genP3CallFrame (A : RustAlloc) (img : Obj.Image) (sp : BitVec 64)
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
    CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗
    logOff img ∗
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)

/-- Named scratch values for pending/kyber spill slots `[sp + 0x08 .. sp + 0x2c]`. -/
structure GenP3PendSpill where
  v08 : BitVec 64
  v10 : BitVec 64
  v18 : BitVec 64
  v24 : BitVec 32
  v28 : BitVec 32
  v2c : BitVec 32

/-- Pending/kyber scratch spill slots `[sp + 0x08 .. sp + 0x2c]` prior to `ClonePendingStmt` (`J3`). -/
def genP3PendSpillScratch (sp : BitVec 64) : SepProp :=
  ∃∗ w : GenP3PendSpill,
    ((sp + 0x8#64) ↦₆₄ w.v08) ∗
      ((sp + 0x10#64) ↦₆₄ w.v10) ∗
      ((sp + 0x18#64) ↦₆₄ w.v18) ∗
      ((sp + 0x24#64) ↦₃₂ w.v24) ∗
      ((sp + 0x28#64) ↦₃₂ w.v28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.v2c)

/-- Named scratch values for tail spill slots `[sp + 0x30 .. sp + 0x40]`. -/
structure GenP3TailSpill where
  u_30 : BitVec 32
  u_34 : BitVec 32
  u_38 : BitVec 64
  u_40 : BitVec 64

/-- Tail-segment spill slots `[sp + 0x30 .. sp + 0x40]` prior to `CloneKeysTailStmt` (`J4`). -/
def genP3TailSpillScratch (sp : BitVec 64) : SepProp :=
  ∃∗ w : GenP3TailSpill,
    ((sp + 0x30#64) ↦₃₂ w.u_30) ∗
      ((sp + 0x34#64) ↦₃₂ w.u_34) ∗
      ((sp + 0x38#64) ↦₆₄ w.u_38) ∗
      ((sp + 0x40#64) ↦₆₄ w.u_40)

/-- Named scratch values for chains spill slots `[sp + 0x60 .. sp + 0x70]`. -/
structure GenP3ChainsSpill where
  u_60 : BitVec 64
  u_68 : BitVec 64
  u_70 : BitVec 64

/-- Chains-segment spill slots `[sp + 0x60 .. sp + 0x70]` prior to `CloneChainsStmt` (`J2`). -/
def genP3ChainsSpillScratch (sp : BitVec 64) : SepProp :=
  ∃∗ w : GenP3ChainsSpill,
    ((sp + 0x60#64) ↦₆₄ w.u_60) ∗
      ((sp + 0x68#64) ↦₆₄ w.u_68) ∗
      ((sp + 0x70#64) ↦₆₄ w.u_70)

/-- Named scratch values for front-segment spill slots `[sp + 0x48..0xd0, sp + 0x930..0x988]`. -/
structure GenP3FrontSpill where
  u_48 : BitVec 64
  u_50 : BitVec 64
  u_5c : BitVec 32
  u_7c : BitVec 32
  u_98 : BitVec 64
  u_d0 : BitVec 64
  u930 : BitVec 64
  u938 : BitVec 64
  u940 : BitVec 64
  u948 : BitVec 64
  u950 : BitVec 64
  u958 : BitVec 64
  u960 : BitVec 64
  u968 : BitVec 64
  u970 : BitVec 64
  u978 : BitVec 64
  u980 : BitVec 64
  u988 : BitVec 64

/-- Sender-chain inline 96-byte scratch `[sp + 0x930 .. sp + 0x990)` expressed as 6 × 128-bit quads
matching `bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5`. -/
def genP3SenderInlineWords (sp : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) : SepProp :=
  ((sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗
    ((sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
    ((sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗
    ((sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
    ((sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗
    ((sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
    ((sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗
    ((sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
    ((sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗
    ((sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
    ((sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗
    ((sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)

/-- Full spill scratch bundle `[sp + 0x08 .. sp + 0x98, sp + 0xd0, sp + 0x930 .. sp + 0x988]` at
`+0x1778` (`genP3Pre`) and after packing (`genP3Post`). -/
def genP3SpillAll (sp : BitVec 64) : SepProp :=
  genP3PendSpillScratch sp ∗
    genP3TailSpillScratch sp ∗
    genP3ChainsSpillScratch sp ∗
    ∃∗ w : GenP3FrontSpill,
      ((sp + 0x48#64) ↦₆₄ w.u_48) ∗
        ((sp + 0x50#64) ↦₆₄ w.u_50) ∗
        ((sp + 0x5c#64) ↦₃₂ w.u_5c) ∗
        ((sp + 0x7c#64) ↦₃₂ w.u_7c) ∗
        ((sp + 0x98#64) ↦₆₄ w.u_98) ∗
        ((sp + 0xd0#64) ↦₆₄ w.u_d0) ∗
        ((sp + 0x930#64) ↦₆₄ w.u930) ∗
        ((sp + 0x938#64) ↦₆₄ w.u938) ∗
        ((sp + 0x940#64) ↦₆₄ w.u940) ∗
        ((sp + 0x948#64) ↦₆₄ w.u948) ∗
        ((sp + 0x950#64) ↦₆₄ w.u950) ∗
        ((sp + 0x958#64) ↦₆₄ w.u958) ∗
        ((sp + 0x960#64) ↦₆₄ w.u960) ∗
        ((sp + 0x968#64) ↦₆₄ w.u968) ∗
        ((sp + 0x970#64) ↦₆₄ w.u970) ∗
        ((sp + 0x978#64) ↦₆₄ w.u978) ∗
        ((sp + 0x980#64) ↦₆₄ w.u980) ∗
        ((sp + 0x988#64) ↦₆₄ w.u988)

/-- Named witness at junction `J1` (`+0x19b0`). -/
structure GenP3J1Witness where
  newLocIdPtr : BitVec 64
  newRemIdPtr : BitVec 64
  newRootKeyPtr : BitVec 64
  c0 : BitVec 64
  sender' : Option SenderChainGhost
  sq0 : BitVec 128
  sq1 : BitVec 128
  sq2 : BitVec 128
  sq3 : BitVec 128
  sq4 : BitVec 128
  sq5 : BitVec 128

/-- Named witness at junction `J2` (`+0x1a5c`). -/
structure GenP3J2Witness extends GenP3J1Witness where
  newRcPtr : BitVec 64
  chains' : List ChainGhost

/-- Named witness at junction `J3` (`+0x1b20`). -/
structure GenP3J3Witness extends GenP3J2Witness where
  pendCap' : BitVec 64
  pendPtr' : BitVec 64
  kybCap' : BitVec 64
  kybPtr' : BitVec 64
  d10 : BitVec 64
  w24 : BitVec 32
  w28 : BitVec 32
  w2c : BitVec 32

/-- Named witness at junction `J4` (`+0x1bac`). -/
structure GenP3J4Witness extends GenP3J3Witness where
  newAlicePtr : BitVec 64
  newPqPtr : BitVec 64
  regW0 : BitVec 32
  regW1 : BitVec 32

/-- Entry state predicate `genP3Pre` at `+0x1778`: Holds arbitrary source `sessionStateAt A (coroPtr + 0xf8#64) recG st`, allocator pool + stack frame,
`[sp + 0xc0] ↦₆₄ ctxPtr`, spill slots, and `try_decrypt` setup frame, with entry register equalities
`s.sp = sp`, `x19 = coroPtr`, `x27 = sp + 0x370#64`, `x29 = fp`. -/
def genP3Pre (A : RustAlloc) (img : Obj.Image) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
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
    genP3CallFrame A img sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
    genP3SpillAll sp

/-- Junction 1 predicate `genP3J1` at `+0x19b0`: After cloning `local_identity_public`, `remote_identity_public`, `root_key`, and `sender_chain`
(`+0x1778 → +0x19b0`).
Live registers: `x19 = coroPtr`, `x23 = newLocIdPtr`, `x24 = remIdLen`, `x25 = newRemIdPtr`,
`x27 = sp + 0x370#64` (still live for `Chain::clone` sret loads in `CloneChains`), `x29 = fp`. -/
def genP3J1 (A : RustAlloc) (img : Obj.Image) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J1Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x23 = w.newLocIdPtr ∧
      s.readReg64 .x24 = BitVec.ofNat 64 recG.remoteIk.bytes.length ∧
      s.readReg64 .x25 = w.newRemIdPtr ∧
      s.readReg64 .x27 = sp + 0x370#64 ∧
      s.readReg64 .x29 = fp ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      A.pool ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFrame A img sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
      vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A w.sender' st.senderChain ∗
      genP3PendSpillScratch sp ∗
      genP3TailSpillScratch sp ∗
      genP3ChainsSpillScratch sp ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-- Junction 2 predicate `genP3J2` at `+0x1a5c`: After spilling `[sp + 0x60..0x78)` and cloning `receiver_chains` (`+0x19b0 → +0x1a5c`).
Live registers: `x19 = coroPtr`, `x23 = receiverChains.length`, `x25 = newRcPtr`,
`x27 = sp + 0x370#64`, `x28 = 32#64` (`[sp + 0x98]`), `x29 = fp`. -/
def genP3J2 (A : RustAlloc) (img : Obj.Image) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J2Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x23 = BitVec.ofNat 64 st.receiverChains.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x27 = sp + 0x370#64 ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      w.chains'.length = st.receiverChains.length ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      A.pool ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFrame A img sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
      vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A w.sender' st.senderChain ∗
      vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
        (w.chains'.zip st.receiverChains) ∗
      genP3PendSpillScratch sp ∗
      genP3TailSpillScratch sp ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-- Junction 3 predicate `genP3J3` at `+0x1b20`: After reloading `x27 = ctxPtr` from `[sp + 0xc0]` and cloning `pending_pre_key` and
`pending_kyber_pre_key` (`+0x1a5c → +0x1b20`).
Live registers: `x19 = coroPtr`, `x22 = pendCap'`, `x23 = receiverChains.length`,
`x25 = newRcPtr`, `x26 = kybCap'`, `x27 = ctxPtr`, `x28 = 32#64`, `x29 = fp`
(plus unpinned `w20` read directly from `s.readReg64 .x20` when packing `[sp + 0xba4]`). -/
def genP3J3 (A : RustAlloc) (img : Obj.Image) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J3Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x22 = w.pendCap' ∧
      s.readReg64 .x23 = BitVec.ofNat 64 st.receiverChains.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x26 = w.kybCap' ∧
      s.readReg64 .x27 = ctxPtr ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      w.chains'.length = st.receiverChains.length ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      A.pool ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFrame A img sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
      vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A w.sender' st.senderChain ∗
      vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
        (w.chains'.zip st.receiverChains) ∗
      OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
      OptKybClone A recG.kyber w.kybCap' w.kybPtr' ∗
      genP3TailSpillScratch sp ∗
      ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
      ((sp + 0x10#64) ↦₆₄ w.d10) ∗
      ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
      ((sp + 0x24#64) ↦₃₂ w.w24) ∗
      ((sp + 0x28#64) ↦₃₂ w.w28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-- Junction 4 predicate `genP3J4` at `+0x1bac`: After spilling `[sp + 0x30..0x48)` and cloning `alice_base_key` and `pq_ratchet_state`
(`+0x1b20 → +0x1bac`). All heap allocations are complete and ready to assemble into
`sp + 0xa90`. -/
def genP3J4 (A : RustAlloc) (img : Obj.Image) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ∃∗ w : GenP3J4Witness,
    ⌜s.sp = sp ∧
      s.readReg64 .x19 = coroPtr ∧
      s.readReg64 .x21 = w.newPqPtr ∧
      s.readReg64 .x22 = w.pendCap' ∧
      s.readReg64 .x23 = w.newAlicePtr ∧
      s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length ∧
      s.readReg64 .x25 = w.newRcPtr ∧
      s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length ∧
      s.readReg64 .x27 = ctxPtr ∧
      s.readReg64 .x28 = 32#64 ∧
      s.readReg64 .x29 = fp ∧
      recG.regIds = unpack32 w.regW0 ++ unpack32 w.regW1 ∧
      w.chains'.length = st.receiverChains.length ∧
      OptSenderChainCloneRel recG.sender st.senderChain w.sender' ∧
      OptSenderChainInline w.sender' st.senderChain
        (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)⌝ ∗
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      A.pool ∗
      stackAt sp chainCloneStack ∗
      memRegion (sp + 0x3e0#64) 104 ∗
      ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      genP3CallFrame A img sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
      vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      optSenderChainHeap A w.sender' st.senderChain ∗
      vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
        (w.chains'.zip st.receiverChains) ∗
      OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
      OptKybClone A recG.kyber w.kybCap' w.kybPtr' ∗
      vecU8Buf A (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState ∗
      ((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
      ((sp + 0x10#64) ↦₆₄ w.d10) ∗
      ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
      ((sp + 0x24#64) ↦₃₂ w.w24) ∗
      ((sp + 0x28#64) ↦₃₂ w.w28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
      ((sp + 0x30#64) ↦₃₂ w.regW0) ∗
      ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
      ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
      ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5

/-- Spatial resources common to both post-pack exit points (`+0x1cd4` and `+0x1e04`):
the original `sessionStateAt A (coroPtr + 0xf8#64) recG st`, the newly packed
`∃∗ G₁, ⌜recG.CloneRel G₁⌝ ∗ sessionStateAt A (sp + 0xa90#64) G₁ st`, the exact `try_decrypt`
spatial precondition bundle (`protocolAddressAt` × 2, `signalMessageAt`, `memRegion (sp + 0x270) 48`,
`coinsAt`, `logOff img`, `stackAt sp rootStack`, `A.pool`), plus the preserved closure frame slots. -/
def genP3PostSpatial (A : RustAlloc) (img : Obj.Image) (sp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
    (∃∗ G₁ : SessionGhost, ⌜CloneRel recG G₁⌝ ∗ sessionStateAt A (sp + 0xa90#64) G₁ st) ∗
    protocolAddressAt A rem remAddrPtr ∗
    protocolAddressAt A loc locAddrPtr ∗
    signalMessageAt A msgG whisperMsgPtr msg ∗
    memRegion (sp + 0x270#64) 48 ∗
    CryptoVerification.SignalSession.Coins.coinsAt img.base cur rest ∗
    logOff img ∗
    stackAt sp rootStack ∗
    A.pool ∗
    memRegion (sp + 0x3e0#64) 104 ∗
    ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
    ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
    ((sp + 0xb8#64) ↦₃₂ msgVer) ∗
    ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
    ((sp + 0x3ac#64) ↦₈ 3#8) ∗
    genP3SpillAll sp

/-- **Post-pack state predicate `genP3PostEq` at `+0x1cd4`** (`st.version = msgVer`):
All `try_decrypt_with_state` ABI call registers (`x0..x6`) and closure callee-saved registers
(`x19`, `x24 = sp + 0x370#64`, `x27 = ctxPtr`, `x29 = fp`) are loaded for `bl try_decrypt_with_state`. -/
def genP3PostEq (A : RustAlloc) (img : Obj.Image) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ⌜s.sp = sp ∧
    s.readReg64 .x0 = sp + 0x270#64 ∧
    s.readReg64 .x1 = sp + 0xa90#64 ∧
    s.readReg64 .x2 = remAddrPtr ∧
    s.readReg64 .x3 = locAddrPtr ∧
    s.readReg64 .x4 = whisperMsgPtr ∧
    s.readReg64 .x5 = 3#64 ∧
    s.readReg64 .x6 = 0#64 ∧
    s.readReg64 .x19 = coroPtr ∧
    s.readReg64 .x24 = sp + 0x370#64 ∧
    s.readReg64 .x27 = ctxPtr ∧
    s.readReg64 .x29 = fp⌝ ∗
    genP3PostSpatial A img sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg

/-- **Post-pack state predicate `genP3PostNe` at `+0x1e04`** (`st.version ≠ msgVer`):
Version-mismatch branch target `+0x1e04` with `x9 = msgVer.setWidth 64`, `x19 = coroPtr`,
`x24 = sp + 0x370#64`, `x27 = ctxPtr`, `x29 = fp`, and the packed cloned state at `sp + 0xa90` ready
for logging and `drop_glue::<SessionStructure>`. -/
def genP3PostNe (A : RustAlloc) (img : Obj.Image) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  ⌜s.sp = sp ∧
    s.readReg64 .x9 = msgVer.setWidth 64 ∧
    s.readReg64 .x19 = coroPtr ∧
    s.readReg64 .x24 = sp + 0x370#64 ∧
    s.readReg64 .x27 = ctxPtr ∧
    s.readReg64 .x29 = fp⌝ ∗
    genP3PostSpatial A img sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg

/-- Unified post-pack state predicate `genP3Post`: Selects `genP3PostEq` at `+0x1cd4` when `st.version = msgVer` and `genP3PostNe` at `+0x1e04` when
`st.version ≠ msgVer` (where `st.version = if st.sessionVersion == 0 then 2 else st.sessionVersion`). -/
def genP3Post (A : RustAlloc) (img : Obj.Image) (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur : BitVec 64) (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (s : State) : SepProp :=
  if st.version = msgVer then
    genP3PostEq A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg s
  else
    genP3PostNe A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg s

/-- `Chain::clone [local#5]` (`chainClone3Name`) meets `chainCloneSpec A` on
`tripleRatchetProgAtExt b ext` (`ProgAtExt` twin of `ChainClone3.ChainClone3Ok`). -/
def ChainClone3OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name)
    (chainCloneSpec A)

/-- `Chain::clone [local#5]` (`chainClone3Name`) meets `senderChainCloneSpec A` on
`tripleRatchetProgAtExt b ext` (`ProgAtExt` twin of `ChainClone3.SenderChainClone3Ok`). -/
def SenderChainClone3OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3.chainClone3Name)
    (senderChainCloneSpec A)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
