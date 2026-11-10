/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.InImage.Spqr
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet

/-!
# `try_decrypt_with_state` Segment Checkpoints and Contracts

Defines the intermediate machine checkpoint states (`LoadRatchetState` through `ApplyRatchetState`
and `ErrTailState`), per-segment contracts (`IdentityKeysSpec` through `ApplyRatchetSpec` and
`ErrTailSpec`), and callee bundles for `try_decrypt_with_state` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalSession

/-! ## Callee Symbol Names and `subroutine_ok` Hypotheses -/

/-- Callee hypothesis that `core::ptr::drop_glue::<Chain>` meets `dropChainSpec A` on
`tripleRatchetProgAt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName)
    (dropChainSpec A)

/-- Bundle of all 16 callee `subroutine_ok` hypotheses required by `try_decrypt_with_state`. -/
structure _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCallees (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop where
  localIk : LocalIdentityKeyOk img C A ctl abs
  remoteIk : RemoteIdentityKeyOk img C A ctl abs
  sameAcc : IsSameAccountOk img.base C ctl abs
  clearUpk : ClearUpkOk img.base C A ctl abs
  dropChain : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk img.base C A ctl abs
  chainKeyToPb : ChainKeyToPbOk img.base C A ctl abs
  derivePk : DerivePublicKeyBytesOk img.base C ctl abs
  trFrom : TrFromOk img C A ctl abs
  trApply : TrApplyOk img.base C A ctl abs
  findReceiverChainKey : FindReceiverChainKeyOk img C A ctl abs
  createChain : CreateChainOk img C A ctl abs
  genKeys : GenerateKeysOk img C A ctl abs
  pkSer : PublicKeySerializeOk img.base C A ctl abs
  verifyMac : VerifyMacWithAddressesOk img C A ctl parse abs
  cmk : CmkOk img C A ctl abs
  growOne : GrowOneChainOk img C A ctl abs

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName)
    (dropChainSpec A)

/-- Bundle of all 16 callee `subroutine_ok` hypotheses on `tripleRatchetProgAtExt img.base ext`. -/
structure _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCalleesExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop where
  localIk : LocalIdentityKeyOkExt img A ext
  remoteIk : RemoteIdentityKeyOkExt img A ext
  sameAcc : IsSameAccountOkExt img.base ext
  clearUpk : ClearUpkOkExt img.base A ext
  dropChain : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext
  chainKeyToPb : ChainKeyToPbOkExt img.base A ext
  derivePk : DerivePublicKeyBytesOkExt img.base C ext
  trFrom : TrFromOkExt img A ext
  trApply : TrApplyOkExt img.base A ext
  findReceiverChainKey : FindReceiverChainKeyOkExt img A ext
  createChain : CreateChainOkExt img C A ext
  genKeys : GenerateKeysOkExt img C A ext
  pkSer : PublicKeySerializeOkExt img.base A ext
  verifyMac : VerifyMacWithAddressesOkExt img C A parse ext
  cmk : CmkOkExt img C A ext
  growOne : GrowOneChainOkExt img A ext

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt b A (trTrapExterns C abs)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCallees_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCalleesExt img C A parse (trTrapExterns C abs)

def _root_.CryptoVerification.LibsignalTripleRatchet.SpqrRecvOk_trap (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img spqrRecvName)
    (spqrRecvSpec A S img)

def SpqrRecvOkQ_trap (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img spqrRecvName)
    ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes))

theorem spqrRecvOkQ_of_recvOk_trap {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image}
    (h : _root_.CryptoVerification.LibsignalTripleRatchet.SpqrRecvOk_trap C A S abs img) :
    SpqrRecvOkQ_trap Q C A S abs img :=
  Spec.subroutine_ok_restrictPre _ h

theorem spqrRecvOkQ_empty_trap {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {abs : String → Option (State → State)} {img : Obj.Image}
    (h : SpqrRecvEmptyRunStmt_trap C A S abs img) (hhooks : TripleRatchetHooks C A S abs)
    (hempty : S.RecvEmptyOk) (hloads : Obj.Loads libsignalSessionImage img) :
    SpqrRecvOkQ_trap (· = []) C A S abs img :=
  h hhooks hempty hloads

def SpqrRecvOkQF_trap (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img spqrRecvName)
    (spqrRecvSpecQF Q Pstk F A S img)

theorem spqrRecvOkQF_of_okQ_trap {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image}
    (h : SpqrRecvOkQ_trap Q C A S abs img) :
    SpqrRecvOkQF_trap Q (fun _ => True) emp C A S abs img :=
  subroutine_ok_spqrRecvSpecQF_emp h

/-- Entry address of `try_decrypt_with_state::<Coins>`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName

/-- S1 entry (`+0x1d8`): `bl TR::from_session_state` after identity-key checks complete with
`self_session = false` (`w1 = 0`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x1d8#64

/-- S2 entry (`+0x2a4`): `bl RatchetState::find_receiver_chain_key` after `TR::from_session_state`
copies the 264-byte `TripleRatchet` to `sp + 0x38..0x140`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segFindChainPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x2a4#64

/-- S3 entry (`+0x500`): inlined `RatchetState::dh_ratchet_step` body when
`find_receiver_chain_key` returns `Ok(None)`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDhStepPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x500#64

/-- S4 entry (`+0x3e4`): join point of `ensureReceiverChain = .ok ck` before
`<ProtocolAddress as Display>::fmt` (`+0x440`) and `RatchetState::consume_message_key` (`+0x474`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x3e4#64

/-- S5 entry (`+0x5b8`): after `consume_message_key` returns `Ok(mkg)` and the formatted `Display`
string at `sp + 0x3d0` has been dropped. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x5b8#64

/-- S6 entry (`+0x5dc`): after `spqr::recv` (`+0x5cc`) returns `Ok(newPqrState, pqrKey)`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x5dc#64

/-- S7 entry (`+0x63c`): immediately after `MessageKeyGenerator::generate_keys` returns at `+0x638`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x63c#64

/-- S8 entry (`+0x678`): after `SignalMessage::verify_mac_with_addresses` (`+0x65c`) returns `Ok(true)`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segAesDecryptPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x678#64

/-- S9 entry (`+0x6a4`): after `aes_256_cbc_decrypt` (`+0x694`) returns `some pt`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segApplyRatchetPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x6a4#64

/-- `ErrTail` entry (`+0x30c`): shared `TripleRatchet` drop and error return block after
`TR::from_session_state` has taken `receiver_chains` and `pq_ratchet_state` from `x.ss`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x30c#64

/-- `ErrTail` chain-drop loop header (`+0x33c`), iterating `drop_glue<Chain>` over
`tr.ratchet.receiver_chains` (`x19` advancing by `0x68 = 104`, `x21` decrementing by `1`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errDropChainLoopPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x33c#64

/-- Shared return epilogue (`+0x394 .. +0x3b0`), restoring `sp` and callee-saved registers. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.retEpiloguePC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img + 0x394#64

/-! ## Stack Frame Predicates and Intermediate Checkpoint States -/

set_option linter.unusedVariables false in
/-- Borrowed read-only inputs and environment resources kept unchanged across the execution of
`try_decrypt_with_state` (with `draws` bytes consumed from the RNG tape: `0` before S3 and on the
`findReceiverChainKey = .ok (some _)` path, `min 32 x.rest.length` after `rng_fill` in S3). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (draws : Nat) (s0 : State) : SepProp :=
  protocolAddressAt A x.rem x.remA ∗
  protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
  logOff img ∗
  stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
  tryDecryptSavedRegs s0.sp s0 ∗
  A.pool

/-- Error cleanup checkpoint state at `errTailPC img` (`+0x30c`) after `TR::from_session_state` has
succeeded:
* `x19 = x.ret`, `x20 = sp + 0x140`, `x26 = speTag e`;
* `sp + 0x168..0x190` holds `speBodyAt A (utf8 "decrypt") (sp + 0x168) e`;
* `sp + 0x38..0x140` holds `trAt A (sp + 0x38) trG tr`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x26 = speTag e ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x38 ∗
    memRegion (sp + 0x140#64) 0x28 ∗
    speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
    memRegion (sp + 0x190#64) 0x3f0 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S1 checkpoint state at `segLoadRatchetPC img` (`+0x1d8`) after identity-key checks complete with
`w1 = 0` (`self_session = false`):
* `x19 = x.ret`, `x20 = sp + 0x140`, `x21 = x.ss`, `x22 = x.msgA`, `x23 = sp + 0x500`,
  `(x24).setWidth 8 = msgTypeByte x.msgType`, `x25 = x.locA`, `(x1).setWidth 32 = 0#32`;
* `[sp + 0x30] = x.remA`, with scratch regions `[sp .. sp + 0x30]` and `[sp + 0x38 .. sp + 0x580]`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = x.locA ∧
  (s.readReg64 .x1).setWidth 32 = 0#32 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G x.st ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x30 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x548 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- S2 checkpoint state at `segFindChainPC img` (`+0x2a4`): `TR::from_session_state` returned
`Ok(tr)` copied to `sp + 0x38..0x140`, `[sp + 0x20] = x.locA`, `[sp + 0x28] = x.msg.counter`, and
`(x0, x1, x8) = (sp + 0x38, x.msgA + 0x38, sp + 0x190)` are staged for `find_receiver_chain_key`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segFindChainPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x0 = sp + 0x38#64 ∧
  s.readReg64 .x1 = x.msgA + 0x38#64 ∧
  s.readReg64 .x8 = sp + 0x190#64 ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x2c0#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x440 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- S3 checkpoint state at `segDhStepPC img` (`+0x500`): `find_receiver_chain_key` returned
`Ok(None)`, entering the inlined `RatchetState::dh_ratchet_step` body with `x12 = sp + 0x2c0`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDhStepPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x12 = sp + 0x2c0#64 ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x2c0#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x440 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- S4 checkpoint state at `segConsumeMsgKeyPC img` (`+0x3e4`) after `ensureReceiverChain = .ok ck`:
the 36-byte `chainKeyBytes ck` is staged across `sp + 0x2c0..0x2d4` (first 20 bytes, `x12 = sp + 0x2c0`)
and `sp + 0x2b0..0x2c0` (last 16 bytes, `x25 + 0x120`) for reassembly at `sp + 0x2e0..0x304`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x12 = sp + 0x2c0#64 ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  (s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    trAt A (sp + 0x38#64) trG tr ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
    memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x170 ∗
    ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes ck).drop 20) ∗
    ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes ck).take 20) ∗
    memRegion (sp + 0x2d4#64) 0x2ac ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S5 checkpoint state at `segPqRecvPC img` (`+0x5b8`) after `consume_message_key` returns `Ok(mkg)`:
* `[sp + 0x1c]` holds `msgW` with low byte `msgTypeByte x.msgType` (`w24 = 1#32`);
* `mkg.seed` (`32` B) is split across `cap` at `[sp + 0x28]`, `ptr` at `[sp + 0x10]`, `len = 32` at
  `[sp + 0x450]`, with `mkg.counter` at `[sp + 0x458]`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segPqRecvPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 32 = 1#32 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  ∃ (seedCap seedPtr : BitVec 64) (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 0x18#64) 4 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ seedCap) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x310 ∗
      ((sp + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 0x458#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 0x45c#64) 0x124 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S6 checkpoint state at `segDeriveKeysPC img` (`+0x5dc`): `spqr::recv` returned
`Ok(newPqrState, pqrKey)` at `sp + 0x500..0x530` with `x8 = newPqrCap`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDeriveKeysPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  (s.readReg64 .x24).setWidth 32 = 1#32 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x500#64 ∧
  ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
    s.readReg64 .x8 = newPqrCap ∧
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      vecU8At A (sp + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
      spqrRecvKeyAt A (sp + 0x518#64) pqrKey ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 0x18#64) 4 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ seedCap) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x310 ∗
      ((sp + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 0x458#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 0x45c#64) 0xa4 ∗
      memRegion (sp + 0x530#64) 0x50 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S7 checkpoint state at `segVerifyMacPC img` (`+0x63c`): `generate_keys` returned `mks` (`84` B)
at `sp + 0x500..0x554`, with `newPqrState` split across `[sp + 0x8]`, `[sp + 0x28]`, and `x24`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x3d0#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x500#64 ∧
  ∃ (newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      messageKeysAt (sp + 0x500#64) mks ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 0x10#64) 0xc ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ newPqrPtr) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x3c0 ∗
      memRegion (sp + 0x554#64) 0x2c ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S8 checkpoint state at `segAesDecryptPC img` (`+0x678`) after `verify_mac_with_addresses`
returns `Ok(true)`, preserving the `VerifyMacState` frame and registers. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segAesDecryptPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x3d0#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x500#64 ∧
  ∃ (newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      messageKeysAt (sp + 0x500#64) mks ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 0x10#64) 0xc ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₆₄ newPqrPtr) ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x3c0 ∗
      memRegion (sp + 0x554#64) 0x2c ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S9 checkpoint state at `segApplyRatchetPC img` (`+0x6a4`): `aes_256_cbc_decrypt` returned
`some pt`, placing `vecU8 A (sp + 0x3d0) pt` at `sp + 0x3d0..0x3e8`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segApplyRatchetPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x23 = sp + 0x3d0#64 ∧
  s.readReg64 .x24 = BitVec.ofNat 64 newPqrState.length ∧
  ∃ (newPqrCap newPqrPtr : BitVec 64),
    newPqrState.length ≤ newPqrCap.toNat ∧ newPqrCap.toNat < 2 ^ 63 ∧ newPqrPtr ≠ 0 ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      (if newPqrCap = 0 then emp else A.live newPqrPtr newPqrCap.toNat 1 ∗
        (newPqrPtr ↦ₛ newPqrState) ∗
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length) (newPqrCap.toNat - newPqrState.length)) ∗
      vecU8 A (sp + 0x3d0#64) pt ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 0x10#64) 0x18 ∗
      ((sp + 0x28#64) ↦₆₄ newPqrPtr) ∗
      memRegion (sp + 0x30#64) 8 ∗
      memRegion (sp + 0x140#64) 0x290 ∗
      memRegion (sp + 0x3e8#64) 0x198 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-! ## Segment Contracts and `TryDecryptOk` -/

/-- `ErrTail` contract (`+0x30c → +0x3b0`): writes `speAt` to `x.ret`, drops all chains in
`tr.ratchet.receiver_chains` and the `receiver_chains` / `tr.pqr_state` buffers, and executes the
return epilogue. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

/-- Segment S0 contract (`+0x000 → +0x1d8`): executes the prologue, `local_identity_key`,
`remote_identity_key`, and either the `remoteIdentity = none` log path or `is_same_account`
(returning `false`), reaching `LoadRatchetState` at `segLoadRatchetPC img`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.IdentityKeysSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOk img C A ctl abs →
  RemoteIdentityKeyOk img C A ctl abs →
  IsSameAccountOk img.base C ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0)

/-- Segment S1 contract (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`): calls `TR::from_session_state`,
either writing the SPE and returning on `.error e` or copying `tr` (`264` B) to `sp + 0x38..0x140`
and reaching `FindChainState` at `segFindChainPC img` on `.ok tr`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
          (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s'

/-- Segment S2 contract (`+0x2a4 → +0x3e4 / +0x500 / +0x30c`): calls
`RatchetState::find_receiver_chain_key`, branching to `ConsumeMsgKeyState` on `.ok (some ck)`,
`DhStepState` on `.ok none`, or `ErrTailState` on `.error e`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  FindReceiverChainKeyOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDhStepPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e 0 R s0)

/-- Segment S3 contract (`+0x500 → +0x3e4 / +0x30c` or OOM panic): executes the inlined
`RatchetState::dh_ratchet_step`, reaching `ConsumeMsgKeyState` on `.ok ck` or `ErrTailState` on
`.error e`. Assumes `tr.ratchet.receiverChains.length < 2 ^ 32` (preventing `CapacityOverflow` in
`grow_one`) and `rootStack ≤ s0.sp.toNat` (non-null stack HKDF salt pointers `sp + 0x3b0`, `sp + 0x4a0`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CreateChainOk img C A ctl abs →
  DerivePublicKeyBytesOk img.base C ctl abs →
  PublicKeySerializeOk img.base C A ctl abs →
  ChainKeyToPbOk img.base C A ctl abs →
  GrowOneChainOk img C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG' r1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment S4 contract (`+0x3e4 → +0x5b8 / +0x30c` or panic): formats `x.rem`, calls
`RatchetState::consume_message_key`, drops the formatted string, and branches to `PqRecvState` on
`.ok mkg`, panics on `.error .panic`, or reaches `ErrTailState` on `.error e` (`e ≠ .panic`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeySpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CmkOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

/-- Segment S5 contract (`+0x5b8 → +0x5dc / +0x30c` or panic), parameterized by a precondition `Q` on
`tr.pqrState`: calls `spqr::recv` under `SpqrRecvOkQ Q`, reaching `DeriveKeysState` on
`.ok (newPqrState, pqrKey)` or formatting the error, freeing `mkg.seed`, and reaching `ErrTailState`
on `.error sd`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvSpec (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  SpqrRecvOkQ Q C A ctl S abs img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvSpecQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  SpqrRecvOkQF Q Pstk F C A ctl S abs img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      Pstk (s0.sp - 1504#64).toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (F ∗ R) s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment S6 contract (`+0x5dc → +0x63c`): saves `newPqrState`, stages `mkg` and `pqrKey`, and
calls `MessageKeyGenerator::generate_keys` (assuming `mkg.seed.length = 32`), reaching `VerifyMacState`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  GenerateKeysOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img) s
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

/-- Segment S7 contract (`+0x63c → +0x678 / +0x30c` or OOM panic): calls
`SignalMessage::verify_mac_with_addresses`, reaching `AesDecryptState` on `true` or allocating
`"bad authentication code"`, freeing `newPqrState`, and reaching `ErrTailState` on `false`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  VerifyMacWithAddressesOk img C A ctl parse abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment S8 contract (`+0x678 → +0x6a4 / +0x30c` or OOM panic): calls `aes_256_cbc_decrypt`,
reaching `ApplyRatchetState` on `some pt` or formatting `"bad ciphertext"`, freeing `newPqrState`,
and reaching `ErrTailState` on `none`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment S9 contract (`+0x6a4 → +0x4b8 → +0x3b0` or OOM panic): replaces `tr.pqr_state` with
`newPqrState`, writes `Ok(pt)` to `x.ret`, calls `TR::apply_to_session_state` and
`SessionState::clear_unacknowledged_pre_key_message`, and returns via the epilogue. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  TrApplyOk img.base C A ctl abs →
  ClearUpkOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
      (R : SepProp) (s0 s : State),
      (x.model C S parse).1 = .ok pt →
      (x.model C S parse).2 =
        (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

/-- Whole-function `subroutine_ok` statement for `try_decrypt_with_state::<Coins>` against
`tryDecryptSpec`, restricted to session states whose PQ state satisfies `Q`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptOk (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecQF (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s
    post := fun x s0 sf => F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).post x s0 sf }

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptOkQF (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecQF Q F C A ctl parse S img)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptOk_of_okQF {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptOkQF Q emp img C A ctl parse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptOk Q img C A ctl parse S abs := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecQF, Spec.restrictPre] at hpre ⊢
    rwa [emp_sepConj]
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecQF, Spec.restrictPre] at hpost ⊢
    rwa [emp_sepConj] at hpost

/-! ## `tripleRatchetProgAtExt` Segment Contracts -/

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S0SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOkExt img A ext →
  RemoteIdentityKeyOkExt img A ext →
  IsSameAccountOkExt img.base ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S1SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOkExt img A ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s'

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S2SpecExt (img : Obj.Image) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  FindReceiverChainKeyOkExt img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDhStepPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e 0 R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S3SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  CreateChainOkExt img C A ext →
  DerivePublicKeyBytesOkExt img.base C ext →
  PublicKeySerializeOkExt img.base A ext →
  ChainKeyToPbOkExt img.base A ext →
  GrowOneChainOkExt img A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      x.rest.length < 2 ^ 63 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG' r1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S4SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  CmkOkExt img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S6SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  GenerateKeysOkExt img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img) s
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S7SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  VerifyMacWithAddressesOkExt img C A parse ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S8SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S9SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  TrApplyOkExt img.base A ext →
  ClearUpkOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
      (R : SepProp) (s0 s : State),
      (x.model C S parse).1 = .ok pt →
      (x.model C S parse).2 =
        (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S3SpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  CreateChainOkExt img C A ext →
  DerivePublicKeyBytesOkExt img.base C ext →
  PublicKeySerializeOkExt img.base A ext →
  ChainKeyToPbOkExt img.base A ext →
  GrowOneChainOkExt img A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG' r1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S4SpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  CmkOkExt img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S7SpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  VerifyMacWithAddressesOkExt img C A parse ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S8SpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S9SpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  TrApplyOkExt img.base A ext →
  ClearUpkOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
      (R : SepProp) (s0 s : State),
      (x.model C S parse).1 = .ok pt →
      (x.model C S parse).2 =
        (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk_trap img.base C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.IdentityKeysSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S0SpecExt img C A ctl parse S (trTrapExterns C abs)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S1SpecExt img C A ctl parse S (trTrapExterns C abs)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S2SpecExt img A ctl (trTrapExterns C abs)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CreateChainOkExt img C A (trTrapExterns C abs) →
  DerivePublicKeyBytesOkExt img.base C (trTrapExterns C abs) →
  PublicKeySerializeOkExt img.base A (trTrapExterns C abs) →
  ChainKeyToPbOkExt img.base A (trTrapExterns C abs) →
  GrowOneChainOkExt img A (trTrapExterns C abs) →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOk_trap img.base C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((∃ trG' r1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeySpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CmkOkExt img C A (trTrapExterns C abs) →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck draws R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvSpec_trap (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  SpqrRecvOkQ_trap Q C A S abs img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvSpecQF_trap (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  SpqrRecvOkQF_trap Q Pstk F C A S abs img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      Pstk (s0.sp - 1504#64).toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG tr st1 mkg draws (F ∗ R) s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S6SpecExt img C A ctl (trTrapExterns C abs)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  VerifyMacWithAddressesOkExt img C A parse (trTrapExterns C abs) →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (trTrapProgAt img.base C abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (trTrapProgAt img.base C abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (trTrapProgAt img.base C abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (trTrapProgAt img.base C abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  TrApplyOkExt img.base A (trTrapExterns C abs) →
  ClearUpkOkExt img.base A (trTrapExterns C abs) →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
      (R : SepProp) (s0 s : State),
      (x.model C S parse).1 = .ok pt →
      (x.model C S parse).2 =
        (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptOk_trap (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptOkQF_trap (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecQF Q F C A ctl parse S img)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptOk_of_okQF_trap {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptOkQF_trap Q emp img C A ctl parse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptOk_trap Q img C A ctl parse S abs := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecQF, Spec.restrictPre] at hpre ⊢
    rwa [emp_sepConj]
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecQF, Spec.restrictPre] at hpost ⊢
    rwa [emp_sepConj] at hpost

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → _root_.CryptoVerification.LibsignalTripleRatchet.SpqrRecvOk_trap C A S abs img → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜x.st.pqRatchetState = []⌝ ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).pre x s }

/-- Generalization of `ErrTailState` for `Stage2ContractsX`, allowing `b = false` on
`e = .invalidMessage x.msgType .badCiphertext` when `aes_256_cbc_decrypt` returns a null pointer. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStateX (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  ∃ b : Bool,
    (b = false → e = .invalidMessage x.msgType .badCiphertext) ∧
    s.readReg64 .x26 = (if b then speTag e else speWord 20) ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG tr ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x38 ∗
      memRegion (sp + 0x140#64) 0x28 ∗
      (if b then speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e
       else memRegion (sp + 0x168#64) 40) ∗
      memRegion (sp + 0x190#64) 0x3f0 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState.toX {A : RustAlloc} {ctl : BitVec 64} {img : Obj.Image}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e draws R s0 s) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStateX A ctl img x trG tr st1 e draws R s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, true, nofun, h.2.2.2.2.1, h.2.2.2.2.2⟩

set_option linter.unusedVariables false in
/-- AES-CBC-parameterized variant of `tryDecryptSpec`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
          s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
          (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
          x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
          x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
        sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
        memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗
        A.pool
      post := fun x s0 sf =>
        ⌜(x.modelFn C decFn S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.modelFn C decFn S uuidParse).1.toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.modelFn C decFn S uuidParse).2) ∗
        decResultFnAt A x.ret (x.modelFn C decFn S uuidParse).1 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
        logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.modelFn C decFn S uuidParse).1 = .error .panic ∨
            S.recvPanics x.st.pqRatchetState x.msg.pqRatchet ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName)
    ((dropChainSpecX A).inImage img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecX (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsX img C A encFn decFn ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkX img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.modelFn C decFn S parse).1 = .error e →
      (x.modelFn C decFn S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStateX A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S0SpecX (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOkExt img A ext →
  RemoteIdentityKeyOkExt img A ext →
  IsSameAccountOkExt img.base ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S1SpecX (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOkX img A ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s'

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S4SpecX (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsX img C A encFn decFn ext →
  CmkOkX img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S6SpecX (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  GenerateKeysOkX img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segVerifyMacPC img) s
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S7SpecX (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsX img C A encFn decFn ext →
  VerifyMacWithAddressesOkX img C A parse ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S8SpecX (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsX img C A encFn decFn ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStateX A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.S9SpecX (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsX img C A encFn decFn ext →
  TrApplyOkX img A ext →
  ClearUpkOkX img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
      (R : SepProp) (s0 s : State),
      (x.modelFn C decFn S parse).1 = .ok pt →
      (x.modelFn C decFn S parse).2 =
        (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptFnSpec C decFn A ctl parse S img) x R s0 s

end CryptoVerification.LibsignalTripleRatchet.Decrypt
