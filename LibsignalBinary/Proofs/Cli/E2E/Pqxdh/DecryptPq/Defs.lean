/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet

/-!
# Segment Checkpoints and Contracts for CLI `try_decrypt_with_state::<Coins>`

Callee `subroutine_ok` bundles, checkpoint PCs (`segS1PC` .. `segS9PC`, `errTailPC`,
`retEpiloguePC`), intermediate stack-frame predicates (`S1State` .. `S9State`, `ErrTailState`), and
segment contracts (`S0Spec` .. `S9Spec`, `ErrTailSpec`, `TryDecryptOk`) for
`libsignal_protocol::session_management::try_decrypt_with_state::<signal_session_handshake::Coins>`
in `libsignalSessionImage`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalSession

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName : String :=
  "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName : String := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name

/-! ## Callee Symbol Names and `subroutine_ok` Hypotheses -/

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.LocalIdentityKeyOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr localIdentityKeyName)
    (localIdentityKeySpec A img)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.RemoteIdentityKeyOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr remoteIdentityKeyName)
    (remoteIdentityKeySpec A img)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_trap
    (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr isSameAccountName)
    isSameAccountSpec

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ClearUpkOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr clearUpkName)
    (clearUpkSpec A)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName)
    (dropChainSpec A)

/-- `core::ptr::drop_glue::<Chain>` satisfies `dropChainSpec A` on `tripleRatchetProgAt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName)
    (dropChainSpec A)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ChainKeyToPbOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr chainKeyToPbName)
    (chainKeyToPbSpec A)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DerivePublicKeyBytesOk_trap
    (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr derivePublicKeyBytesName)
    (derivePublicKeyBytesSpec C.pubKey)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrFromOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  TrFromOkExt img A (trTrapExterns C abs)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrApplyOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  TrApplyOkExt b A (trTrapExterns C abs)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.FindReceiverChainKeyOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  FindReceiverChainKeyOkExt img A (trTrapExterns C abs)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  CreateChainOkExt img C A (trTrapExterns C abs)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GenerateKeysOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  GenerateKeysOkExt img C A (trTrapExterns C abs)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.PublicKeySerializeOk_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs)
    ((trTrapProgAt b C abs).fnAddr publicKeySerializeName)
    (publicKeySerializeSpec A)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.VerifyMacWithAddressesOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr verifyMacWithAddressesName)
    ((verifyMacWithAddressesSpec img C.F A parse).inImage img)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CmkOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr cmkName)
    (CryptoVerification.LibsignalSession.consumeMessageKeySpec C.F A img)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GrowOneChainOk_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr growOneChainName)
    ((CryptoVerification.LibsignalSession.growOneSpec A).inImage img)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap
    (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img spqrRecvName)
    (spqrRecvSpecQF Q Pstk F A S img)

abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_trap
    (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img spqrRecvName)
    ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes))

structure _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop where
  localIk : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.LocalIdentityKeyOk_trap img C A abs
  remoteIk : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.RemoteIdentityKeyOk_trap img C A abs
  sameAcc : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_trap img.base C abs
  clearUpk : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ClearUpkOk_trap img.base C A abs
  dropChain : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs
  chainKeyToPb : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ChainKeyToPbOk_trap img.base C A abs
  derivePk : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DerivePublicKeyBytesOk_trap img.base C abs
  trFrom : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrFromOk_trap img C A abs
  trApply : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrApplyOk_trap img.base C A abs
  findReceiverChainKey : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.FindReceiverChainKeyOk_trap img C A abs
  createChain : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_trap img C A abs
  genKeys : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GenerateKeysOk_trap img C A abs
  pkSer : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.PublicKeySerializeOk_trap img.base C A abs
  verifyMac : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.VerifyMacWithAddressesOk_trap img C A parse abs
  cmk : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CmkOk_trap img C A abs
  growOne : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GrowOneChainOk_trap img C A abs

/-- Bundle of the 16 callee `subroutine_ok` hypotheses consumed by `try_decrypt_with_state`. -/
structure _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop where
  localIk : LocalIdentityKeyOk img C A ctl abs
  remoteIk : RemoteIdentityKeyOk img C A ctl abs
  sameAcc : IsSameAccountOk img.base C ctl abs
  clearUpk : ClearUpkOk img.base C A ctl abs
  dropChain : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk img.base C A ctl abs
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

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap.to_kit
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees_trap img C A parse abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptCallees img C A ctl parse abs where
  localIk := subroutine_ok_kit_of_trTrap h.localIk
  remoteIk := subroutine_ok_kit_of_trTrap h.remoteIk
  sameAcc := subroutine_ok_kit_of_trTrap h.sameAcc
  clearUpk := subroutine_ok_kit_of_trTrap h.clearUpk
  dropChain := subroutine_ok_kit_of_trTrap h.dropChain
  chainKeyToPb := subroutine_ok_kit_of_trTrap h.chainKeyToPb
  derivePk := subroutine_ok_kit_of_trTrap h.derivePk
  trFrom := subroutine_ok_kit_of_trTrap h.trFrom
  trApply := subroutine_ok_kit_of_trTrap h.trApply
  findReceiverChainKey := subroutine_ok_kit_of_trTrap h.findReceiverChainKey
  createChain := subroutine_ok_kit_of_trTrap h.createChain
  genKeys := subroutine_ok_kit_of_trTrap h.genKeys
  pkSer := subroutine_ok_kit_of_trTrap h.pkSer
  verifyMac := subroutine_ok_kit_of_trTrap h.verifyMac
  cmk := subroutine_ok_kit_of_trTrap h.cmk
  growOne := subroutine_ok_kit_of_trTrap h.growOne

/-! ## Frame Layout Constants and Checkpoint PCs -/

/-- Entry address of `try_decrypt_with_state::<signal_session_handshake::Coins>`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName

/-- Segment `S1` entry (`+0x1d8`): `bl TR::from_session_state` after `is_same_account` returns `false` (`w1 = 0`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1d8#64

/-- Segment `S2` entry (`+0x2a4`): `bl RatchetState::find_receiver_chain_key` after `TR::from_session_state` copies `TripleRatchet` (`264` B) to `sp + 0x38..0x140`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x2a4#64

/-- Segment `S3` entry (`+0x500`): inlined `RatchetState::dh_ratchet_step` when `find_receiver_chain_key` returns `Ok(None)`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS3PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x500#64

/-- Segment `S4` entry (`+0x3e4`): join point of `ensureReceiverChain = .ok ck`, before `<ProtocolAddress as Display>::fmt` (`+0x440`) and `consume_message_key` (`+0x474`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x3e4#64

/-- Segment `S5` entry (`+0x5b8`): after `consume_message_key` returns `Ok(mkg)` and the formatted `Display` string at `sp + 0x3d0` is dropped. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS5PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x5b8#64

/-- Segment `S6` entry (`+0x5dc`): after `spqr::recv` (`+0x5cc`) returns `Ok(newPqrState, pqrKey)`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS6PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x5dc#64

/-- Segment `S7` entry (`+0x63c`): after `MessageKeyGenerator::generate_keys` (`+0x638`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS7PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x63c#64

/-- Segment `S8` entry (`+0x678`): after `SignalMessage::verify_mac_with_addresses` (`+0x65c`) returns `Ok(true)`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS8PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x678#64

/-- Segment `S9` entry (`+0x6a4`): after `aes_256_cbc_decrypt` (`+0x694`) returns `some pt`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS9PC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x6a4#64

/-- `ErrTail` entry (`+0x30c`): shared `TripleRatchet` drop and error-return block after `TR::from_session_state` has moved `receiver_chains` and `pq_ratchet_state` out of `x.ss`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x30c#64

/-- `ErrTail` chain-drop loop header (`+0x33c`): `bl drop_glue<Chain>` advancing `x19` by `104` B (`0x68`) and decrementing `x21`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errDropChainLoopPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x33c#64

/-- Shared return epilogue (`+0x394 .. +0x3b0`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x394#64

/-! ## Stack Frame Predicates and Intermediate Checkpoint States -/

set_option linter.unusedVariables false in
/-- Borrowed read-only inputs and environment resources kept unchanged across the execution of
`try_decrypt_with_state` (with `draws` bytes consumed from the RNG tape: `0` before S3 and on the
`findReceiverChainKey = .ok (some _)` path, `min 32 x.rest.length` after `rng_fill` in S3). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (draws : Nat) (s0 : State) : SepProp :=
  protocolAddressAt A x.rem x.remA ∗
  protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
  logOff img ∗
  stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
  tryDecryptSavedRegs s0.sp s0 ∗
  A.pool

/-- `ErrTail` checkpoint state (`+0x30c`): `TR::from_session_state` has produced `st1`,
`x19 = x.ret`, `x20 = sp + 0x140`, `x26 = speTag e`, `sp + 0x168..0x190` holds `speBodyAt`, and
`sp + 0x38..0x140` holds `trAt A (sp + 0x38) trG tr` awaiting cleanup. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img ∧
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
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- Segment `S1` checkpoint state (`+0x1d8`): prologue and identity/same-account checks have
completed with `w1 = 0` (`self_session = false`), `x19 = x.ret`, `x20 = sp + 0x140`, `x21 = x.ss`,
`x22 = x.msgA`, `x23 = sp + 0x500`, `x24[7:0] = msgTypeByte x.msgType`, `x25 = x.locA`, and
`[sp + 0x30] = x.remA` inside the 1408-byte (`0x580`) stack frame. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img ∧
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
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- Segment `S2` checkpoint state (`+0x2a4`): `TR::from_session_state` returned `(.ok tr, st1)` with
`tr` (`264` B) at `sp + 0x38..0x140`, `[sp + 0x20] = x.locA`, `[sp + 0x28] = x.msg.counter`, and
`x0 = sp + 0x38`, `x1 = x.msgA + 0x38`, `x8 = sp + 0x190` prepared for `find_receiver_chain_key`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC img ∧
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
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- Segment `S3` checkpoint state (`+0x500`): `find_receiver_chain_key` returned `Ok(None)`, entering inlined `dh_ratchet_step` with `x12 = sp + 0x2c0`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS3PC img ∧
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
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- Segment `S4` checkpoint state (`+0x3e4`): join point after `ensureReceiverChain = .ok ck`, with
`(chainKeyBytes ck).take 20` at `sp + 0x2c0..0x2d4`, `(chainKeyBytes ck).drop 20` at
`sp + 0x2b0..0x2c0`, and `x12 = sp + 0x2c0` ready to reassemble `ck` at `sp + 0x2e0..0x304`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img ∧
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
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- Segment `S5` checkpoint state (`+0x5b8`): `consume_message_key` returned `Ok(mkg)` and its
formatted `Display` string is freed; `[sp + 0x1c]` saves `msgW` (low byte `msgTypeByte x.msgType`),
`w24 = 1#32` (`Seed` tag), and `mkg` is split across `[sp + 0x28]` (`cap`), `[sp + 0x10]` (`ptr`),
`[sp + 0x450]` (`len = 32`), and `[sp + 0x458]` (`counter`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS5PC img ∧
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
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- Segment `S6` checkpoint state (`+0x5dc`): `spqr::recv` returned `Ok(newPqrState, pqrKey)` at `sp + 0x500..0x530` with `x8 = newPqrCap`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS6PC img ∧
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
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- Segment `S7` checkpoint state (`+0x63c`): `generate_keys` wrote `mks` (`84` B) to `sp + 0x500..0x554`, with `newPqrState` saved in `([sp + 0x8], [sp + 0x28], x24)`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS7PC img ∧
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
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length)
          (newPqrCap.toNat - newPqrState.length)) ∗
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
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- Segment `S8` checkpoint state (`+0x678`): `verify_mac_with_addresses` returned `Ok(true)`, preserving the `S7State` frame at `segS8PC img`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS8PC img ∧
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
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length)
          (newPqrCap.toNat - newPqrState.length)) ∗
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
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- Segment `S9` checkpoint state (`+0x6a4`): `aes_256_cbc_decrypt` returned `some pt` as `vecU8 A (sp + 0x3d0) pt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS9PC img ∧
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
        memRegion (newPqrPtr + BitVec.ofNat 64 newPqrState.length)
          (newPqrCap.toNat - newPqrState.length)) ∗
      vecU8 A (sp + 0x3d0#64) pt ∗
      memRegion x.ret 48 ∗
      memRegion sp 8 ∗
      ((sp + 0x8#64) ↦₆₄ newPqrCap) ∗
      memRegion (sp + 0x10#64) 0x18 ∗
      ((sp + 0x28#64) ↦₆₄ newPqrPtr) ∗
      memRegion (sp + 0x30#64) 8 ∗
      memRegion (sp + 0x140#64) 0x290 ∗
      memRegion (sp + 0x3e8#64) 0x198 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-! ## Segment Contracts and `TryDecryptOk` -/

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

/-- `ErrTail` contract (`+0x30c → +0x3b0`): writes `speAt A (utf8 "decrypt") x.ret e`, drops all
chains in `tr.ratchet.receiver_chains`, deallocates the `receiver_chains` and `tr.pqr_state`
buffers, restores callee-saved registers and `sp`, and returns. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.LocalIdentityKeyOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.RemoteIdentityKeyOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountOk_trap img.base C abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img) s0
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0)

/-- Segment `S0` contract (`+0x000 → +0x1d8`): executes the prologue, `local_identity_key`,
`remote_identity_key`, and either the `remoteIdentity = none` log path or `is_same_account = false`,
reaching `S1State` at `segS1PC img`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOk img C A ctl abs →
  RemoteIdentityKeyOk img C A ctl abs →
  IsSameAccountOk img.base C ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img) s0
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrFromOk_trap img C A abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (trTrapProgAt img.base C abs)
          (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s'

/-- Segment `S1` contract (`+0x1d8 → +0x2a4 / +0x3b0`): runs `TR::from_session_state(x.ss, false)`,
returning early with `Err` when `x.st.remoteIdentity = none` or copying `tr` (`264` B) to
`sp + 0x38..0x140` and reaching `S2State` at `segS2PC img`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
          (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s'

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.FindReceiverChainKeyOk_trap img C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS3PC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3State A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e 0 R s0)

/-- Segment `S2` contract (`+0x2a4 → +0x3e4 / +0x500 / +0x30c`): calls `find_receiver_chain_key`
and branches to `S4State` (`.ok (some ck)`), `S3State` (`.ok none`), or `ErrTailState` (`.error e`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  FindReceiverChainKeyOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS3PC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3State A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img) s
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e 0 R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CreateChainOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DerivePublicKeyBytesOk_trap img.base C abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.PublicKeySerializeOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ChainKeyToPbOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GrowOneChainOk_trap img C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk_trap img.base C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3State A ctl img x trG tr st1 R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((∃ trG' r1,
              CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment `S3` contract (`+0x500 → +0x3e4 / +0x30c` or panic): runs inlined `dh_ratchet_step`
when `findReceiverChainKey = .ok none`, reaching `S4State` on `.ok ck` or `ErrTailState` on
`.error e` (assuming `receiverChains.length < 2 ^ 32` to rule out `CapacityOverflow` in `grow_one`,
and `rootStack ≤ s0.sp.toNat` so stack salt pointers `sp + 0x3b0` and `sp + 0x4a0` are non-null). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CreateChainOk img C A ctl abs →
  DerivePublicKeyBytesOk img.base C ctl abs →
  PublicKeySerializeOk img.base C A ctl abs →
  ChainKeyToPbOk img.base C A ctl abs →
  GrowOneChainOk img C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S3State A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG' r1,
              CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.CmkOk_trap img C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG tr st1 ck draws R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5State A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

/-- Segment `S4` contract (`+0x3e4 → +0x5b8 / +0x30c` or panic): formats `x.rem`, calls
`consume_message_key`, drops the formatted string, and branches to `S5State` (`.ok mkg`), panic
(`.error .panic`), or `ErrTailState` (`.error e`, `e ≠ .panic`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CmkOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S4State A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5State A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF_trap (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp) (img : Obj.Image)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQF_trap Q Pstk F C A S abs img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      Pstk (s0.sp - 1504#64).toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5State A ctl img x trG tr st1 mkg draws (F ∗ R) s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Frame- and state-predicate-parameterized Segment `S5` contract (`+0x5b8 → +0x5dc / +0x30c` or panic). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5SpecQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp) (img : Obj.Image)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  SpqrRecvOkQF Q Pstk F C A ctl S abs img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      Pstk (s0.sp - 1504#64).toNat →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5State A ctl img x trG tr st1 mkg draws (F ∗ R) s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5Spec_trap (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SpqrRecvOkQ_trap Q C A S abs img →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      tr.pqrState = x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5State A ctl img x trG tr st1 mkg draws R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment `S5` contract (`+0x5b8 → +0x5dc / +0x30c` or panic): calls `spqr::recv` under
`SpqrRecvOkQ Q`, reaching `S6State` on `.ok (newPqrState, pqrKey)` or formatting the error, freeing
`mkg.seed`, and reaching `ErrTailState` on `.error sd`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5Spec (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
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
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S5State A ctl img x trG tr st1 mkg draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GenerateKeysOk_trap img C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS7PC img) s
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

/-- Segment `S6` contract (`+0x5dc → +0x63c`): saves `newPqrState`, stages `mkg` (`mkg.seed.length = 32`)
and `pqrKey`, and calls `MessageKeyGenerator::generate_keys`, reaching `S7State`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  GenerateKeysOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS7PC img) s
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.VerifyMacWithAddressesOk_trap img C A parse abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (trTrapProgAt img.base C abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (trTrapProgAt img.base C abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1
              (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment `S7` contract (`+0x63c → +0x678 / +0x30c` or panic): calls `verify_mac_with_addresses`,
reaching `S8State` on `true` or allocating `"bad authentication code"`, freeing `newPqrState`, and
reaching `ErrTailState` on `false`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  VerifyMacWithAddressesOk img C A ctl parse abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S7State A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1
              (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (trTrapProgAt img.base C abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9State A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (trTrapProgAt img.base C abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment `S8` contract (`+0x678 → +0x6a4 / +0x30c` or panic): calls `aes_256_cbc_decrypt`,
reaching `S9State` on `some pt` or formatting `"bad ciphertext"`, freeing `newPqrState`, and
reaching `ErrTailState` on `none`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9State A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TrApplyOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.ClearUpkOk_trap img.base C A abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
      (R : SepProp) (s0 s : State),
      (x.model C S parse).1 = .ok pt →
      (x.model C S parse).2 =
        (({ tr with pqrState := newPqrState }).applyToSessionState
          st1).clearUnacknowledgedPreKeyMessage →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9State A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

/-- Segment `S9` contract (`+0x6a4 → +0x3b0` or panic): frees old `tr.pqr_state`, installs
`newPqrState`, writes `Ok(pt)` to `x.ret`, calls `TR::apply_to_session_state` and
`clear_unacknowledged_pre_key_message`, and returns via the epilogue. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
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
        (({ tr with pqrState := newPqrState }).applyToSessionState
          st1).clearUnacknowledgedPreKeyMessage →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S9State A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s
    post := fun x s0 sf => F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).post x s0 sf }

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOkQF_trap (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF Q F C A ctl parse S img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOkQF (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img)
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF Q F C A ctl parse S img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk_trap (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

/-- Full `subroutine_ok` statement for `try_decrypt_with_state::<signal_session_handshake::Coins>` restricted to PQ states satisfying `Q`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptOk_of_okQF_trap {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOkQF_trap Q emp img C A ctl parse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk_trap Q img C A ctl parse S abs := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF, Spec.restrictPre] at hpre ⊢
    rwa [emp_sepConj]
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF, Spec.restrictPre] at hpost ⊢
    rwa [emp_sepConj] at hpost

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptOk_of_okQF {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOkQF Q emp img C A ctl parse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptOk Q img C A ctl parse S abs := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF, Spec.restrictPre] at hpre ⊢
    rwa [emp_sepConj]
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptSpecQF, Spec.restrictPre] at hpost ⊢
    rwa [emp_sepConj] at hpost

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
