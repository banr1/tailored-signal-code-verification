/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs

/-!
# Segment Specifications and Checkpoint States for `try_decrypt_with_state`

Defines callee `subroutine_ok` bundles (`TryDecryptCallees`, `TryDecryptCalleesExt`,
`TryDecryptCalleesX`), stack-frame layout constants, checkpoint PCs (`segLoadRatchetPC` ..
`segApplyRatchetPC`, `errTailPC`), intermediate machine-state invariants (`LoadRatchetState` ..
`ApplyRatchetState`, `ErrTailState`), and segment contracts (`IdentityKeysSpec` ..
`ApplyRatchetSpec`, `ErrTailSpec`) partitioning `try_decrypt_with_state` across fixed-image,
`Stage2ContractsX` (`decFn`), and relocatable `[LibsignalPlacement]` forms.
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

/-! ## 1. Callee Symbol Names and `subroutine_ok` Hypotheses -/

/-- `<SessionState>::local_identity_key` (`0x119f4`, called at `+0x050`) meets
`localIdentityKeySpec A img` on `tripleRatchetProgAt`. -/
def LocalIdentityKeyOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr localIdentityKeyName) (localIdentityKeySpec A img)

/-- `<IdentityKey>::is_same_account` (`0xacec`, called at `+0x1d0`) meets `isSameAccountSpec` on
`tripleRatchetProgAt`. -/
def IsSameAccountOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr isSameAccountName)
    isSameAccountSpec

/-- `<SessionState>::clear_unacknowledged_pre_key_message` (`0x12404`, called at `+0x4f0`) meets
`clearUpkSpec A` on `tripleRatchetProgAt`. -/
def ClearUpkOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr clearUpkName)
    (clearUpkSpec A)

/-- `core::ptr::drop_glue::<Chain>` (`0x35dc8`, called at `+0x340` and `+0xb88`) meets
`dropChainSpec A` on `tripleRatchetProgAt`. -/
def DropChainOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr dropChainName)
    (dropChainSpec A)

/-- `<ChainKey>::to_pb` (`0xcf68`, called at `+0xa80`) meets `chainKeyToPbSpec A` on
`tripleRatchetProgAt`. -/
def ChainKeyToPbOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chainKeyToPbName)
    (chainKeyToPbSpec A)

/-- `<PrivateKey>::derive_public_key_bytes` (`0x3db4c`, called at `+0x7b0`) meets
`derivePublicKeyBytesSpec C.pubKey` on `tripleRatchetProgAt`. -/
def DerivePublicKeyBytesOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr derivePublicKeyBytesName)
    (derivePublicKeyBytesSpec C.pubKey)

/-- `<SignalMessage>::verify_mac_with_addresses` (`0x1d5a0`, called at `+0x65c`) meets
`(verifyMacWithAddressesSpec img C.F A parse).inImage img` on `tripleRatchetProgAt`. -/
def VerifyMacWithAddressesOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr verifyMacWithAddressesName)
    ((verifyMacWithAddressesSpec img C.F A parse).inImage img)

/-- Base-program callee symbol name (`0xded8`): `<RatchetState>::consume_message_key`. -/
abbrev cmkName : String := "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

/-- `<RatchetState>::consume_message_key` (`0xded8`, called at `+0x474`) meets
`consumeMessageKeySpec C.F A img` on `tripleRatchetProgAt`. -/
def CmkOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) ((tripleRatchetProgAt img.base C ctl abs).fnAddr cmkName)
    (CryptoVerification.LibsignalSession.consumeMessageKeySpec C.F A img)

/-- Callee symbol `<RawVec<MessageKey>>::grow_one` (`0x15cac`, called at `+0xa98` for
`RawVec<Chain>`, sharing element size `104` and alignment `8`). -/
abbrev growOneChainName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"

/-- `<RawVec<MessageKey>>::grow_one` (`0x15cac`, called at `+0xa98`) meets
`(growOneSpec A).inImage img` on `tripleRatchetProgAt`. -/
def GrowOneChainOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr growOneChainName)
    ((CryptoVerification.LibsignalSession.growOneSpec A).inImage img)

/-- Bundle of all 16 callee `subroutine_ok` hypotheses required by `try_decrypt_with_state`. -/
structure TryDecryptCallees (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop where
  localIk : LocalIdentityKeyOk img C A ctl abs
  remoteIk : RemoteIdentityKeyOk img C A ctl abs
  sameAcc : IsSameAccountOk img.base C ctl abs
  clearUpk : ClearUpkOk img.base C A ctl abs
  dropChain : DropChainOk img.base C A ctl abs
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

def LocalIdentityKeyOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr localIdentityKeyName) (localIdentityKeySpec A img)

def RemoteIdentityKeyOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr remoteIdentityKeyName) (remoteIdentityKeySpec A img)

def IsSameAccountOkExt (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr isSameAccountName)
    isSameAccountSpec

def ClearUpkOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr clearUpkName)
    (clearUpkSpec A)

def DropChainOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr dropChainName)
    (dropChainSpec A)

def ChainKeyToPbOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName)
    (chainKeyToPbSpec A)

def DerivePublicKeyBytesOkExt (b : BitVec 64) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr derivePublicKeyBytesName)
    (derivePublicKeyBytesSpec C.pubKey)

def VerifyMacWithAddressesOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
    ((verifyMacWithAddressesSpec img C.F A parse).inImage img)

def CmkOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr cmkName)
    (CryptoVerification.LibsignalSession.consumeMessageKeySpec C.F A img)

def GrowOneChainOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr growOneChainName)
    ((CryptoVerification.LibsignalSession.growOneSpec A).inImage img)

/-- Bundle of all 16 callee `subroutine_ok` hypotheses on `tripleRatchetProgAtExt img.base ext`. -/
structure TryDecryptCalleesExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop where
  localIk : LocalIdentityKeyOkExt img A ext
  remoteIk : RemoteIdentityKeyOkExt img A ext
  sameAcc : IsSameAccountOkExt img.base ext
  clearUpk : ClearUpkOkExt img.base A ext
  dropChain : DropChainOkExt img.base A ext
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

theorem TryDecryptCallees.toExt {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : TryDecryptCallees img C A ctl uuidTryParse abs) :
    TryDecryptCalleesExt img C A uuidTryParse (tripleRatchetExterns C ctl abs) :=
  ⟨h.localIk, h.remoteIk, h.sameAcc, h.clearUpk, h.dropChain, h.chainKeyToPb, h.derivePk,
   h.trFrom, h.trApply, h.findReceiverChainKey, h.createChain, h.genKeys, h.pkSer, h.verifyMac, h.cmk, h.growOne⟩

/-! ## 2. Frame Layout Constants and Checkpoint PCs (`tryDecryptEntry img = img.base + 0x3439c#64`) -/

/-- Entry address of `try_decrypt_with_state::<HookRng>` (`0x3439c`). -/
abbrev tryDecryptEntry (img : Obj.Image) : BitVec 64 := entryOf img tryDecryptName

/-- Own stack frame size of `try_decrypt_with_state` (`+0x000: stp x29, x30, [sp, #-0x60]!` and
`+0x01c: sub sp, sp, #0x580`, total `0x5e0` = 1504 B, restored at `+0x394 .. +0x3ac`). -/
abbrev tryDecryptFrameSize : Nat := 1504

/-- Stack budget below `sp = s0.sp - 1504#64` available to callees of `try_decrypt_with_state`
(`rootStack - 1504 = 262144 - 1504 = 260640` B, which exceeds every callee stack budget including
`smallRootStack = 65536` B for `TR::from_session_state`, `spqrRecvStack = 16384` B, and
`cmkStack = 8192` B). -/
abbrev tryDecryptSubStack : Nat := rootStack - tryDecryptFrameSize

/-- S1 entry (`+0x1d8` = `0x34574`), right before `bl TR::from_session_state` with `w1 = 0`
(`self_session = false`). -/
abbrev segLoadRatchetPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x1d8#64

/-- S2 entry (`+0x2a4` = `0x39b1c`), at `bl RatchetState::find_receiver_chain_key` after copying
`TripleRatchet` (`264` B) to `sp + 0x38..0x140`. -/
abbrev segFindChainPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x2a4#64

/-- S3 entry (`+0x500` = `0x3489c`), entering the inlined `RatchetState::dh_ratchet_step` body when
`find_receiver_chain_key` returns `Ok(None)`. -/
abbrev segDhStepPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x500#64

/-- S3 eviction loop header (`+0xb04` = `0x34ea0`), removing the oldest receiver chain via
`memmove` and `drop_glue<Chain>` while `receiver_chains.length ≥ 6`. -/
abbrev s3EvictLoopPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0xb04#64

/-- S4 entry (`+0x3e4` = `0x34780`), join point where `ensureReceiverChain = .ok ck` before
`<ProtocolAddress as Display>::fmt` (`+0x440`) and `RatchetState::consume_message_key` (`+0x474`). -/
abbrev segConsumeMsgKeyPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x3e4#64

/-- S5 entry (`+0x5b8` = `0x34954`), after `consume_message_key` returns `Ok(mkg)` and the
formatted `Display` `String` at `sp + 0x3d0` has been dropped. -/
abbrev segPqRecvPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x5b8#64

/-- S6 entry (`+0x5dc` = `0x34978`), after `spqr::recv` (`+0x5cc`) returns
`Ok(newPqrState, pqrKey)`. -/
abbrev segDeriveKeysPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x5dc#64

/-- S7 entry (`+0x63c` = `0x349d8`), right after `MessageKeyGenerator::generate_keys` returns at
`+0x638`. -/
abbrev segVerifyMacPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x63c#64

/-- S8 entry (`+0x678` = `0x34a14`), after `SignalMessage::verify_mac_with_addresses` (`+0x65c`)
returns `Ok(true)`. -/
abbrev segAesDecryptPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x678#64

/-- S9 entry (`+0x6a4` = `0x34a40`), after `aes_256_cbc_decrypt` (`+0x694`) returns `some pt`. -/
abbrev segApplyRatchetPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x6a4#64

/-- `ErrTail` entry (`+0x30c` = `0x346a8`), shared `TripleRatchet` cleanup and error-return block
after `TR::from_session_state` has extracted `receiver_chains` and `pq_ratchet_state`. -/
abbrev errTailPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x30c#64

/-- `ErrTail` chain-drop loop header (`+0x33c` = `0x346d8`), advancing `x19` by `0x68` (`104` B)
and decrementing `x21` across `tr.ratchet.receiver_chains`. -/
abbrev errDropChainLoopPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x33c#64

/-- Shared return epilogue (`+0x394` = `0x34730`, `+0x394 .. +0x3b0`), restoring `sp` and
`x19..x30` before `ret`. -/
abbrev retEpiloguePC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x394#64

/-! ## 3. Machine Metadata, Stack Frame Predicates, and Intermediate Checkpoint States -/

/-- Callee-saved register save area `[sp0 - 96#64 .. sp0]` (`[sp + 0x580 .. sp + 0x5e0]`, 96 bytes)
written by the prologue `+0x000 .. +0x014` and restored by `+0x394 .. +0x3ac`. -/
def tryDecryptSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Common machine metadata invariant at every internal checkpoint after the prologue
(`+0x000 .. +0x01c`): `s` is `.Running` with `sp = s0.sp - 1504#64` (16-byte aligned),
`x29 = s0.sp - 96#64 = s.sp + 0x580#64`, `trace` unchanged from `s0`, and the image's frozen
sections and symbol table preserved. -/
def tryDecryptMidMeta (img : Obj.Image) (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp - 1504#64 ∧
  s0.spAligned = true ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = s0.sp - 96#64 ∧
  s.trace = s0.trace ∧
  img.FrozenLoaded s ∧
  s.symtab = img.symtab ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

/-- Borrowed read-only inputs and environment resources kept unchanged across the execution of
`try_decrypt_with_state` (with `draws` bytes consumed from the RNG tape: `0` before S3 and on the
`findReceiverChainKey = .ok (some _)` path, `min 32 x.rest.length` after `rng_fill` in S3). -/
def tryDecryptCommonHeap (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (draws : Nat) (s0 : State) : SepProp :=
  protocolAddressAt A x.rem x.remA ∗
  protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  tapeAfter ctl x.cur x.rest draws ∗
  logOff img ∗
  stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
  tryDecryptSavedRegs s0.sp s0 ∗
  A.pool

/-- Word 0 (`x26` at `errTailPC`) of `speAt` for `e`. -/
def speTag : SignalProtocolError → BitVec 64
  | .invalidState => speWord 1
  | .ciphertextMessageTooShort _ => speWord 3
  | .legacyCiphertextVersion _ => speWord 4
  | .unrecognizedCiphertextVersion _ => speWord 5
  | .invalidProtobufEncoding => speWord 2
  | .noKeyTypeIdentifier => speWord 7
  | .badKeyType _ => speWord 8
  | .badKeyLength _ => speWord 9
  | .invalidKeyAgreement => speWord 10
  | .invalidSessionStructure _ => speWord 20
  | .duplicatedMessage _ _ => speWord 23
  | .invalidMessage _ _ => speWord 24
  | .panic => 0#64

/-- The 40-byte payload of `speAt A fnName a e` at `p = a + 8#64` (`sp + 0x168..0x190` at
`errTailPC`). -/
def speBodyAt (A : RustAlloc) (fnName : List (BitVec 8)) (p : BitVec 64) :
    SignalProtocolError → SepProp
  | .invalidState =>
    (∃∗ bs : List (BitVec 8), vecU8 A p bs) ∗ strRefAt (p + 24#64) fnName
  | .ciphertextMessageTooShort n =>
    (p ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (p + 8#64) 32
  | .legacyCiphertextVersion v =>
    (p ↦₈ v) ∗ memRegion (p + 1#64) 39
  | .unrecognizedCiphertextVersion v =>
    (p ↦₈ v) ∗ memRegion (p + 1#64) 39
  | .invalidProtobufEncoding => memRegion p 40
  | .noKeyTypeIdentifier => memRegion p 40
  | .badKeyType t => (p ↦₈ t) ∗ memRegion (p + 1#64) 39
  | .badKeyLength n =>
    (p ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (p + 8#64) 32
  | .invalidKeyAgreement => memRegion p 40
  | .invalidSessionStructure r =>
    strRefAt p (invalidSessionStructureStr r) ∗ memRegion (p + 16#64) 24
  | .duplicatedMessage i c =>
    (p ↦₃₂ i) ∗ ((p + 4#64) ↦₃₂ c) ∗ memRegion (p + 8#64) 32
  | .invalidMessage t r =>
    invalidMessageStrAt A p r ∗ ((p + 24#64) ↦₈ msgTypeByte t) ∗ memRegion (p + 25#64) 15
  | .panic => ⌜False⌝

/-- `ErrTail` checkpoint state at `errTailPC img` (`+0x30c`) after `TR::from_session_state`
succeeds (`st1 = (Mut.exec TripleRatchet.fromSessionState x.st).2`):
* `x19 = x.ret`, `x20 = sp + 0x140`, `x26 = speTag e`;
* `sp + 0x168..0x190` holds `speBodyAt A (utf8 "decrypt") (sp + 0x168) e`;
* `sp + 0x38..0x140` holds `trAt A (sp + 0x38) trG tr`. -/
def ErrTailState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = errTailPC img ∧
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
    tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S1 checkpoint state at `segLoadRatchetPC img` (`+0x1d8`), after identity-key checks complete
with `w1 = 0` (`self_session = false`):
* `x19 = x.ret`, `x20 = sp + 0x140`, `x21 = x.ss`, `x22 = x.msgA`, `x23 = sp + 0x500`,
  `(x24).setWidth 8 = msgTypeByte x.msgType`, `x25 = x.locA`, `(x1).setWidth 32 = 0#32`;
* `[sp + 0x30] = x.remA`, with scratch regions `[sp .. sp + 0x30]` and `[sp + 0x38 .. sp + 0x580]`. -/
def LoadRatchetState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segLoadRatchetPC img ∧
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
    tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- S2 checkpoint state at `segFindChainPC img` (`+0x2a4`), after `TR::from_session_state` returns
`Ok(tr)` (`264` B copied to `sp + 0x38..0x140`), `[sp + 0x20] = x.locA`, `[sp + 0x28] = x.msg.counter`,
and `(x0, x1, x8) = (sp + 0x38, x.msgA + 0x38, sp + 0x190)` are set for `find_receiver_chain_key`. -/
def FindChainState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segFindChainPC img ∧
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
    tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- S3 checkpoint state at `segDhStepPC img` (`+0x500`), when `find_receiver_chain_key` returns
`Ok(None)` (`w9 = 0`) and execution enters `RatchetState::dh_ratchet_step` with `x12 = sp + 0x2c0`. -/
def DhStepState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segDhStepPC img ∧
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
    tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)

/-- S4 checkpoint state at `segConsumeMsgKeyPC img` (`+0x3e4`), join point after
`ensureReceiverChain = .ok ck`: `chainKeyBytes ck` (`36` B) is split across `sp + 0x2c0..0x2d4`
(first `20` B) and `sp + 0x2b0..0x2c0` (last `16` B) with `x12 = sp + 0x2c0`. -/
def ConsumeMsgKeyState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segConsumeMsgKeyPC img ∧
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
    tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S5 checkpoint state at `segPqRecvPC img` (`+0x5b8`), after `consume_message_key` returns
`Ok(mkg)` and its formatted `Display` string is freed: `[sp + 0x1c]` holds `msgW` (low byte
`msgTypeByte x.msgType`), `w24 = 1#32` (`Seed` tag), and `mkg.seed` (`32` B) + `mkg.counter` are
staged across `[sp + 0x28]`, `[sp + 0x10]`, `[sp + 0x450]`, and `[sp + 0x458]`. -/
def PqRecvState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segPqRecvPC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S6 checkpoint state at `segDeriveKeysPC img` (`+0x5dc`), after `spqr::recv` writes
`Ok(newPqrState, pqrKey)` at `sp + 0x500..0x530` with `x8 = newPqrCap`. -/
def DeriveKeysState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segDeriveKeysPC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S7 checkpoint state at `segVerifyMacPC img` (`+0x63c`), after `MessageKeyGenerator::generate_keys`
writes `mks = mkg.generateKeys C.F pqrKey` (`84` B) at `sp + 0x500..0x554` and `newPqrState` is
saved across `[sp + 0x8]`, `[sp + 0x28]`, and `x24`. -/
def VerifyMacState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segVerifyMacPC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S8 checkpoint state at `segAesDecryptPC img` (`+0x678`), after
`SignalMessage::verify_mac_with_addresses` returns `Ok(true)`. -/
def AesDecryptState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segAesDecryptPC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- S9 checkpoint state at `segApplyRatchetPC img` (`+0x6a4`), after `aes_256_cbc_decrypt` writes
`vecU8 A (sp + 0x3d0) pt` at `sp + 0x3d0..0x3e8`. -/
def ApplyRatchetState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segApplyRatchetPC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-! ## 4. Segment Contracts `IdentityKeysSpec` .. `ApplyRatchetSpec`, `ErrTailSpec`, and `TryDecryptOk` -/

/-- `ErrTail` contract (`+0x30c → +0x394 → +0x3b0`): from `ErrTailState` when
`(x.model C S parse).1 = .error e` (`e ≠ .panic`), writes `speAt A (utf8 "decrypt") x.ret e`, drops
`tr.ratchet.receiver_chains` and `tr.pqr_state`, and returns via the epilogue `+0x394 .. +0x3b0`. -/
def ErrTailSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (tryDecryptSpec C A ctl parse S img) x R s0 s

/-- Segment S0 contract (`+0x000 → +0x1d8`): from `tryDecryptEntry img`, runs the prologue,
`local_identity_key`, `remote_identity_key`, and either the `remoteIdentity = none` log-filter path
or `is_same_account` (returning `false` since `x.st.remoteIdentity ≠ some x.st.localIdentity`),
reaching `LoadRatchetState`. -/
def IdentityKeysSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOk img C A ctl abs →
  RemoteIdentityKeyOk img C A ctl abs →
  IsSameAccountOk img.base C ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segLoadRatchetPC img) s0
        (LoadRatchetState A ctl img x R s0)

/-- Segment S1 contract (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`): calls
`TR::from_session_state(x.ss, false)` (`+0x1e0`), either writing the SPE error and returning via
`+0x394 .. +0x3b0` or copying `tr` (`264` B) to `sp + 0x38..0x140` to reach `FindChainState`. -/
def LoadRatchetSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      LoadRatchetState A ctl img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
          (tryDecryptSpec C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ∃ trG, FindChainState A ctl img x trG tr st1 R s0 s'

/-- Segment S2 contract (`+0x2a4 → +0x3e4 / +0x500 / +0x30c`): calls
`RatchetState::find_receiver_chain_key` and branches on `tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey`
to `ConsumeMsgKeyState` (`.ok (some ck)`), `DhStepState` (`.ok none`), or `ErrTailState` (`.error e`). -/
def FindChainSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  FindReceiverChainKeyOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      FindChainState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segConsumeMsgKeyPC img) s
          (ConsumeMsgKeyState A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segDhStepPC img) s
          (DhStepState A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (errTailPC img) s
          (ErrTailState A ctl img x trG tr st1 e 0 R s0)

/-- Segment S3 contract (`+0x500 → +0x3e4 / +0x30c` or OOM panic): runs the inlined
`RatchetState::dh_ratchet_step` when `findReceiverChainKey = .ok none`, reaching
`ConsumeMsgKeyState` on `.ok ck` (with `draws = min 32 x.rest.length`) or `ErrTailState` on
`.error e`. Assumes `tr.ratchet.receiverChains.length < 2 ^ 32` (no `CapacityOverflow` in
`grow_one`) and `rootStack ≤ s0.sp.toNat` (non-null stack salt pointers for `Hkdf::extract`). -/
def DhStepSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CreateChainOk img C A ctl abs →
  DerivePublicKeyBytesOk img.base C ctl abs →
  PublicKeySerializeOk img.base C A ctl abs →
  ChainKeyToPbOk img.base C A ctl abs →
  GrowOneChainOk img C A ctl abs →
  DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      DhStepState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG' r1, ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment S4 contract (`+0x3e4 → +0x5b8 / +0x30c` or panic): formats `x.rem` via
`<ProtocolAddress as Display>::fmt`, calls `RatchetState::consume_message_key`, drops the formatted
`String`, and reaches `PqRecvState` (`.ok mkg`), panics (`.error .panic`), or reaches
`ErrTailState` (`.error e`, `e ≠ .panic`). -/
def ConsumeMsgKeySpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CmkOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      ConsumeMsgKeyState A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

/-- `SpqrRecvOk` on the states meeting `Q`: the in-image `spqr::recv` meets `spqrRecvSpec`
restricted to `Q x.1.bytes`. `Q := fun _ => True` is implied by `SpqrRecvOk`
(`spqrRecvOkQ_of_recvOk`) and `Q := (· = [])` is the conclusion of `SpqrRecvEmptyRunStmt`
(`spqrRecvOkQ_empty`). -/
def SpqrRecvOkQ (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrRecvName)
    ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes))

theorem spqrRecvOkQ_of_recvOk {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image}
    (h : SpqrRecvOk C A ctl S abs img) : SpqrRecvOkQ Q C A ctl S abs img :=
  Spec.subroutine_ok_restrictPre _ h

theorem spqrRecvOkQ_empty {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)} {img : Obj.Image}
    (h : SpqrRecvEmptyRunStmt C A ctl S abs img) (hhooks : TripleRatchetHooks C A S abs)
    (hempty : S.RecvEmptyOk) (hloads : Obj.Loads libsignalSessionImage img) :
    SpqrRecvOkQ (· = []) C A ctl S abs img :=
  h hhooks hempty hloads

/-- `spqrRecvSpec` restricted to states meeting `Q x.1.bytes` with message length `< 2 ^ 40`,
stack `Pstk s.sp.toNat`, and an extra frame `F` preserved from `pre` to `post`. -/
def spqrRecvSpecQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) : Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvSpec A S img with
    pre := fun x s =>
      ⌜Q x.1.bytes ∧ x.2.1.bytes.length < 2 ^ 40 ∧ Pstk s.sp.toNat⌝ ∗
        F ∗ (spqrRecvSpec A S img).pre x s
    post := fun x s0 sf => F ∗ (spqrRecvSpec A S img).post x s0 sf }

def SpqrRecvOkQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrRecvName)
    (spqrRecvSpecQF Q Pstk F A S img)

theorem subroutine_ok_spqrRecvSpecQF_emp {Q : List (BitVec 8) → Prop} {prog : Program}
    {entry : BitVec 64} {A : RustAlloc} {S : SpqrModel} {img : Obj.Image}
    (h : subroutine_ok prog entry ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes))) :
    subroutine_ok prog entry (spqrRecvSpecQF Q (fun _ => True) emp A S img) := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)
  · dsimp only [spqrRecvSpecQF, Spec.restrictPre] at hpre ⊢
    rw [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.1, hpre.2⟩
  · dsimp only [spqrRecvSpecQF, Spec.restrictPre] at hpost ⊢
    rwa [emp_sepConj]

theorem spqrRecvOkQF_of_okQ {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)} {img : Obj.Image}
    (h : SpqrRecvOkQ Q C A ctl S abs img) :
    SpqrRecvOkQF Q (fun _ => True) emp C A ctl S abs img :=
  subroutine_ok_spqrRecvSpecQF_emp h

/-- Segment S5 contract (`+0x5b8 → +0x5dc / +0x30c` or panic): calls `spqr::recv` under
`SpqrRecvOkQ Q`, reaching `DeriveKeysState` on `.ok (newPqrState, pqrKey)` or formatting the error,
freeing `mkg.seed`, and reaching `ErrTailState` on `.error sd` (or panicking on `S.recvPanics` / OOM). -/
def PqRecvSpec (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
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
      PqRecvState A ctl img x trG tr st1 mkg draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def PqRecvSpecQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
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
      PqRecvState A ctl img x trG tr st1 mkg draws (F ∗ R) s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((ErrTailState A ctl img x trG tr st1 e draws (F ∗ R) s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment S6 contract (`+0x5dc → +0x63c`): saves `newPqrState`, reassembles `mkg` and `pqrKey`,
and calls `MessageKeyGenerator::generate_keys` (`mkg.seed.length = 32`), reaching `VerifyMacState`
with `mks = mkg.generateKeys C.F pqrKey`. -/
def DeriveKeysSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  GenerateKeysOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segVerifyMacPC img) s
        (VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

/-- Segment S7 contract (`+0x63c → +0x678 / +0x30c` or OOM panic): calls
`SignalMessage::verify_mac_with_addresses`, reaching `AesDecryptState` on `true` or allocating
`"bad authentication code"`, freeing `newPqrState`, and reaching `ErrTailState` on `false`. -/
def VerifyMacSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  VerifyMacWithAddressesOk img C A ctl parse abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment S8 contract (`+0x678 → +0x6a4 / +0x30c` or OOM panic): calls `aes_256_cbc_decrypt`,
reaching `ApplyRatchetState` on `some pt` or formatting `"bad ciphertext"`, freeing `newPqrState`,
and reaching `ErrTailState` on `none`. -/
def AesDecryptSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- Segment S9 contract (`+0x6a4 → +0x4b8 → +0x394 → +0x3b0`): frees the old `tr.pqr_state`,
installs `newPqrState`, writes `Ok(pt)` to `x.ret`, calls `TR::apply_to_session_state` and
`SessionState::clear_unacknowledged_pre_key_message`, and returns via the epilogue. -/
def ApplyRatchetSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
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
      ApplyRatchetState A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (tryDecryptSpec C A ctl parse S img) x R s0 s

/-- Target `subroutine_ok` statement for `Root.lean`:
`try_decrypt_with_state::<HookRng>` (`tryDecryptEntry img = img.base + 0x3439c#64`) meets
`tryDecryptSpec C A ctl parse S img` on `tripleRatchetProgAt img.base C ctl abs`, restricted to session states whose
pq state meets `Q` (`Q := fun _ => True`: unrestricted, `Spec.restrictPre_true`). -/
def TryDecryptOk (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (tryDecryptEntry img)
    ((tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

def tryDecryptSpecQF (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    Spec TryDecryptGhost :=
  { tryDecryptSpec C A ctl parse S img with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ F ∗ (tryDecryptSpec C A ctl parse S img).pre x s
    post := fun x s0 sf => F ∗ (tryDecryptSpec C A ctl parse S img).post x s0 sf }

def TryDecryptOkQF (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (tryDecryptEntry img)
    (tryDecryptSpecQF Q F C A ctl parse S img)

theorem tryDecryptOk_of_okQF {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : TryDecryptOkQF Q emp img C A ctl parse S abs) :
    TryDecryptOk Q img C A ctl parse S abs := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he)
  · dsimp only [tryDecryptSpecQF, Spec.restrictPre] at hpre ⊢
    rwa [emp_sepConj]
  · dsimp only [tryDecryptSpecQF, Spec.restrictPre] at hpost ⊢
    rwa [emp_sepConj] at hpost

/-! ## 5. `tripleRatchetProgAtExt` Segment Contracts `S0SpecExt` .. `S9SpecExt`, `ErrTailSpecExt`, and `TryDecryptOkExt` -/

def ErrTailSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  DropChainOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (tryDecryptSpec C A ctl parse S img) x R s0 s

def S0SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOkExt img A ext →
  RemoteIdentityKeyOkExt img A ext →
  IsSameAccountOkExt img.base ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (segLoadRatchetPC img) s0
        (LoadRatchetState A ctl img x R s0)

def S1SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOkExt img A ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      LoadRatchetState A ctl img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAtExt img.base ext)
          (tryDecryptSpec C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ∃ trG, FindChainState A ctl img x trG tr st1 R s0 s'

def S2SpecExt (img : Obj.Image) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  FindReceiverChainKeyOkExt img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      FindChainState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (segConsumeMsgKeyPC img) s
          (ConsumeMsgKeyState A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (segDhStepPC img) s
          (DhStepState A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (tripleRatchetProgAtExt img.base ext) (errTailPC img) s
          (ErrTailState A ctl img x trG tr st1 e 0 R s0)

def S3SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  CreateChainOkExt img C A ext →
  DerivePublicKeyBytesOkExt img.base C ext →
  PublicKeySerializeOkExt img.base A ext →
  ChainKeyToPbOkExt img.base A ext →
  GrowOneChainOkExt img A ext →
  DropChainOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      x.rest.length < 2 ^ 63 →
      DhStepState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG' r1, ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def S4SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  CmkOkExt img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      ConsumeMsgKeyState A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

def S5SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      tr.pqrState = x.st.pqRatchetState →
      PqRecvState A ctl img x trG tr st1 mkg draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def S6SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  GenerateKeysOkExt img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (segVerifyMacPC img) s
        (VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

def S7SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  VerifyMacWithAddressesOkExt img C A parse ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def S8SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

def S9SpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
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
      ApplyRatchetState A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (tryDecryptSpec C A ctl parse S img) x R s0 s

/-- Target `subroutine_ok` statement on `tripleRatchetProgAtExt img.base ext`:
`try_decrypt_with_state::<HookRng>` (`tryDecryptEntry img = img.base + 0x3439c#64`) meets
`tryDecryptSpec C A ctl parse S img` on `tripleRatchetProgAtExt img.base ext`. -/
def TryDecryptOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) (tryDecryptEntry img)
    (tryDecryptSpec C A ctl parse S img)

/-! ## 6. Whole-Function `decFn` Model, `tryDecryptFnSpec`, and `Stage2ContractsX` Segment Contracts -/

/-- Whole-function AES-CBC-parameterized `TripleRatchet.decrypt`: replaces
`aesCbcDecrypt C.D messageKeys.cipherKey messageKeys.iv ciphertext.ciphertext` with
`decFn ciphertext.ciphertext (keyToBytes32 messageKeys.cipherKey) (CBC.blockToBytesLE messageKeys.iv)`. -/
def _root_.CryptoGames.LibsignalSession.TripleRatchet.decryptFn {PQ PQC : Type} (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) : Mut (TripleRatchet PQ) (List (BitVec 8)) := do
  let their := ciphertext.senderRatchetKey
  let counter := ciphertext.counter
  let chainKey ← TripleRatchet.onRatchet (RatchetState.ensureReceiverChain C their coins)
  let messageKeyGen ←
    TripleRatchet.onRatchet (RatchetState.consumeMessageKey C.F their chainKey counter msgType)
  let t ← get
  if spqr.recvPanics t.pqrState ciphertext.pqRatchet then throw .panic
  let (newPqrState, pqrKey) ← match spqr.recv t.pqrState ciphertext.pqRatchet with
    | .ok r => pure r
    | .error true => throw .invalidState
    | .error false => throw (.invalidMessage msgType .pqRatchet)
  let messageKeys := messageKeyGen.generateKeys C.F pqrKey
  let macValid := ciphertext.verifyMacWithAddresses C.F expected t.remoteIdentityKey
    t.localIdentityKey messageKeys.macKey
  if !macValid then throw (.invalidMessage msgType .macFailed)
  let some ptext := decFn ciphertext.ciphertext
      (keyToBytes32 messageKeys.cipherKey) (CBC.blockToBytesLE messageKeys.iv)
    | throw (.invalidMessage msgType .badCiphertext)
  modify fun t => { t with pqrState := newPqrState }
  return ptext

/-- Whole-function AES-CBC-parameterized `SessionState.tryDecryptWithState`. -/
def _root_.CryptoGames.LibsignalSession.SessionState.tryDecryptWithStateFn {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) : Mut (SessionState PQ) (List (BitVec 8)) := do
  let session ← TripleRatchet.fromSessionState
  let (r, session) :=
    Mut.exec (TripleRatchet.decryptFn C decFn spqr expected ciphertext msgType coins) session
  let ptext ← liftE r
  modify fun s => (session.applyToSessionState s).clearUnacknowledgedPreKeyMessage
  return ptext

/-- AES-CBC-parameterized `TryDecryptGhost.model` using `decFn`. -/
def _root_.CryptoVerification.LibsignalTripleRatchet.TryDecryptGhost.modelFn
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (S : SpqrModel) (uuidParse : UuidParser) (x : TryDecryptGhost) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState (List (BitVec 8)) :=
  Mut.exec (SessionState.tryDecryptWithStateFn C decFn S.spqr
    (serializeAddresses (serviceIdParse uuidParse) x.rem x.loc) x.msg
    x.msgType (coinsOf x.rest)) x.st

/-- `speAt` generalized on `.invalidMessage t .badCiphertext` to also allow the
`InvalidSessionStructure("bad key or IV for AES-CBC")` niche `(a ↦₆₄ speWord 20) ∗ memRegion (a + 8#64) 40`
produced when `aes_256_cbc_decrypt` returns `(errTag, 0, _)` under `Externs.aesDecSpec`. -/
def _root_.CryptoVerification.LibsignalTripleRatchetRepr.speFnAt (A : RustAlloc)
    (fnName : List (BitVec 8)) (a : BitVec 64) : SignalProtocolError → SepProp
  | .invalidMessage t .badCiphertext =>
    ∃∗ b : Bool,
      if b then speAt A fnName a (.invalidMessage t .badCiphertext)
      else (a ↦₆₄ speWord 20) ∗ memRegion (a + 8#64) 40
  | e => speAt A fnName a e

theorem _root_.CryptoVerification.LibsignalTripleRatchetRepr.speAt_entails_speFnAt (A : RustAlloc)
    (fnName : List (BitVec 8)) (a : BitVec 64) (e : SignalProtocolError) :
    speAt A fnName a e ⊢ speFnAt A fnName a e := by
  cases e with
  | invalidMessage t r =>
    cases r with
    | badCiphertext =>
      dsimp only [speFnAt]
      exact Entails.sepExists_right true (Entails.refl _)
    | _ => exact Entails.refl _
  | _ => exact Entails.refl _

/-- Result of `try_decrypt_with_state` at `r` (48 bytes) under `aesDecFnSpec`:
`Ok(pt)` is `(-2, vecU8 pt)`, `Err(e)` is `speFnAt "decrypt"`. -/
def _root_.CryptoVerification.LibsignalTripleRatchet.decResultFnAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError (List (BitVec 8)) → SepProp
  | .ok pt => (r ↦₆₄ okTagVec) ∗ vecU8 A (r + 8#64) pt ∗ memRegion (r + 32#64) 16
  | .error e => speFnAt A (utf8 "decrypt") r e

theorem _root_.CryptoVerification.LibsignalTripleRatchet.decResultAt_entails_decResultFnAt
    (A : RustAlloc) (r : BitVec 64) (res : Except SignalProtocolError (List (BitVec 8))) :
    vecResultAt A r res ⊢ decResultFnAt A r res := by
  cases res with
  | ok pt => exact Entails.refl _
  | error e => exact speAt_entails_speFnAt A (utf8 "decrypt") r e

/-- `ErrTailState` generalized for `Stage2ContractsX`: allows `b = false` on
`e = .invalidMessage x.msgType .badCiphertext` (when `aes_256_cbc_decrypt` returns `p = 0#64`),
where `x26 = speWord 20` and `sp + 0x168..0x190` holds `memRegion (sp + 0x168#64) 40`. -/
def ErrTailStateX (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = errTailPC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

theorem ErrTailState.toX {A : RustAlloc} {ctl : BitVec 64} {img : Obj.Image}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailState A ctl img x trG tr st1 e draws R s0 s) :
    ErrTailStateX A ctl img x trG tr st1 e draws R s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, true, nofun, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Whole-function AES-CBC-parameterized `tryDecryptSpec`. -/
def _root_.CryptoVerification.LibsignalTripleRatchet.tryDecryptFnSpec
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
        memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗
        A.pool
      post := fun x s0 sf =>
        ⌜(x.modelFn C decFn S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.modelFn C decFn S uuidParse).1.toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.modelFn C decFn S uuidParse).2) ∗
        decResultFnAt A x.ret (x.modelFn C decFn S uuidParse).1 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
        logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.modelFn C decFn S uuidParse).1 = .error .panic ∨
            S.recvPanics x.st.pqRatchetState x.msg.pqRatchet ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

private theorem bytesToKey32_keyToBytes32' (k : BitVec 256) :
    bytesToKey32 (keyToBytes32 k) = k := by
  change bytesToKey32
    [k.extractLsb' 0 8, k.extractLsb' 8 8, k.extractLsb' 16 8, k.extractLsb' 24 8,
     k.extractLsb' 32 8, k.extractLsb' 40 8, k.extractLsb' 48 8, k.extractLsb' 56 8,
     k.extractLsb' 64 8, k.extractLsb' 72 8, k.extractLsb' 80 8, k.extractLsb' 88 8,
     k.extractLsb' 96 8, k.extractLsb' 104 8, k.extractLsb' 112 8, k.extractLsb' 120 8,
     k.extractLsb' 128 8, k.extractLsb' 136 8, k.extractLsb' 144 8, k.extractLsb' 152 8,
     k.extractLsb' 160 8, k.extractLsb' 168 8, k.extractLsb' 176 8, k.extractLsb' 184 8,
     k.extractLsb' 192 8, k.extractLsb' 200 8, k.extractLsb' 208 8, k.extractLsb' 216 8,
     k.extractLsb' 224 8, k.extractLsb' 232 8, k.extractLsb' 240 8, k.extractLsb' 248 8] = k
  have h0 (x : BitVec 8) : ((0 : BitVec 256) <<< 8) ||| x.setWidth 256 = x.setWidth 256 := by simp
  have hs {w : Nat} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 256) <<< 8) ||| y.setWidth 256 = (x ++ y).setWidth 256 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  have hext (s₂ s₁ n₂ n₁ : Nat) (h : s₂ = s₁ + n₁) :
      k.extractLsb' s₂ n₂ ++ k.extractLsb' s₁ n₁ = k.extractLsb' s₁ (n₂ + n₁) := by
    subst h
    ext i hi
    simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
    split
    · rfl
    · congr 1; omega
  dsimp only [HKDF.bytesToKey32, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hs]
  rw [BitVec.setWidth_eq]
  rw [hext 248 240 _ 8 rfl, hext 240 232 _ 8 rfl, hext 232 224 _ 8 rfl, hext 224 216 _ 8 rfl,
      hext 216 208 _ 8 rfl, hext 208 200 _ 8 rfl, hext 200 192 _ 8 rfl, hext 192 184 _ 8 rfl,
      hext 184 176 _ 8 rfl, hext 176 168 _ 8 rfl, hext 168 160 _ 8 rfl, hext 160 152 _ 8 rfl,
      hext 152 144 _ 8 rfl, hext 144 136 _ 8 rfl, hext 136 128 _ 8 rfl, hext 128 120 _ 8 rfl,
      hext 120 112 _ 8 rfl, hext 112 104 _ 8 rfl, hext 104 96 _ 8 rfl, hext 96 88 _ 8 rfl,
      hext 88 80 _ 8 rfl, hext 80 72 _ 8 rfl, hext 72 64 _ 8 rfl, hext 64 56 _ 8 rfl,
      hext 56 48 _ 8 rfl, hext 48 40 _ 8 rfl, hext 40 32 _ 8 rfl, hext 32 24 _ 8 rfl,
      hext 24 16 _ 8 rfl, hext 16 8 _ 8 rfl, hext 8 0 _ 8 rfl]
  ext i hi; simp

private theorem bytesToBlock_blockToBytesLE' (iv : CBC.Block) :
    CBC.bytesToBlock (CBC.blockToBytesLE iv) = iv := by
  change CBC.bytesToBlock
    [iv.extractLsb' 0 8, iv.extractLsb' 8 8, iv.extractLsb' 16 8, iv.extractLsb' 24 8,
     iv.extractLsb' 32 8, iv.extractLsb' 40 8, iv.extractLsb' 48 8, iv.extractLsb' 56 8,
     iv.extractLsb' 64 8, iv.extractLsb' 72 8, iv.extractLsb' 80 8, iv.extractLsb' 88 8,
     iv.extractLsb' 96 8, iv.extractLsb' 104 8, iv.extractLsb' 112 8, iv.extractLsb' 120 8] = iv
  have h0 (x : BitVec 8) : ((0 : BitVec 128) <<< 8) ||| x.setWidth 128 = x.setWidth 128 := by simp
  have hs {w : Nat} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 128) <<< 8) ||| y.setWidth 128 = (x ++ y).setWidth 128 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  have hext (s₂ s₁ n₂ n₁ : Nat) (h : s₂ = s₁ + n₁) :
      iv.extractLsb' s₂ n₂ ++ iv.extractLsb' s₁ n₁ = iv.extractLsb' s₁ (n₂ + n₁) := by
    subst h
    ext i hi
    simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
    split
    · rfl
    · congr 1; omega
  dsimp only [CBC.bytesToBlock, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hs]
  rw [BitVec.setWidth_eq]
  rw [hext 120 112 _ 8 rfl, hext 112 104 _ 8 rfl, hext 104 96 _ 8 rfl, hext 96 88 _ 8 rfl,
      hext 88 80 _ 8 rfl, hext 80 72 _ 8 rfl, hext 72 64 _ 8 rfl, hext 64 56 _ 8 rfl,
      hext 56 48 _ 8 rfl, hext 48 40 _ 8 rfl, hext 40 32 _ 8 rfl, hext 32 24 _ 8 rfl,
      hext 24 16 _ 8 rfl, hext 16 8 _ 8 rfl, hext 8 0 _ 8 rfl]
  ext i hi; simp

@[simp]
theorem decryptFn_block_eq {PQ PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) :
    TripleRatchet.decryptFn C
      (fun ct k iv => aesCbcDecrypt C.D (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) ct)
      spqr expected ciphertext msgType coins =
      TripleRatchet.decrypt C spqr expected ciphertext msgType coins := by
  unfold TripleRatchet.decryptFn TripleRatchet.decrypt
  simp only [bytesToKey32_keyToBytes32', bytesToBlock_blockToBytesLE']
  rfl

@[simp]
theorem tryDecryptWithStateFn_block_eq {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) :
    SessionState.tryDecryptWithStateFn C
      (fun ct k iv => aesCbcDecrypt C.D (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) ct)
      spqr expected ciphertext msgType coins =
      SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins := by
  unfold SessionState.tryDecryptWithStateFn SessionState.tryDecryptWithState
  rw [decryptFn_block_eq]

@[simp]
theorem modelFn_block_eq (C : Crypto) (S : SpqrModel)
    (x : TryDecryptGhost) :
    x.modelFn C
      (fun ct k iv => aesCbcDecrypt C.D (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) ct)
      S uuidTryParse = x.model C S uuidTryParse := by
  unfold TryDecryptGhost.modelFn TryDecryptGhost.model
  rw [tryDecryptWithStateFn_block_eq]

def ClearUpkOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr clearUpkName)
    ((clearUpkSpecX A).inImage img)

def DropChainOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainName)
    ((dropChainSpecX A).inImage img)

def ChainKeyToPbOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr chainKeyToPbName)
    ((chainKeyToPbSpecX A).inImage img)

def DerivePublicKeyBytesOkX (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr derivePublicKeyBytesName)
    ((derivePublicKeyBytesStackSpec C.pubKey extHookStack).inImage img)

def VerifyMacWithAddressesOkX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
    ((verifyMacWithAddressesSpecX img C.F A parse).inImage img)

/-- `RawVec<Chain>::grow_one` stack budget under `AllocContractsX` (`464 + finishGrowStackX`). -/
abbrev growOneChainStackX : Nat := 464 + finishGrowStackX

def growOneChainSpecX (A : RustAlloc) : Spec CryptoVerification.LibsignalSession.GrowGhost where
  pre := fun (v, cap, ptr, bs) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool ∗ stackAt s.sp growOneChainStackX
  post := fun (v, cap, _, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) ∗
      A.pool ∗ stackAt s0.sp growOneChainStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def GrowOneChainOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr growOneChainName)
    ((growOneChainSpecX A).inImage img)

/-- `RatchetState::consume_message_key` stack budget under `AllocContractsX` (`4096 + extHookStack`). -/
abbrev cmkStackX : Nat := 4096 + extHookStack

def cmkSpecX (F : ShaCompress) (A : RustAlloc) (img : Obj.Image) :
    Spec CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ckA ∧
          (s.readReg64 .x3).setWidth 32 = x.counter ∧
          (s.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s.readReg64 .x8 = x.ret⌝ ∗
        ratchetAt A x.self x.G x.st ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
        memRegion x.ret 88 ∗ (CryptoVerification.LibsignalSession.logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt s.sp cmkStackX ∗ A.pool
      post := fun x s0 sf =>
        ⌜(x.model F).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G' : RatchetGhost,
          ⌜x.G.AgreeExcept G' (x.touched F)⌝ ∗ ratchetAt A x.self G' (x.model F).2) ∗
        CryptoVerification.LibsignalSessionRepr.consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
        (CryptoVerification.LibsignalSession.logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt s0.sp cmkStackX ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model F).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

def CmkOkX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr cmkName)
    (cmkSpecX C.F A img)

/-- Bundle of all 16 callee `subroutine_ok` hypotheses on `tripleRatchetProgAtExt img.base ext` under `Stage2ContractsX`. -/
structure TryDecryptCalleesX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop where
  localIk : LocalIdentityKeyOkExt img A ext
  remoteIk : RemoteIdentityKeyOkExt img A ext
  sameAcc : IsSameAccountOkExt img.base ext
  clearUpk : ClearUpkOkX img A ext
  dropChain : DropChainOkX img A ext
  chainKeyToPb : ChainKeyToPbOkX img A ext
  derivePk : DerivePublicKeyBytesOkX img C ext
  trFrom : TrFromOkX img A ext
  trApply : TrApplyOkX img A ext
  findReceiverChainKey : FindReceiverChainKeyOkExt img A ext
  createChain : CreateChainOkX img C A ext
  genKeys : GenerateKeysOkX img C A ext
  pkSer : PublicKeySerializeOkX img A ext
  verifyMac : VerifyMacWithAddressesOkX img C A parse ext
  cmk : CmkOkX img C A ext
  growOne : GrowOneChainOkX img A ext

def ErrTailSpecX (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsX img C A encFn decFn ext →
  DropChainOkX img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.modelFn C decFn S parse).1 = .error e →
      (x.modelFn C decFn S parse).2 = st1 →
      ErrTailStateX A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (tryDecryptFnSpec C decFn A ctl parse S img) x R s0 s

def S0SpecX (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOkExt img A ext →
  RemoteIdentityKeyOkExt img A ext →
  IsSameAccountOkExt img.base ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (segLoadRatchetPC img) s0
        (LoadRatchetState A ctl img x R s0)

def S1SpecX (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOkX img A ext →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      LoadRatchetState A ctl img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAtExt img.base ext)
          (tryDecryptFnSpec C decFn A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ∃ trG, FindChainState A ctl img x trG tr st1 R s0 s'

abbrev S2SpecX := S2SpecExt

def S3SpecX (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsX img C A encFn decFn ext →
  Stage2RngContract img.base ctl ext →
  CreateChainOkX img C A ext →
  DerivePublicKeyBytesOkX img C ext →
  PublicKeySerializeOkX img A ext →
  ChainKeyToPbOkX img A ext →
  GrowOneChainOkX img A ext →
  DropChainOkX img A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      x.rest.length < 2 ^ 63 →
      DhStepState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG' r1, ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))

def S4SpecX (img : Obj.Image) (C : Crypto)
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
      ConsumeMsgKeyState A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((∃ trG', PqRecvState A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

def S5SpecX (img : Obj.Image) (C : Crypto)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2ContractsX img C A encFn decFn ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
      (R : SepProp) (s0 s : State),
      tr.pqrState = x.st.pqRatchetState →
      PqRecvState A ctl img x trG tr st1 mkg draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
             S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          ((ErrTailState A ctl img x trG tr st1 e draws R s0 s' ∧ S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))

def S6SpecX (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  GenerateKeysOkX img C A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      DeriveKeysState A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAtExt img.base ext) (segVerifyMacPC img) s
        (VerifyMacState A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

def S7SpecX (img : Obj.Image) (C : Crypto)
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
      VerifyMacState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))

def S8SpecX (img : Obj.Image) (C : Crypto)
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
      AesDecryptState A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      match decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (ApplyRatchetState A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
          (ErrTailStateX A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptFnSpec C decFn A ctl parse S img).onPanic x s0 s' ∗ R)))

def S9SpecX (img : Obj.Image) (C : Crypto)
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
      ApplyRatchetState A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (tryDecryptFnSpec C decFn A ctl parse S img) x R s0 s

/-- Target `subroutine_ok` statement on `tripleRatchetProgAtExt img.base ext` for `tryDecryptFnSpec C decFn`:
`try_decrypt_with_state::<HookRng>` (`tryDecryptEntry img = img.base + 0x3439c#64`) meets
`tryDecryptFnSpec C decFn A ctl parse S img` on `tripleRatchetProgAtExt img.base ext`. -/
def TryDecryptOkX (img : Obj.Image) (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) (tryDecryptEntry img)
    (tryDecryptFnSpec C decFn A ctl parse S img)

/-! ## 7. Relocatable `[LibsignalPlacement]` Checkpoint PCs, States, and Segment Contracts -/

/-- Synthetic `Obj.Image` whose `logFilterAddr` equals `lsLogFilterAddr` (`lsmpl.ρ "log::MAX_LOG_LEVEL_FILTER"`),
allowing reuse of `tryDecryptCommonHeap`, `(tryDecryptSpec ...).post`, and `(tryDecryptFnSpec ...).post`. -/
def tryDecryptPlacedImg [LibsignalPlacement] : Obj.Image :=
  { (default : Obj.Image) with base := lsLogFilterAddr - logFilterAddr { (default : Obj.Image) with base := 0 } }

@[simp, arm64_norm, wp_norm]
theorem logFilterAddr_tryDecryptPlacedImg [LibsignalPlacement] :
    logFilterAddr tryDecryptPlacedImg = lsLogFilterAddr := by
  simp only [tryDecryptPlacedImg, logFilterAddr]; bv_omega

@[simp, arm64_norm, wp_norm]
theorem logOff_tryDecryptPlacedImg [LibsignalPlacement] :
    logOff tryDecryptPlacedImg = (lsLogFilterAddr ↦₆₄ 0#64) := by
  simp only [logOff, logFilterAddr_tryDecryptPlacedImg]

abbrev segLoadRatchetPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x1d8#64
abbrev segFindChainPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x2a4#64
abbrev segDhStepPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x500#64
abbrev s3EvictLoopPC_at (entry : BitVec 64) : BitVec 64 := entry + 0xb04#64
abbrev segConsumeMsgKeyPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x3e4#64
abbrev segPqRecvPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x5b8#64
abbrev segDeriveKeysPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x5dc#64
abbrev segVerifyMacPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x63c#64
abbrev segAesDecryptPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x678#64
abbrev segApplyRatchetPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x6a4#64
abbrev errTailPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x30c#64
abbrev errDropChainLoopPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x33c#64
abbrev retEpiloguePC_at (entry : BitVec 64) : BitVec 64 := entry + 0x394#64

/-- Relocatable machine metadata invariant at internal checkpoints of `try_decrypt_with_state`
(Block `130` or Block `433`). Carries `LibsignalCodeRoLoaded lsmpl s` (`LibsignalCodeLoaded` +
`LibsignalRoLoaded`). -/
def tryDecryptMidMetaPlaced [LibsignalPlacement] (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp - 1504#64 ∧
  s0.spAligned = true ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = s0.sp - 96#64 ∧
  s.trace = s0.trace ∧
  LibsignalCodeRoLoaded lsmpl s.mem ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

def ErrTailStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = errTailPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
    tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

def ErrTailStateXPlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = errTailPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
      (if b then speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e else memRegion (sp + 0x168#64) 40) ∗
      memRegion (sp + 0x190#64) 0x3f0 ∗
      tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

theorem ErrTailStatePlaced.toX [LibsignalPlacement] {entry : BitVec 64} {A : RustAlloc}
    {ctl : BitVec 64} {x : TryDecryptGhost} {trG : TrGhost}
    {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {e : SignalProtocolError} {draws : Nat} {R : SepProp} {s0 s : State}
    (h : ErrTailStatePlaced entry A ctl x trG tr st1 e draws R s0 s) :
    ErrTailStateXPlaced entry A ctl x trG tr st1 e draws R s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, true, nofun, h.2.2.2.2.1, h.2.2.2.2.2⟩

def LoadRatchetStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segLoadRatchetPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
    tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R)

def FindChainStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segFindChainPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
    tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R)

def DhStepStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segDhStepPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
    tryDecryptCommonHeap A ctl tryDecryptPlacedImg x 0 s0 ∗ R)

def ConsumeMsgKeyStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (ck : ChainKey) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segConsumeMsgKeyPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
    tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

def PqRecvStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segPqRecvPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
      tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

def DeriveKeysStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segDeriveKeysPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
      tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

def VerifyMacStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mks : MessageKeys) (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segVerifyMacPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
      tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

def AesDecryptStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mks : MessageKeys) (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segAesDecryptPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
      tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

def ApplyRatchetStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (newPqrState pt : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segApplyRatchetPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
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
      tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

/-- Relocatable `[LibsignalPlacement]` raw specification of `try_decrypt_with_state`
(without `withLsCodeRoLoaded`). -/
def tryDecryptRawSpecPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
      s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
      (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
      x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
      x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
    sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
    memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗ logOff tryDecryptPlacedImg ∗
    stackAt s.sp rootStack ∗ A.pool
  post := (tryDecryptSpec C A ctl uuidParse S tryDecryptPlacedImg).post
  onPanic := (tryDecryptSpec C A ctl uuidParse S tryDecryptPlacedImg).onPanic

/-- Relocatable `[LibsignalPlacement]` specification of `try_decrypt_with_state` (Blocks `130` and `549`). -/
def tryDecryptSpecPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  withLsCodeRoLoaded lsmpl (tryDecryptRawSpecPlaced C A ctl uuidParse S)

/-- Relocatable `[LibsignalPlacement]` raw specification of `try_decrypt_with_state` for `decFn`
(without `withLsCodeRoLoaded`). -/
def tryDecryptFnRawSpecPlaced [LibsignalPlacement] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) :
    Spec TryDecryptGhost where
  pre := (tryDecryptRawSpecPlaced C A ctl uuidParse S).pre
  post := (tryDecryptFnSpec C decFn A ctl uuidParse S tryDecryptPlacedImg).post
  onPanic := (tryDecryptFnSpec C decFn A ctl uuidParse S tryDecryptPlacedImg).onPanic

/-- Relocatable `[LibsignalPlacement]` specification of `try_decrypt_with_state` for `decFn`. -/
def tryDecryptFnSpecPlaced [LibsignalPlacement] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) :
    Spec TryDecryptGhost :=
  withLsCodeRoLoaded lsmpl (tryDecryptFnRawSpecPlaced C decFn A ctl uuidParse S)

def ErrTailSeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State),
    e ≠ .panic →
    (x.model C S parse).1 = .error e →
    (x.model C S parse).2 = st1 →
    ErrTailStatePlaced entry A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (tryDecryptSpecPlaced C A ctl parse S) x R s0 s

def S0SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
    s0.pc = entry → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).pre x s0 ∗ R) →
    reaches_pc prog (segLoadRatchetPC_at entry) s0
      (LoadRatchetStatePlaced entry A ctl x R s0)

def S1SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      reaches_outcome prog (tryDecryptSpecPlaced C A ctl parse S) x R s0 s
    | (.ok tr, st1) =>
      ∃ s', Steps prog s s' ∧
        ∃ trG, FindChainStatePlaced entry A ctl x trG tr st1 R s0 s'

def S2SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    FindChainStatePlaced entry A ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
    | .ok (some ck) =>
      reaches_pc prog (segConsumeMsgKeyPC_at entry) s
        (ConsumeMsgKeyStatePlaced entry A ctl x trG tr st1 ck 0 R s0)
    | .ok none =>
      reaches_pc prog (segDhStepPC_at entry) s
        (DhStepStatePlaced entry A ctl x trG tr st1 R s0)
    | .error e =>
      reaches_pc prog (errTailPC_at entry) s
        (ErrTailStatePlaced entry A ctl x trG tr st1 e 0 R s0)

def S3SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    DhStepStatePlaced entry A ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
        tr.ratchet with
    | (.ok ck, r1) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG', ConsumeMsgKeyStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG' r1, ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

def S4SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State),
    ConsumeMsgKeyStatePlaced entry A ctl x trG tr st1 ck draws R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG', PqRecvStatePlaced entry A ctl x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    | (.error e, r2) =>
      ∃ s', Steps prog s s' ∧
        ((e ≠ .panic ∧ ∃ trG',
            ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
           (s'.mem ⊨ anyHeap ∗ R)))

def S5SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State),
    tr.pqrState = x.st.pqRatchetState →
    PqRecvStatePlaced entry A ctl x trG tr st1 mkg draws R s0 s →
    prog.CodeLoaded s.mem →
    match S.recv tr.pqrState x.msg.pqRatchet with
    | .ok (newPqrState, pqrKey) =>
      ∃ s', Steps prog s s' ∧
        ((DeriveKeysStatePlaced entry A ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
           S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    | .error sd =>
      let e : SignalProtocolError :=
        if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
      ∃ s', Steps prog s s' ∧
        ((ErrTailStatePlaced entry A ctl x trG tr st1 e draws R s0 s' ∧
           S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

def S6SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State),
    mkg.seed.length = 32 →
    DeriveKeysStatePlaced entry A ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
    reaches_pc prog (segVerifyMacPC_at entry) s
      (VerifyMacStatePlaced entry A ctl x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

def S7SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    VerifyMacStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps prog s s' ∧
        (AesDecryptStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps prog s s' ∧
        (ErrTailStatePlaced entry A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

def S8SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    AesDecryptStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
    | some pt =>
      ∃ s' : State, Steps prog s s' ∧
        (ApplyRatchetStatePlaced entry A ctl x trG tr st1 newPqrState pt draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    | none =>
      ∃ s' : State, Steps prog s s' ∧
        (ErrTailStatePlaced entry A ctl x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
            draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

def S9SeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (R : SepProp) (s0 s : State),
    (x.model C S parse).1 = .ok pt →
    (x.model C S parse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
    ApplyRatchetStatePlaced entry A ctl x trG tr st1 newPqrState pt
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (tryDecryptSpecPlaced C A ctl parse S) x R s0 s

def ErrTailSeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State),
    e ≠ .panic →
    (x.modelFn C decFn S parse).1 = .error e →
    (x.modelFn C decFn S parse).2 = st1 →
    ErrTailStateXPlaced entry A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A ctl parse S) x R s0 s

def S0SeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
    s0.pc = entry → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).pre x s0 ∗ R) →
    reaches_pc prog (segLoadRatchetPC_at entry) s0
      (LoadRatchetStatePlaced entry A ctl x R s0)

def S1SeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A ctl parse S) x R s0 s
    | (.ok tr, st1) =>
      ∃ s', Steps prog s s' ∧
        ∃ trG, FindChainStatePlaced entry A ctl x trG tr st1 R s0 s'

abbrev S2SeamXPlaced [LibsignalPlacement] := S2SeamPlaced

def S3SeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    DhStepStatePlaced entry A ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
        tr.ratchet with
    | (.ok ck, r1) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG', ConsumeMsgKeyStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG' r1, ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))

def S4SeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State),
    ConsumeMsgKeyStatePlaced entry A ctl x trG tr st1 ck draws R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG', PqRecvStatePlaced entry A ctl x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))
    | (.error e, r2) =>
      ∃ s', Steps prog s s' ∧
        ((e ≠ .panic ∧ ∃ trG',
            ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
           (s'.mem ⊨ anyHeap ∗ R)))

def S5SeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State),
    tr.pqrState = x.st.pqRatchetState →
    PqRecvStatePlaced entry A ctl x trG tr st1 mkg draws R s0 s →
    prog.CodeLoaded s.mem →
    match S.recv tr.pqrState x.msg.pqRatchet with
    | .ok (newPqrState, pqrKey) =>
      ∃ s', Steps prog s s' ∧
        ((DeriveKeysStatePlaced entry A ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
           S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))
    | .error sd =>
      let e : SignalProtocolError :=
        if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
      ∃ s', Steps prog s s' ∧
        ((ErrTailStatePlaced entry A ctl x trG tr st1 e draws R s0 s' ∧
           S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))

abbrev S6SeamXPlaced [LibsignalPlacement] := S6SeamPlaced

def S7SeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    VerifyMacStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps prog s s' ∧
        (AesDecryptStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps prog s s' ∧
        (ErrTailStatePlaced entry A ctl x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))

def S8SeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    AesDecryptStatePlaced entry A ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    match decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (CBC.blockToBytesLE mks.iv) with
    | some pt =>
      ∃ s' : State, Steps prog s s' ∧
        (ApplyRatchetStatePlaced entry A ctl x trG tr st1 newPqrState pt draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))
    | none =>
      ∃ s' : State, Steps prog s s' ∧
        (ErrTailStateXPlaced entry A ctl x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
            draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic x s0 s' ∗ R)))

def S9SeamXPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (R : SepProp) (s0 s : State),
    (x.modelFn C decFn S parse).1 = .ok pt →
    (x.modelFn C decFn S parse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
    ApplyRatchetStatePlaced entry A ctl x trG tr st1 newPqrState pt
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A ctl parse S) x R s0 s

end CryptoVerification.LibsignalTripleRatchet.Decrypt
