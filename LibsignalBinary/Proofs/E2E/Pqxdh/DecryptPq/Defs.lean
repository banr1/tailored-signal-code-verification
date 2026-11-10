/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropChain2
public import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs

/-!
# Segment Specifications and Callee Hypotheses for `try_decrypt_with_state::<PqxdhRng>`

Intermediate segment contracts and callee `subroutine_ok` hypotheses for
`libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>`
(image offset `0x6eff8`, 822 instructions, `+0x000 .. +0xcd4`), supporting `tryDecryptSpec` and
`TryDecryptRunStmt` (`Root`).

Defines:
- Callee `subroutine_ok` hypotheses (`LocalIdentityKeyOk`, `IsSameAccountOk`, `ClearUpkOk`,
  `DropChainOk`, `ChainKeyToPbOk`, `DerivePublicKeyBytesOk`, `VerifyMacWithAddressesOk`, `CmkOk`,
  `GrowOneChainOk`) bundled with imported callee predicates into `TryDecryptCallees`.
- Checkpoint PCs (`segS1PC` .. `segS9PC`, `errTailPC`, `s3EvictLoopPC`, `errDropChainLoopPC`),
  stack frame layout predicates, and intermediate seam invariants.
- Segment contracts `S0Spec` .. `S9Spec` and `ErrTailSpec`, together with `TryDecryptOk`.
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

abbrev tryDecryptName : String :=
  "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_pqxdh_e2e::PqxdhRng>"

abbrev dropChainName : String := dropChain2Name

/-! ## 1. Callee Symbol Names and `subroutine_ok` Hypotheses -/

/-- `<SessionState>::local_identity_key` (`0x119f4`, called at `try_decrypt+0x050`) meets
`localIdentityKeySpec A img` on `tripleRatchetProgAt`. -/
def LocalIdentityKeyOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr localIdentityKeyName)
    (localIdentityKeySpec A img)

/-- `<IdentityKey>::is_same_account` (`0xacec`, called at `try_decrypt+0x1d0`) meets
`isSameAccountSpec` on `tripleRatchetProgAt`. -/
def IsSameAccountOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr isSameAccountName)
    isSameAccountSpec

/-- `<SessionState>::clear_unacknowledged_pre_key_message` (`0x12404`, called at
`try_decrypt+0x4f0`) meets `clearUpkSpec A` on `tripleRatchetProgAt`. -/
def ClearUpkOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr clearUpkName)
    (clearUpkSpec A)

/-- `core::ptr::drop_glue::<Chain>` (`0x35dc8`, called at `try_decrypt+0x340` and `+0xb88`) meets
`dropChainSpec A` on `tripleRatchetProgAt`. -/
def DropChainOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr dropChainName)
    (dropChainSpec A)

/-- `<ChainKey>::to_pb` (`0xcf68`, called at `try_decrypt+0xa80`) meets `chainKeyToPbSpec A` on
`tripleRatchetProgAt`. -/
def ChainKeyToPbOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainKeyToPbName)
    (chainKeyToPbSpec A)

/-- `<PrivateKey>::derive_public_key_bytes` (`0x3db4c`, called at `try_decrypt+0x7b0`) meets
`derivePublicKeyBytesSpec C.pubKey` on `tripleRatchetProgAt`. -/
def DerivePublicKeyBytesOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr derivePublicKeyBytesName)
    (derivePublicKeyBytesSpec C.pubKey)

/-- `<SignalMessage>::verify_mac_with_addresses` (`0x1d5a0`, called at `try_decrypt+0x65c`) meets
`(verifyMacWithAddressesSpec img C.F A parse).inImage img` on `tripleRatchetProgAt`. -/
def VerifyMacWithAddressesOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr verifyMacWithAddressesName)
    ((verifyMacWithAddressesSpec img C.F A parse).inImage img)

abbrev cmkName : String := "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

/-- `<RatchetState>::consume_message_key` (`0xded8`, called at `try_decrypt+0x474`) meets
`consumeMessageKeySpec C.F A img` on `tripleRatchetProgAt`. -/
def CmkOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr cmkName)
    (CryptoVerification.LibsignalSession.consumeMessageKeySpec C.F A img)

/-- Symbol name (`0x15cac`) for `<RawVec<Chain>>::grow_one` (called at `try_decrypt+0xa98`; shared
monomorphization with `RawVec<MessageKey>::grow_one` at `size = 104`, `align = 8`). -/
abbrev growOneChainName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"

/-- `<RawVec<Chain>>::grow_one` (`0x15cac`, called at `try_decrypt+0xa98`) meets
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

/-! ## 2. Frame Layout Constants and Checkpoint PCs (`img.base + 0x6eff8#64`) -/

/-- Entry address of `try_decrypt_with_state::<HookRng>` (`0x6eff8`). -/
abbrev tryDecryptEntry (img : Obj.Image) : BitVec 64 := entryOf img tryDecryptName

/-- Own stack frame size of `try_decrypt_with_state` (`+0x000: stp x29, x30, [sp, #-0x60]!` and
`+0x01c: sub sp, sp, #0x580`, total `0x5e0` = 1504 B, restored at `+0x394 .. +0x3ac`). -/
abbrev tryDecryptFrameSize : Nat := 1504

/-- Stack budget below `sp = s0.sp - 1504#64` available to callees of `try_decrypt_with_state`
(`rootStack - 1504 = 262144 - 1504 = 260640` B, which exceeds every callee stack budget including
`smallRootStack = 65536` B for `TR::from_session_state`, `spqrRecvStack = 16384` B, and
`cmkStack = 8192` B). -/
abbrev tryDecryptSubStack : Nat := rootStack - tryDecryptFrameSize

/-- **S1 entry (`+0x1d8`)**: `add x8, sp, #0x190; mov x0, x21; bl TR::from_session_state`
after `local_identity_key`, `remote_identity_key`, and (when `remoteIdentity = some _`)
`is_same_account` complete with `self_session = false` (`w1 = 0`). -/
abbrev segS1PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x1d8#64

/-- **S2 entry (`+0x2a4` = `0x39b1c`)**: `bl RatchetState::find_receiver_chain_key` after
`TR::from_session_state` succeeds and its `TripleRatchet` (`264` B) is copied
to `sp + 0x38..0x140`. -/
abbrev segS2PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x2a4#64

/-- **S3 entry (`+0x500` = `0x3489c`)**: `ldr w8, [sp, #0x50]` (`RatchetState::dh_ratchet_step`
inlined body) when `find_receiver_chain_key` returns `Ok(None)`. -/
abbrev segS3PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x500#64

/-- **S3 eviction loop header (`+0xb04` = `0x34ea0`)**: `ldr x0, [sp, #0x40]; mov w8, #0x68; ...`
in `dh_ratchet_step` when `receiver_chains.length ≥ 6` after pushing the new receiver chain
(`Vec::remove(0)` via `memmove` + `drop_glue<Chain>` until `len = 5`). -/
abbrev s3EvictLoopPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0xb04#64

/-- **S4 entry (`+0x3e4` = `0x34780`)**: `ldr q0, [x25, #0x120]; ldr w8, [sp, #0x2d0]`
join point of `ensureReceiverChain = .ok ck` (from S2 `Ok(Some ck)` or S3 `dh_ratchet_step`),
before `<ProtocolAddress as Display>::fmt` (`+0x440`) and `RatchetState::consume_message_key`
(`+0x474`). -/
abbrev segS4PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x3e4#64

/-- **S5 entry (`+0x5b8` = `0x34954`)**: `add x27, sp, #0x38; sub x8, x29, #0x80; ...`
after `consume_message_key` returns `Ok(mkg)` and the formatted `Display` `String` at `sp + 0x3d0`
has been dropped. -/
abbrev segS5PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x5b8#64

/-- **S6 entry (`+0x5dc` = `0x34978`)**: `ldur q0, [x23, #0x18]; str x8, [sp, #0x8]; ...`
after `bl spqr::recv` (`+0x5cc`) returns `Ok(newPqrState, pqrKey)` and passes the `cmn x8, #1;
b.eq 0x3a094` check (`+0x5d0 .. +0x5d8`). -/
abbrev segS6PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x5dc#64

/-- **S7 entry (`+0x63c` = `0x349d8`)**: `ldr x1, [sp, #0x30]; ldr x2, [sp, #0x20]; ...`
right after `bl MessageKeyGenerator::generate_keys` returns at `+0x638` (`0x349d4`). -/
abbrev segS7PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x63c#64

/-- **S8 entry (`+0x678` = `0x34a14`)**: `ldp x0, x1, [x22, #0x18]; sub x9, x29, #0x80; ...`
after `bl SignalMessage::verify_mac_with_addresses` (`+0x65c`) returns `Ok(true)` and passes the
`cmn x26, #2` and `tbz w8, #0, 0x34cb0` checks (`+0x660 .. +0x674`). -/
abbrev segS8PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x678#64

/-- **S9 entry (`+0x6a4` = `0x34a40`)**: `ldr q0, [x23]; ldr x8, [sp, #0x3e0]; ...`
after `bl aes_256_cbc_decrypt` (`+0x694`) returns `some pt` and passes the `cmn x8, #1;
b.eq 0x34db8` check (`+0x698 .. +0x6a0`). -/
abbrev segS9PC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x6a4#64

/-- **ErrTail entry (`+0x30c` = `0x346a8`)**: `ldur q0, [x20, #0x28]; ldr q1, [x20, #0x40]; ...`
common `TripleRatchet` drop and error return block when an error occurs after
`TR::from_session_state` has taken `receiver_chains` and `pq_ratchet_state` from `x.ss`. -/
abbrev errTailPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x30c#64

/-- **ErrTail chain-drop loop header (`+0x33c` = `0x346d8`)**: `mov x0, x19; bl drop_glue<Chain>`
iterating over `tr.ratchet.receiver_chains` (`x19` advancing by `0x68 = 104`, `x21` decrementing by
`1`). -/
abbrev errDropChainLoopPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x33c#64

/-- **Shared return epilogue (`+0x394` = `0x34730`)**: `add sp, sp, #0x580; ldp x20, x19, ...; ret`
(`+0x394 .. +0x3b0`). -/
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

/-- **ErrTail checkpoint state (`errTailPC img = +0x30c`)**:
Common error cleanup entry after `TR::from_session_state` has succeeded (`sessionStateAt A x.ss
x.G.afterTrFrom st1`, where `st1 = (Mut.exec TripleRatchet.fromSessionState x.st).2 =
(x.model C S parse).2` and `x.G.AfterTryDecrypt false x.G.afterTrFrom`).
* `x19 = x.ret`, `x20 = sp + 0x140`, `x26 = speTag e`;
* `sp + 0x168..0x190` (`x20 + 0x28 .. x20 + 0x50`) holds
  `speBodyAt A (utf8 "decrypt") (sp + 0x168) e`;
* `sp + 0x38..0x140` holds `trAt A (sp + 0x38) trG tr` (whose `receiver_chains` and `pqr_state`
  will be dropped at `+0x334 .. +0x380`). -/
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

/-- **S1 checkpoint state (`segS1PC img = +0x1d8`)**:
Prologue and `local_identity_key` / `remote_identity_key` / `is_same_account` have completed with
`w1 = 0` (`self_session = false`).
* Live registers: `x19 = x.ret`, `x20 = sp + 0x140`, `x21 = x.ss`, `x22 = x.msgA`,
  `x23 = sp + 0x500` (`x29 - 0x80`), `(x24).setWidth 8 = msgTypeByte x.msgType`, `x25 = x.locA`,
  `(x1).setWidth 32 = 0#32`.
* Stack frame (`[sp .. sp + 0x580]`, 1408 B): `[sp + 0x30] = x.remA`, and the remaining scratch
  regions `[sp .. sp + 0x30]` (48 B) and `[sp + 0x38 .. sp + 0x580]` (1352 B) are uninitialized. -/
def S1State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS1PC img ∧
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

/-- **S2 checkpoint state (`segS2PC img = +0x2a4`)**:
`TR::from_session_state` returned `Ok(tr)` (`Mut.exec TripleRatchet.fromSessionState x.st =
(.ok tr, st1)`), `tr` (`264` B) has been copied from `sp + 0x190` to `sp + 0x38..0x140`,
`x.locA` is stored at `[sp + 0x20]`, `x.msg.counter` (`u32`) is stored at `[sp + 0x28]`,
and `x0 = sp + 0x38`, `x1 = x.msgA + 0x38`, `x8 = sp + 0x190` are set up for
`bl find_receiver_chain_key`. -/
def S2State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS2PC img ∧
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

/-- **S3 checkpoint state (`segS3PC img = +0x500`)**:
`find_receiver_chain_key` returned `Ok(None)` (`w9 = 0` at `+0x3b8: cmp w9, #1; +0x3cc: b.ne
0x3489c`), entering the inlined `RatchetState::dh_ratchet_step(&mut tr.ratchet,
&x.msg.senderRatchetKey)` block with `x12 = sp + 0x2c0`. -/
def S3State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS3PC img ∧
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

/-- **S4 checkpoint state (`segS4PC img = +0x3e4`)**:
Join point after `ensureReceiverChain` succeeds with `.ok ck` (either directly from S2 with
`draws = 0` or after `dhRatchetStep` in S3 with `draws = min 32 x.rest.length` and updated
`trG` / `tr`).
The 36-byte `ChainKey` `ck` (`chainKeyBytes ck`) is staged across `sp + 0x2b0..0x2d4` with the
first 20 bytes (`(chainKeyBytes ck).take 20`) at `sp + 0x2c0..0x2d4` and the last 16 bytes
(`(chainKeyBytes ck).drop 20`, bytes 20..31 of `ck.key` plus `ck.index`) at `sp + 0x2b0..0x2c0`
(`x25 + 0x120`), with `x12 = sp + 0x2c0` so that `+0x3e4..+0x428` reassembles `chainKeyBytes ck`
at `sp + 0x2e0..0x304`. -/
def S4State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS4PC img ∧
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

/-- **S5 checkpoint state (`segS5PC img = +0x5b8`)**:
`consume_message_key` returned `Ok(mkg)` and its formatted `Display` string has been freed.
* a 32-bit word `msgW` with low byte `msgTypeByte x.msgType` is saved at `[sp + 0x1c]` (`str w24`;
  `w24` is the caller's `w5`, whose upper bits AAPCS64 leaves unspecified; readers use `strb`);
* `w24 = 1#32` (`MessageKeyGenerator::Seed` tag), `w26` holds the 4 padding bytes
  from `[sp + 0x194]`;
* `mkg.seed` `Vec<u8>` (`32` B) is split across `cap = seedCap` at `[sp + 0x28]`, `ptr = seedPtr` at
  `[sp + 0x10]`, `len = 32` at `[sp + 0x450]`, and `mkg.counter` (`u32`) at `[sp + 0x458]` (`+0x57c`
  `ldur q0, [x25, #0x18]`, `+0x598` `stp q0, q1, [x8, #0x80]` with `x8 = sp + 0x3d0`). -/
def S5State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS5PC img ∧
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

/-- **S6 checkpoint state (`segS6PC img = +0x5dc`)**:
`spqr::recv` returned `Ok(newPqrState, pqrKey)` at `sp + 0x500..0x530`, with `x8 = newPqrCap`
loaded by `+0x5d0: ldur x8, [x29, #-0x80]`. -/
def S6State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS6PC img ∧
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

/-- **S7 checkpoint state (`segS7PC img = +0x63c`)**:
`MessageKeyGenerator::generate_keys` returned `mks = mkg.generateKeys C.F pqrKey` (`84` B) at
`sp + 0x500..0x554`, with `newPqrState` split across `cap = newPqrCap` at `[sp + 0x8]`,
`ptr = newPqrPtr` at `[sp + 0x28]`, and `len = newPqrState.length` in `x24`. -/
def S7State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS7PC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- **S8 checkpoint state (`segS8PC img = +0x678`)**:
`SignalMessage::verify_mac_with_addresses` returned `Ok(true)`. Same frame and register state as
`S7State`, at `segS8PC img`. -/
def S8State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS8PC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-- **S9 checkpoint state (`segS9PC img = +0x6a4`)**:
`aes_256_cbc_decrypt` returned `some pt`, placing `vecU8 A (sp + 0x3d0) pt`
at `sp + 0x3d0..0x3e8`. -/
def S9State (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  s.pc = segS9PC img ∧
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
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

/-! ## 4. Segment Contracts `S0Spec` .. `S9Spec`, `ErrTailSpec`, and `TryDecryptOk` -/

/-- **ErrTail contract (`+0x30c → +0x394 → +0x3b0`, `ErrTail.lean`)**:
From `ErrTailState` at `errTailPC img` (`+0x30c`) when `(x.model C S parse).1 = .error e`
(`e ≠ .panic`),
`(x.model C S parse).2 = st1`, and `draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest`,
execution writes `speAt A (utf8 "decrypt") x.ret e` (`vecResultAt A x.ret (.error e)`), drops all
chains in `tr.ratchet.receiver_chains` via `drop_glue<Chain>` (`+0x33c .. +0x34c`), deallocates the
`receiver_chains` buffer (`+0x350 .. +0x368`) and `tr.pqr_state` buffer (`+0x36c .. +0x380`),
restores `x19..x30` and `sp = s0.sp` (`+0x394 .. +0x3ac`), and returns at `+0x3b0`. -/
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

/-- **S0 contract (`+0x000 → +0x1d8`, `Seg0.lean`)**:
From `tryDecryptEntry img` (`0x6eff8`), the prologue (`+0x000 .. +0x04c`), `local_identity_key`
(`+0x050`), `remote_identity_key` (`+0x09c`), and either the `remoteIdentity = none` warn path
(`+0x180 → +0x564 → +0x0b0 → +0x14c` with `logOff img`) or `is_same_account` (`+0x1d0`, returning
`false` since `x.st.remoteIdentity ≠ some x.st.localIdentity`) reach `segS1PC img` (`+0x1d8`) in
`S1State`. -/
def S0Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOk img C A ctl abs →
  RemoteIdentityKeyOk img C A ctl abs →
  IsSameAccountOk img.base C ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segS1PC img) s0
        (S1State A ctl img x R s0)

/-- **S1 contract (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`, `Seg1.lean`)**:
From `S1State` at `segS1PC img` (`+0x1d8`), `TR::from_session_state(x.ss, false)` (`+0x1e0`):
* if `Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1)`
  (`x.st.remoteIdentity = none`),
  copies the SPE to `x.ret` (`+0x1e4 .. +0x200 → +0x384 .. +0x390`) and returns via the epilogue
  (`+0x394 .. +0x3b0`), satisfying `tryDecryptSpec`;
* if `Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1)`, copies `tr` (`264` B) to
  `sp + 0x38..0x140` (`+0x204 .. +0x2a0`) and reaches `segS2PC img` (`+0x2a4`) in `S2State`. -/
def S1Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      S1State A ctl img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
          (tryDecryptSpec C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ∃ trG, S2State A ctl img x trG tr st1 R s0 s'

/-- **S2 contract (`+0x2a4 → +0x3e4 / +0x500 / +0x30c`, `Seg2.lean`)**:
From `S2State` at `segS2PC img` (`+0x2a4`), `RatchetState::find_receiver_chain_key` (`+0x2a4`)
branches on `tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey`:
* `.ok (some ck)`: stages `ck` (`36` B) at `sp + 0x2b0..0x2d4` (`+0x3b4 .. +0x3e0`) and reaches
  `segS4PC img` (`+0x3e4`) in `S4State` with `draws = 0`;
* `.ok none`: reaches `segS3PC img` (`+0x500`) in `S3State`;
* `.error e` (`missingReceiverChainKey`): stages `e` at `x26` and `sp + 0x168..0x190`
  (`+0x2b4 .. +0x308`) and reaches `errTailPC img` (`+0x30c`) in `ErrTailState` with `draws = 0`. -/
def S2Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  FindReceiverChainKeyOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      S2State A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | .ok (some ck) =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segS4PC img) s
          (S4State A ctl img x trG tr st1 ck 0 R s0)
      | .ok none =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segS3PC img) s
          (S3State A ctl img x trG tr st1 R s0)
      | .error e =>
        reaches_pc (tripleRatchetProgAt img.base C ctl abs) (errTailPC img) s
          (ErrTailState A ctl img x trG tr st1 e 0 R s0)

/-- **S3 contract (`+0x500 → +0x3e4 / +0x30c` or OOM panic)**:
From `S3State` at `segS3PC img` (`+0x500`) when
`tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none`, the inlined
`RatchetState::dh_ratchet_step(&mut tr.ratchet, &x.msg.senderRatchetKey)`:
* if `Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet =
  (.ok ck, r1)`, reaches `segS4PC img` (`+0x3e4`) in `S4State` with `{ tr with ratchet := r1 }`,
  updated ghost `trG'`, and `draws = min 32 x.rest.length` (or panics on allocator failure);
* if `Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet =
  (.error e, r1)`, reaches `errTailPC img` (`+0x30c`) in `ErrTailState` with `draws =
  decryptDraws C x.st x.msg.senderRatchetKey x.rest` (or panics on allocator failure).

Assumes `tr.ratchet.receiverChains.length < 2 ^ 32` so `grow_one` (`+0xa98`) cannot hit
`CapacityOverflow`, and `rootStack ≤ s0.sp.toNat` so the stack salt pointers `sp + 0x3b0` (`+0x544`)
and `sp + 0x4a0` (`+0x7d4`) passed to `Hkdf::extract` are non-null. -/
def S3Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
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
      S3State A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', S4State A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG' r1,
              ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- **S4 contract (`+0x3e4 → +0x5b8 / +0x30c` or panic, `Seg4.lean`)**:
From `S4State` at `segS4PC img` (`+0x3e4`), execution formats `x.rem` via `<ProtocolAddress as
Display>::fmt` (`+0x440`), calls `RatchetState::consume_message_key` (`+0x474`), and drops the
formatted `Display` string (`+0x4ac` or `+0x5b4`):
* if `Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
  x.msgType) tr.ratchet = (.ok mkg, r2)`, reaches `segS5PC img` (`+0x5b8`) in `S5State` with
  `{ tr with ratchet := r2 }` (or panics on allocator failure);
* if `(.error .panic, _)`, panics satisfying `tryDecryptSpec.onPanic`;
* if `(.error e, r2)` with `e ≠ .panic`, reaches `errTailPC img` (`+0x30c`) in `ErrTailState`. -/
def S4Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CmkOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
      (R : SepProp) (s0 s : State),
      S4State A ctl img x trG tr st1 ck draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
          x.msgType) tr.ratchet with
      | (.ok mkg, r2) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', S5State A ctl img x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | (.error e, r2) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((e ≠ .panic ∧ ∃ trG',
              ErrTailState A ctl img x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R)))

/-- `spqrRecvSpec` restricted to states meeting `Q x.1.bytes` with message length `< 2 ^ 40`,
stack `Pstk s.sp.toNat`, and an extra frame `F` preserved from `pre` to `post`. -/
def spqrRecvSpecQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) : Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvSpec A S img with
    pre := fun x s =>
      ⌜Q x.1.bytes ∧ x.2.1.bytes.length < 2 ^ 40 ∧ Pstk s.sp.toNat⌝ ∗
        F ∗ (spqrRecvSpec A S img).pre x s
    post := fun x s0 sf => F ∗ (spqrRecvSpec A S img).post x s0 sf }

/-- `SpqrRecvOk` on the states meeting `Q` with stack predicate `Pstk` and frame `F`. -/
def SpqrRecvOkQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrRecvName)
    (spqrRecvSpecQF Q Pstk F A S img)

/-- `SpqrRecvOk` on the states meeting `Q`: the in-image `spqr::recv` meets `spqrRecvSpec`
restricted to `Q x.1.bytes`. `Q := fun _ => True` is implied by `SpqrRecvOk`
(`spqrRecvOkQ_of_recvOk`) and `Q := (· = [])` is the conclusion of `SpqrRecvEmptyRunStmt`
(`spqrRecvOkQ_empty`). -/
def SpqrRecvOkQ (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrRecvName)
    ((spqrRecvSpec A S img).restrictPre (Q ·.1.bytes))

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

/-- **S5 contract (`+0x5b8 → +0x5dc / +0x30c` or panic, `Seg5.lean`)** with frame `F`. -/
def S5SpecQF (Q : List (BitVec 8) → Prop) (Pstk : Nat → Prop) (F : SepProp) (img : Obj.Image)
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
      S5State A ctl img x trG tr st1 mkg draws (F ∗ R) s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws (F ∗ R) s0 s' ∧
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

/-- **S5 contract (`+0x5b8 → +0x5dc / +0x30c` or panic, `Seg5.lean`)**:
From `S5State` at `segS5PC img` (`+0x5b8`) with `tr.pqrState = x.st.pqRatchetState`,
`spqr::recv(&tr.pqr_state, &x.msg.pq_ratchet)` (`+0x5cc`):
* if `S.recv tr.pqrState x.msg.pqRatchet = .ok (newPqrState, pqrKey)`, reaches `segS6PC img`
  (`+0x5dc`) in `S6State` (or panics on `S.recvPanics` / allocator failure);
* if `S.recv tr.pqrState x.msg.pqRatchet = .error sd`, formats the error string via `format_inner`
  (`+0x868` for `sd = false` → `.invalidMessage x.msgType .pqRatchet`; `+0x990` for `sd = true` →
  `.invalidState`), frees `mkg.seed` (`+0x9c4 .. +0x9d4`), and reaches `errTailPC img` (`+0x30c`)
  in `ErrTailState` (or panics on `S.recvPanics` / allocator failure).
The `spqr::recv` call is in-image code, crossed with `SpqrRecvOkQ Q`: the recv contract on states
meeting `Q`, for a session state whose pq state meets `Q` (`Q := fun _ => True`:
`SpqrRecvOk`; `Q := (· = [])`: `SpqrRecvEmptyRunStmt`). -/
def S5Spec (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
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
      S5State A ctl img x trG tr st1 mkg draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
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

/-- **S6 contract (`+0x5dc → +0x63c`)**:
From `S6State` at `segS6PC img` (`+0x5dc`), saves `newPqrState` across `([sp + 0x8], [sp + 0x28],
x24)`, reassembles `mkg` at `sp + 0x190..0x1b8` and `pqrKey` at `sp + 0x360..0x378`, and calls
`MessageKeyGenerator::generate_keys` (`+0x638`), reaching `segS7PC img` (`+0x63c`) in `S7State`
with `mks = mkg.generateKeys C.F pqrKey` under `mkg.seed.length = 32`. -/
def S6Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  GenerateKeysOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
      (R : SepProp) (s0 s : State),
      mkg.seed.length = 32 →
      S6State A ctl img x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segS7PC img) s
        (S7State A ctl img x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0)

/-- **S7 contract (`+0x63c → +0x678 / +0x30c` or OOM panic, `Seg7.lean`)**:
From `S7State` at `segS7PC img` (`+0x63c`), calls `SignalMessage::verify_mac_with_addresses`
(`+0x65c`):
* if `x.msg.verifyMacWithAddresses C.F
    (serializeAddresses (serviceIdParse parse) x.rem x.loc) tr.remoteIdentityKey
  tr.localIdentityKey mks.macKey = true`, reaches `segS8PC img` (`+0x678`) in `S8State` (or panics
  on allocator failure);
* if `false`, allocates the 23-byte `"bad authentication code"` string (`+0x920`), frees
  `newPqrState` (`+0x95c .. +0x968 → +0x9d0 .. +0x9d8`), and reaches `errTailPC img` (`+0x30c`) in
  `ErrTailState` with `.invalidMessage x.msgType .macFailed` (or panics on allocator failure). -/
def S7Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  VerifyMacWithAddressesOk img C A ctl parse abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      S7State A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
          tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      else
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (ErrTailState A ctl img x trG tr st1
              (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- **S8 contract (`+0x678 → +0x6a4 / +0x30c` or OOM panic, `Seg8.lean`)**:
From `S8State` at `segS8PC img` (`+0x678`), calls `aes_256_cbc_decrypt` (`+0x694`):
* if `aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext = some pt`, reaches
  `segS9PC img` (`+0x6a4`) in `S9State` (or panics on allocator failure);
* if `none`, formats the `"bad ciphertext"` error string via `format_inner` (`+0xa5c`), frees
  `newPqrState` (`+0xa68 .. +0xa6c → +0x964 → +0x9d0 .. +0x9d8`), and reaches `errTailPC img`
  (`+0x30c`) in `ErrTailState` with `.invalidMessage x.msgType .badCiphertext` (or panics on
  allocator failure). -/
def S8Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
      (newPqrState : List (BitVec 8)) (draws : Nat)
      (R : SepProp) (s0 s : State),
      S8State A ctl img x trG tr st1 mks newPqrState draws R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
      | some pt =>
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (S9State A ctl img x trG tr st1 newPqrState pt draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))
      | none =>
        ∃ s' : State, Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          (ErrTailState A ctl img x trG tr st1 (.invalidMessage x.msgType .badCiphertext)
              draws R s0 s' ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- **S9 contract (`+0x6a4 → +0x4b8 → +0x394 → +0x3b0`, `Seg9.lean`)**:
From `S9State` at `segS9PC img` (`+0x6a4`) when `(x.model C S parse).1 = .ok pt`,
`(x.model C S parse).2 = (({ tr with pqrState := newPqrState }).applyToSessionState
st1).clearUnacknowledgedPreKeyMessage`,
and `draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest`, execution frees the old
`tr.pqr_state` buffer (`+0x6bc .. +0x6c8`), moves `newPqrState` into `tr.pqr_state`
(`+0x6d0 .. +0x6e0`),
branches to `+0x4b8`, writes `Ok(pt)` (`okTagVec` at `[x19]` and `pt` `Vec<u8>` at `x19 + 8`),
copies `tr` (`264` B) to `sp + 0x190` via `memcpy` (`+0x4dc`), calls `TR::apply_to_session_state`
(`+0x4e8`) and `SessionState::clear_unacknowledged_pre_key_message` (`+0x4f0`), and returns via the
epilogue `+0x394 .. +0x3b0` (or panics on allocator failure inside `TR::apply_to_session_state`). -/
def S9Spec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
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
      S9State A ctl img x trG tr st1 newPqrState pt
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (tryDecryptSpec C A ctl parse S img) x R s0 s

/-- `tryDecryptSpec` restricted to session states meeting `Q x.st.pqRatchetState` with frame `F`. -/
def tryDecryptSpecQF (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    Spec TryDecryptGhost :=
  { tryDecryptSpec C A ctl parse S img with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ F ∗ (tryDecryptSpec C A ctl parse S img).pre x s
    post := fun x s0 sf => F ∗ (tryDecryptSpec C A ctl parse S img).post x s0 sf }

/-- Target `subroutine_ok` statement for `Root.lean` with frame `F`. -/
def TryDecryptOkQF (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (tryDecryptEntry img)
    (tryDecryptSpecQF Q F C A ctl parse S img)

/-- Target `subroutine_ok` statement for `Root.lean`:
`try_decrypt_with_state::<HookRng>` (`tryDecryptEntry img = img.base + 0x6eff8#64`) meets
`tryDecryptSpec C A ctl parse S img` on `tripleRatchetProgAt img.base C ctl abs`,
restricted to session states whose
pq state meets `Q` (`Q := fun _ => True`: unrestricted, `Spec.restrictPre_true`). -/
def TryDecryptOk (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (tryDecryptEntry img)
    ((tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

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

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
