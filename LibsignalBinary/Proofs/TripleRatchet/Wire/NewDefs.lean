/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs

/-!
# Specification of `<libsignal_protocol::protocol::SignalMessage>::new`

Machine-level specification (`signalMessageNewSpec`) and `subroutine_ok` predicates for
`<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`), refining
`SignalMessage.new C.F protoSignalCodec` over callee contracts for `PublicKey::serialize`,
`encode_varint`, `wire::SignalMessage::encoded_len`, `SignalMessage::serialize_addresses`, and
`SignalMessage::compute_mac`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol name and stack budget -/

/-- `<libsignal_protocol::protocol::SignalMessage>::new` (image offset `0x1d918`,
556 instructions). -/
abbrev signalMessageNewName : String :=
  "<libsignal_protocol::protocol::SignalMessage>::new"

/-- Stack budget for `SignalMessage::new`: its 416-byte (`0x1a0`) stack frame plus the maximum
callee stack budget `computeMacStack` (which dominates `encodeVarintStack`,
`serializeAddressesStack`, `publicKeySerializeStack`, `encodedLenStack`, and `allocHookStack`). -/
abbrev signalMessageNewStack : Nat := computeMacStack + 0x1a0

/-! ## MAC callee `subroutine_ok` hypotheses -/

/-- Callee hypothesis on `tripleRatchetProgAtExt b ext`: `SignalMessage::serialize_addresses` (`0x1d4b0`)
meets `serializeAddressesSpec A parse`. -/
def SerializeAddressesOkExt (b : BitVec 64) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr serializeAddressesName)
    (serializeAddressesSpec A parse)

/-- Callee hypothesis on `tripleRatchetProgAt`: `SignalMessage::serialize_addresses` (`0x1d4b0`)
meets `serializeAddressesSpec A parse`. -/
def SerializeAddressesOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr serializeAddressesName)
    (serializeAddressesSpec A parse)

/-- Callee hypothesis on `tripleRatchetProgAtExt img.base ext`: `SignalMessage::compute_mac` (`0x1cfc0`)
meets `(computeMacSpec C.F A).inImage img`. -/
def ComputeMacOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
    ((computeMacSpec C.F A).inImage img)

/-- Callee hypothesis on `tripleRatchetProgAt`: `SignalMessage::compute_mac` (`0x1cfc0`)
meets `(computeMacSpec C.F A).inImage img`. -/
def ComputeMacOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr computeMacName)
    ((computeMacSpec C.F A).inImage img)

/-- Image-independent variant of `ComputeMacOkExt` on any base `b`. -/
def ComputeMacRawOkExt (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr computeMacName)
    (computeMacSpec C.F A)

/-- Image-independent variant of `ComputeMacOk` on any base `b`. -/
def ComputeMacRawOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr computeMacName)
    (computeMacSpec C.F A)

/-! ## Ghost state and pure model helpers for `SignalMessage::new` (`0x1d918`) -/

/-- Ghost arguments of `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`). -/
structure SignalMessageNewGhost where
  /-- `message_version: u8` (`w0`, spilled to `[sp + 0x54]`). -/
  messageVersion : BitVec 8
  /-- `mac_key: &[u8]` pointer (`x1`, with length `x2 = 32`, spilled to `[sp + 0x40..0x50]`). -/
  macKeyA : BitVec 64
  /-- The 32-byte MAC key value (`keyToBytes32 macKey`). -/
  macKey : BitVec 256
  /-- First word of `addresses: Option<(&ProtocolAddress, &ProtocolAddress)>` (`x3 = locA` when `loc.isSome` with `locA ≠ 0`, or `0` when `loc = none`). -/
  locA : BitVec 64
  /-- Optional sender (local) `ProtocolAddress` ghost (`optAddrAt A locA loc`). -/
  loc : Option AddrGhost
  /-- Second word of `addresses`: recipient `&ProtocolAddress` (`x4 = remA` when `x3 ≠ 0`). -/
  remA : BitVec 64
  /-- Recipient (remote) `ProtocolAddress` ghost (`protocolAddressAt A rem remA`). -/
  rem : AddrGhost
  /-- `sender_ratchet_key: &PublicKey` (`x5`, 32 bytes). -/
  senderRatchetKeyA : BitVec 64
  /-- The `sender_ratchet_key: PublicKey` model value. -/
  senderRatchetKey : PublicKey
  /-- `counter: u32` (`w6`). -/
  counter : BitVec 32
  /-- `previous_counter: u32` (`w7`). -/
  previousCounter : BitVec 32
  /-- `ciphertext: &[u8]` pointer at caller `[sp + 0x00]`. -/
  ciphertextA : BitVec 64
  /-- `ciphertext` slice bytes (`[sp + 0x08] = ciphertext.length ≤ 2^32`). -/
  ciphertext : List (BitVec 8)
  /-- `sender_identity_key: &PublicKey` at caller `[sp + 0x10]`. -/
  senderIkA : BitVec 64
  /-- Sender `IdentityKey`. -/
  senderIk : IdentityKey
  /-- `receiver_identity_key: &PublicKey` at caller `[sp + 0x18]`. -/
  receiverIkA : BitVec 64
  /-- Receiver `IdentityKey`. -/
  receiverIk : IdentityKey
  /-- `pq_ratchet: &[u8]` pointer at caller `[sp + 0x20]`. -/
  pqRatchetA : BitVec 64
  /-- `pq_ratchet` slice bytes (`[sp + 0x28] = pqRatchet.length < 2^32`). -/
  pqRatchet : List (BitVec 8)
  /-- Output `sret` pointer (`x8`, 120-byte `Result<SignalMessage, SignalProtocolError>`). -/
  ret : BitVec 64

/-- Optional 36-byte serialized address pair `x.loc.bind (serializeAddresses parse · x.rem)`. -/
def SignalMessageNewGhost.addresses (parse : UuidParser) (x : SignalMessageNewGhost) :
    Option (List (BitVec 8)) :=
  x.loc.bind fun l => serializeAddresses (serviceIdParse parse) l x.rem

/-- Temporary `ProtoSignalMessage` assembled on the stack (`sp + 0x80..+0xf0`) before encoding. -/
def SignalMessageNewGhost.protoMsg (parse : UuidParser) (x : SignalMessageNewGhost) :
    ProtoSignalMessage :=
  { ratchetKey := some x.senderRatchetKey.serialize
    counter := some x.counter
    previousCounter := some x.previousCounter
    ciphertext := some x.ciphertext
    pqRatchet := if x.pqRatchet.isEmpty then none else some x.pqRatchet
    addresses := x.addresses parse }

/-- Pure `SignalMessage` model value produced by `SignalMessage.new F protoSignalCodec`. -/
def SignalMessageNewGhost.model (F : ShaCompress) (parse : UuidParser)
    (x : SignalMessageNewGhost) : SignalMessage :=
  SignalMessage.new F protoSignalCodec x.messageVersion x.macKey (x.addresses parse)
    x.senderRatchetKey x.counter x.previousCounter x.ciphertext
    x.senderIk x.receiverIk x.pqRatchet

/-- Caller-owned stack argument words `[sp + 0x00 .. sp + 0x30)` (`ciphertext` slice,
`sender_identity_key`, `receiver_identity_key`, `pq_ratchet` slice) and borrowed input buffers,
all preserved unchanged from precondition to postcondition. -/
def SignalMessageNewGhost.inputsAt (A : RustAlloc) (x : SignalMessageNewGhost) (sp : BitVec 64) :
    SepProp :=
  (sp ↦₆₄ x.ciphertextA) ∗
    ((sp + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
    ((sp + 0x10#64) ↦₆₄ x.senderIkA) ∗
    ((sp + 0x18#64) ↦₆₄ x.receiverIkA) ∗
    ((sp + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
    ((sp + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
    (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
    optAddrAt A x.locA x.loc ∗
    protocolAddressAt A x.rem x.remA ∗
    (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
    (x.ciphertextA ↦ₛ x.ciphertext) ∗
    (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
    (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
    (x.pqRatchetA ↦ₛ x.pqRatchet)

/-! ## Specification of `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`) -/

/-- Machine-level specification of `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`).
Given register arguments `(w0..w7, x8)` and caller stack/heap inputs `x.inputsAt A s.sp` with
`x.ciphertext.length ≤ 2 ^ 32` and `x.pqRatchet.length < 2 ^ 32`, constructs the temporary
`wire::SignalMessage` on the stack, encodes `[versionByte x.messageVersion] ++ encode (x.protoMsg parse)`
and appends the 8-byte truncated HMAC from `compute_mac`, writes the 120-byte `Ok`
`signalMessageAt A g x.ret (x.model F parse)`, and frees temporary `wire::SignalMessage` buffers;
panics only on allocator failure (`allocFailedIn`). -/
def signalMessageNewSpec (F : ShaCompress) (A : RustAlloc) (parse : UuidParser) :
    Spec SignalMessageNewGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.messageVersion ∧
      s.readReg64 .x1 = x.macKeyA ∧ s.readReg64 .x2 = 32#64 ∧
      s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64) ∧
      (x.loc.isSome → x.locA ≠ 0#64) ∧ s.readReg64 .x4 = x.remA ∧
      s.readReg64 .x5 = x.senderRatchetKeyA ∧
      (s.readReg64 .x6).setWidth 32 = x.counter ∧
      (s.readReg64 .x7).setWidth 32 = x.previousCounter ∧
      s.readReg64 .x8 = x.ret ∧
      x.ciphertext.length ≤ 2 ^ 32 ∧ x.pqRatchet.length < 2 ^ 32⌝ ∗
      x.inputsAt A s.sp ∗
      memRegion x.ret 120 ∗ A.pool ∗ stackAt s.sp signalMessageNewStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      x.inputsAt A s0.sp ∗
      (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model F parse)) ∗
      A.pool ∗ stackAt s0.sp signalMessageNewStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Target `subroutine_ok` propositions -/

/-- `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`) meets
`(signalMessageNewSpec C.F A parse).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def SignalMessageNewOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName)
    ((signalMessageNewSpec C.F A parse).inImage img)

/-- `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`) meets
`(signalMessageNewSpec C.F A parse).inImage img` on `tripleRatchetProgAt img.base …`
under `ComputeMacOk img C A ctl parse abs`. -/
def SignalMessageNewOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr signalMessageNewName)
    ((signalMessageNewSpec C.F A parse).inImage img)

/-- Image-independent variant: `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`)
meets `signalMessageNewSpec C.F A parse` on `tripleRatchetProgAtExt b ext`. -/
def SignalMessageNewRawOkExt (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName)
    (signalMessageNewSpec C.F A parse)

/-- Image-independent variant: `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`)
meets `signalMessageNewSpec C.F A parse` on `tripleRatchetProgAt b …` (under `ComputeMacRawOk b C A ctl parse abs`). -/
def SignalMessageNewRawOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName)
    (signalMessageNewSpec C.F A parse)

/-! ## Extended-hook (`extHookStack`) stack budget, spec, and `OkExtX` predicate -/

/-- Stack budget for `SignalMessage::new` (`0x1d918`) over `extHookStack`:
`computeMacStackX + 0x1a0 = 16912 + 416 = 17328` bytes. -/
abbrev signalMessageNewStackX : Nat := computeMacStackX + 0x1a0

/-- `signalMessageNewSpec F A parse` at `signalMessageNewStackX`. -/
def signalMessageNewSpecX (F : ShaCompress) (A : RustAlloc) (parse : UuidParser) :
    Spec SignalMessageNewGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.messageVersion ∧
      s.readReg64 .x1 = x.macKeyA ∧ s.readReg64 .x2 = 32#64 ∧
      s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64) ∧
      (x.loc.isSome → x.locA ≠ 0#64) ∧ s.readReg64 .x4 = x.remA ∧
      s.readReg64 .x5 = x.senderRatchetKeyA ∧
      (s.readReg64 .x6).setWidth 32 = x.counter ∧
      (s.readReg64 .x7).setWidth 32 = x.previousCounter ∧
      s.readReg64 .x8 = x.ret ∧
      x.ciphertext.length ≤ 2 ^ 32 ∧ x.pqRatchet.length < 2 ^ 32⌝ ∗
      x.inputsAt A s.sp ∗
      memRegion x.ret 120 ∗ A.pool ∗ stackAt s.sp signalMessageNewStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      x.inputsAt A s0.sp ∗
      (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model F parse)) ∗
      A.pool ∗ stackAt s0.sp signalMessageNewStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`) meets
`(signalMessageNewSpecX C.F A parse).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def SignalMessageNewOkExtX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName)
    ((signalMessageNewSpecX C.F A parse).inImage img)

end CryptoVerification.LibsignalTripleRatchet

