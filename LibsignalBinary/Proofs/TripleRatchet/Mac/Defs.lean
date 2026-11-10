/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WPp

/-!
# Specifications for `SignalMessage` MAC Computation and Verification

Separation-logic contracts, result layouts, and stack budgets for:
- `<SignalMessage>::serialize_addresses` (`serializeAddressesSpec` ↔ `serializeAddresses`);
- `<SignalMessage>::compute_mac` (`computeMacSpec` ↔ `computeMac`);
- `<SignalMessage>::verify_mac_with_addresses` (`verifyMacWithAddressesSpec` ↔
  `SignalMessage.verifyMacWithAddresses`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Symbol names -/

abbrev serializeAddressesName : String :=
  "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses"

abbrev computeMacName : String :=
  "<libsignal_protocol::protocol::SignalMessage>::compute_mac"

abbrev verifyMacWithAddressesName : String :=
  "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"

/-! ## Stack budgets (own frame + callee budget) -/

/-- `SignalMessage::serialize_addresses` frame (`0x1d4b0`: `sub sp, sp, #0x80` = 128 B) +
`allocHookStack`. -/
abbrev serializeAddressesStack : Nat := allocHookStack + 128

/-- `SignalMessage::compute_mac` frame (`0x1cfc0`: `sub sp, sp, #0x1f0` = 496 B) +
`publicKeySerializeStack` (`≥ newFromSliceStack` and `≥ allocHookStack`). -/
abbrev computeMacStack : Nat := publicKeySerializeStack + 496

/-- `SignalMessage::verify_mac_with_addresses` frame (`0x1d5a0`: `sub sp, sp, #0x120` = 288 B) +
`computeMacStack` (`≥ serializeAddressesStack` and `≥ allocHookStack`). -/
abbrev verifyMacWithAddressesStack : Nat := computeMacStack + 288

/-! ## `PublicKey::serialize` callee predicates -/

def PublicKeySerializeOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr publicKeySerializeName)
    (publicKeySerializeSpec A)

def PublicKeySerializeOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName)
    (publicKeySerializeSpec A)

def PublicKeySerializeOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr publicKeySerializeName)
    (publicKeySerializeSpec A)

/-! ## `SignalMessage::serialize_addresses` -/

/-- 24-byte `Option<Vec<u8>>` result of `SignalMessage::serialize_addresses` at `r`:
- `none`: `noneCap` (`-1`) at `r` and `memRegion (r + 8) 16`;
- `some bs`: a 36-byte `Vec<u8>` (`vecU8At A r 36#64 ptr bs`) at `r`. -/
def optSerializeAddressesAt (A : RustAlloc) (r : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => (r ↦₆₄ noneCap) ∗ memRegion (r + 8#64) 16
  | some bs => ∃∗ ptr : BitVec 64, vecU8At A r 36#64 ptr bs

/-- Ghost arguments of `SignalMessage::serialize_addresses` (`0x1d4b0`). -/
structure SerializeAddressesGhost where
  /-- Sret (`x0`, 24-byte `Option<Vec<u8>>`). -/
  ret : BitVec 64
  /-- `sender: &ProtocolAddress` (`x1`; `+0x018: mov x21, x1`, `+0x01c: ldp x9, x1, [x1, #8]`,
  `+0x09c: ldrb w8, [x21, #0x18]`). -/
  senderA : BitVec 64
  sender : AddrGhost
  /-- `recipient: &ProtocolAddress` (`x2`; `+0x028: mov x20, x2`, `+0x040: ldp x0, x1, [x20, #8]`,
  `+0x0ac: ldrb w8, [x20, #0x18]`). -/
  recipientA : BitVec 64
  recipient : AddrGhost

/-- Contract for `<SignalMessage>::serialize_addresses(x0 = ret, x1 = senderA, x2 = recipientA)`:
parses both service IDs via `ServiceId::parse_from_service_id_string` and writes
`optSerializeAddressesAt A x.ret (serializeAddresses (serviceIdParse parse) x.sender x.recipient)`. -/
def serializeAddressesSpec (A : RustAlloc) (parse : UuidParser) :
    Spec SerializeAddressesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.recipientA⌝ ∗
      protocolAddressAt A x.sender x.senderA ∗ protocolAddressAt A x.recipient x.recipientA ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp serializeAddressesStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protocolAddressAt A x.sender x.senderA ∗ protocolAddressAt A x.recipient x.recipientA ∗
      optSerializeAddressesAt A x.ret (serializeAddresses (serviceIdParse parse) x.sender x.recipient) ∗
      A.pool ∗ stackAt s0.sp serializeAddressesStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `SignalMessage::compute_mac` -/

/-- Ghost arguments of `SignalMessage::compute_mac` (`0x1cfc0`). -/
structure ComputeMacGhost where
  /-- Sret (`x0`, `Result<[u8; 8], SPE>`; `+0x024: mov x19, x0`, `+0x4a8: stp x9, x8, [x19]`). -/
  ret : BitVec 64
  /-- `sender_identity_key: &PublicKey` (`x1`, 32 bytes; `+0x030: mov x23, x1`,
  `+0x05c: mov x0, x23`, `+0x0a0: bl PublicKey::serialize`). -/
  senderA : BitVec 64
  sender : IdentityKey
  /-- `receiver_identity_key: &PublicKey` (`x2`, 32 bytes; `+0x02c: mov x22, x2`,
  `+0x188: mov x0, x22`, `+0x18c: bl PublicKey::serialize`). -/
  receiverA : BitVec 64
  receiver : IdentityKey
  /-- `mac_key: &[u8]` (`x3 = keyA`, `x4 = 32`; `+0x020: cmp x4, #0x20; +0x028: b.ne +0x0e0`,
  `+0x038: mov x1, x3; +0x03c: mov w2, #0x20`). Callers always pass length 32. -/
  keyA : BitVec 64
  macKey : BitVec 256
  /-- `message: &[u8]` (`x5 = msgA`, `x6 = message.length < 2^63`; `+0x040: mov x21, x6`,
  `+0x044: mov x20, x5`, `+0x2f0: and x22, x21, #0x7fffffffffffffc0`). -/
  msgA : BitVec 64
  message : List (BitVec 8)

/-- Contract for `<SignalMessage>::compute_mac(x0 = ret, x1 = senderA, x2 = receiverA, x3 = keyA,
x4 = 32, x5 = msgA, x6 = message.length)`: computes the 8-byte truncated HMAC-SHA256 over
`0x05 ‖ sender ‖ 0x05 ‖ receiver ‖ message` under `macKey`, writing `okTagVec` at `ret` and
`computeMac F x.sender x.receiver x.macKey x.message` at `ret + 8`. -/
def computeMacSpec (F : ShaCompress) (A : RustAlloc) : Spec ComputeMacGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.receiverA ∧
      s.readReg64 .x3 = x.keyA ∧ s.readReg64 .x4 = 32#64 ∧ s.readReg64 .x5 = x.msgA ∧
      (s.readReg64 .x6).toNat = x.message.length ∧ x.message.length < 2 ^ 63⌝ ∗
      memRegion x.ret 16 ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool ∗ stackAt s.sp computeMacStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ okTagVec) ∗
      ((x.ret + 8#64) ↦ₛ computeMac F x.sender x.receiver x.macKey x.message) ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool ∗ stackAt s0.sp computeMacStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `SignalMessage::verify_mac_with_addresses` -/

/-- `Result<bool, SignalProtocolError>::Ok(ok)` layout at `r`: `okTagVec` (`-2`) at `r` and
`1#8` / `0#8` at `r + 8`. -/
def verifyMacResultAt (r : BitVec 64) (ok : Bool) : SepProp :=
  (r ↦₆₄ okTagVec) ∗ ((r + 8#64) ↦₈ (if ok then 1#8 else 0#8))

/-- Ghost arguments of `SignalMessage::verify_mac_with_addresses` (`0x1d5a0`). -/
structure VerifyMacWithAddressesGhost where
  /-- `&self: &SignalMessage` (`x0`; `+0x024: ldr x8, [x0, #0x30]`, `+0x034: ldr x24, [x0, #0x28]`,
  `+0x038: mov x20, x0`, `+0x158: ldr x23, [x20, #0x58]`, `+0x180: ldr x8, [x20, #0x60]`). -/
  msgA : BitVec 64
  msgG : SignalMessageGhost
  msg : SignalMessage
  /-- `sender_address: &ProtocolAddress` (`x1`; `+0x028: stp x1, x2, [sp, #0x20]`,
  `+0x040: mov x22, x1`, `+0x168: mov x1, x22`). -/
  senderAddrA : BitVec 64
  senderAddr : AddrGhost
  /-- `receiver_address: &ProtocolAddress` (`x2`; `+0x028: stp x1, x2, [sp, #0x20]`,
  `+0x03c: mov x21, x2`, `+0x16c: mov x2, x21`). -/
  receiverAddrA : BitVec 64
  receiverAddr : AddrGhost
  /-- `sender_identity_key: &PublicKey` (`x3`, 32 bytes; `+0x048: mov x1, x3`). -/
  senderIkA : BitVec 64
  senderIk : IdentityKey
  /-- `receiver_identity_key: &PublicKey` (`x4`, 32 bytes; `+0x04c: mov x2, x4`). -/
  receiverIkA : BitVec 64
  receiverIk : IdentityKey
  /-- `mac_key: &[u8]` (`x5 = keyA`, `x6 = 32`; `+0x050: mov x3, x5; +0x054: mov x4, x6`). -/
  keyA : BitVec 64
  macKey : BitVec 256
  /-- Sret (`x8`, `Result<bool, SPE>`; `+0x020: mov x19, x8`). -/
  ret : BitVec 64

/-- Contract for `<SignalMessage>::verify_mac_with_addresses`: computes the 8-byte MAC via
`compute_mac`, compares it in constant time against the trailing 8 bytes of `msg.serialized`,
optionally checks `msg.addresses` against `serialize_addresses`, and writes
`verifyMacResultAt x.ret` (`Ok(true)` or `Ok(false)`). -/
def verifyMacWithAddressesSpec (img : Obj.Image) (F : ShaCompress) (A : RustAlloc)
    (parse : UuidParser) : Spec VerifyMacWithAddressesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.senderAddrA ∧
      s.readReg64 .x2 = x.receiverAddrA ∧ s.readReg64 .x3 = x.senderIkA ∧
      s.readReg64 .x4 = x.receiverIkA ∧ s.readReg64 .x5 = x.keyA ∧
      s.readReg64 .x6 = 32#64 ∧ s.readReg64 .x8 = x.ret⌝ ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      memRegion x.ret 9 ∗
      logOff img ∗
      A.pool ∗ stackAt s.sp verifyMacWithAddressesStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      verifyMacResultAt x.ret
        (x.msg.verifyMacWithAddresses F (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey) ∗
      logOff img ∗
      A.pool ∗ stackAt s0.sp verifyMacWithAddressesStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `extHookStack` stack budgets, specs, and `OkX` predicates -/

/-- `SignalMessage::serialize_addresses` frame (128 B) + `parseSidStack` (80 B) + `extHookStack`. -/
abbrev serializeAddressesStackX : Nat := parseSidStack + extHookStack + 128

/-- `SignalMessage::compute_mac` frame (496 B) + `publicKeySerializeStackX`. -/
abbrev computeMacStackX : Nat := publicKeySerializeStackX + 496

/-- `SignalMessage::verify_mac_with_addresses` frame (288 B) + `computeMacStackX`. -/
abbrev verifyMacWithAddressesStackX : Nat := computeMacStackX + 288

def PublicKeySerializeOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr publicKeySerializeName)
    ((publicKeySerializeSpecX A).inImage img)

/-- `serializeAddressesSpec A parse` at `serializeAddressesStackX`. -/
def serializeAddressesSpecX (A : RustAlloc) (parse : UuidParser) :
    Spec SerializeAddressesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.recipientA⌝ ∗
      protocolAddressAt A x.sender x.senderA ∗ protocolAddressAt A x.recipient x.recipientA ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp serializeAddressesStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protocolAddressAt A x.sender x.senderA ∗ protocolAddressAt A x.recipient x.recipientA ∗
      optSerializeAddressesAt A x.ret (serializeAddresses (serviceIdParse parse) x.sender x.recipient) ∗
      A.pool ∗ stackAt s0.sp serializeAddressesStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def SerializeAddressesOkX (img : Obj.Image) (A : RustAlloc) (parse : UuidParser)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr serializeAddressesName)
    ((serializeAddressesSpecX A parse).inImage img)

/-- `computeMacSpec F A` at `computeMacStackX`. -/
def computeMacSpecX (F : ShaCompress) (A : RustAlloc) : Spec ComputeMacGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.receiverA ∧
      s.readReg64 .x3 = x.keyA ∧ s.readReg64 .x4 = 32#64 ∧ s.readReg64 .x5 = x.msgA ∧
      (s.readReg64 .x6).toNat = x.message.length ∧ x.message.length < 2 ^ 63⌝ ∗
      memRegion x.ret 16 ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool ∗ stackAt s.sp computeMacStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ okTagVec) ∗
      ((x.ret + 8#64) ↦ₛ computeMac F x.sender x.receiver x.macKey x.message) ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool ∗ stackAt s0.sp computeMacStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def ComputeMacOkX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
    ((computeMacSpecX C.F A).inImage img)

/-- `verifyMacWithAddressesSpec img F A parse` at `verifyMacWithAddressesStackX`. -/
def verifyMacWithAddressesSpecX (img : Obj.Image) (F : ShaCompress) (A : RustAlloc)
    (parse : UuidParser) : Spec VerifyMacWithAddressesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.senderAddrA ∧
      s.readReg64 .x2 = x.receiverAddrA ∧ s.readReg64 .x3 = x.senderIkA ∧
      s.readReg64 .x4 = x.receiverIkA ∧ s.readReg64 .x5 = x.keyA ∧
      s.readReg64 .x6 = 32#64 ∧ s.readReg64 .x8 = x.ret⌝ ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      memRegion x.ret 9 ∗
      logOff img ∗
      A.pool ∗ stackAt s.sp verifyMacWithAddressesStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      verifyMacResultAt x.ret
        (x.msg.verifyMacWithAddresses F (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey) ∗
      logOff img ∗
      A.pool ∗ stackAt s0.sp verifyMacWithAddressesStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Relocatable `[LibsignalPlacement]` Specifications and Helpers -/

abbrev lsMacRustAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev lsMacRustDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

abbrev lsMacRustNoAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev lsMacHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

abbrev lsMacMemcpySym : String :=
  "memcpy"

abbrev lsMacMemsetSym : String :=
  "memset"

abbrev lsMacCompress256Sym : String :=
  "_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256"

theorem mac_ls_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) hi hunmut

theorem mac_ls_hook_ok_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((mac_ls_externAt?_of_mem hmem hi hunmut).trans hf) hok

theorem sepWPp_seq_lscl {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

/-- Relocatable `MAX_LOG_LEVEL_FILTER == 0` assertion at `lsLogFilterAddr`. -/
def macLsLogOff [LibsignalPlacement] : SepProp :=
  lsLogFilterAddr ↦₆₄ 0#64

/-- Stack-parameterized relocatable specification of `SignalMessage::verify_mac_with_addresses`
(Block `62`). -/
def verifyMacWithAddressesPlacedSpecWithStack [LibsignalPlacement] (F : ShaCompress) (A : RustAlloc)
    (parse : UuidParser) (totalStack : Nat) : Spec VerifyMacWithAddressesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.senderAddrA ∧
      s.readReg64 .x2 = x.receiverAddrA ∧ s.readReg64 .x3 = x.senderIkA ∧
      s.readReg64 .x4 = x.receiverIkA ∧ s.readReg64 .x5 = x.keyA ∧
      s.readReg64 .x6 = 32#64 ∧ s.readReg64 .x8 = x.ret⌝ ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      memRegion x.ret 9 ∗
      macLsLogOff ∗
      A.pool ∗ stackAt s.sp totalStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ keyToBytes32 x.macKey) ∗
      verifyMacResultAt x.ret
        (x.msg.verifyMacWithAddresses F (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey) ∗
      macLsLogOff ∗
      A.pool ∗ stackAt s0.sp totalStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev verifyMacWithAddressesPlacedSpec [LibsignalPlacement] (F : ShaCompress) (A : RustAlloc)
    (parse : UuidParser) : Spec VerifyMacWithAddressesGhost :=
  verifyMacWithAddressesPlacedSpecWithStack F A parse verifyMacWithAddressesStack

abbrev verifyMacWithAddressesPlacedSpecX [LibsignalPlacement] (F : ShaCompress) (A : RustAlloc)
    (parse : UuidParser) : Spec VerifyMacWithAddressesGhost :=
  verifyMacWithAddressesPlacedSpecWithStack F A parse verifyMacWithAddressesStackX

end CryptoVerification.LibsignalTripleRatchet
