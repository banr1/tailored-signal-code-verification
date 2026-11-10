/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2

/-!
# `find_receiver_chain_key`, `ChainKey::message_keys`, and `ChainKey::next_chain_key` Specifications

Separation-logic contracts for out-of-line calls to `RatchetState::find_receiver_chain_key`
(`0xe8fc`), `ChainKey::message_keys` (`0x126a0`), and `ChainKey::next_chain_key` (`0x12730`),
proved on `sessionProg` and transferred to `tripleRatchetProgAt` via
`ConsumeMessageKeyTransfer.session_subroutine_ok_mono`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Names and stack budgets -/

/-- `RatchetState::find_receiver_chain_key` (image offset `0xe8fc`, 99 instructions). -/
abbrev findReceiverChainKeyName : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key"

/-- `ChainKey::message_keys` (image offset `0x126a0`, 36 instructions). -/
abbrev messageKeysName : String := "<libsignal_protocol::ratchet::keys::ChainKey>::message_keys"

/-- `ChainKey::next_chain_key` (image offset `0x12730`, 29 instructions). -/
abbrev nextChainKeyName : String := "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key"

/-- `find_receiver_chain_key` stack budget: own `0x50`-byte frame (`0xe8fc: sub sp, sp, #0x50`)
plus `find_receiver_chain_index`'s `1024`-byte budget (`findIndexSpec`), rounded up. -/
abbrev findReceiverChainKeyStack : Nat := 2048

/-- `message_keys` stack budget: own `0x50`-byte frame (`0x126a0`) plus `max 2048 allocHookStack`,
rounded up. -/
abbrev messageKeysStack : Nat := 8192

/-- `next_chain_key` stack budget: own `0x50`-byte frame (`0x12730`) plus `hmac_sha256`'s `2048`-byte
budget, rounded up. -/
abbrev nextChainKeyStack : Nat := 4096

/-! ## `find_receiver_chain_key` -/

/-- `Result<Option<ChainKey>, InvalidSessionError>` at `r` (40 bytes). Word 0 is a `u32` tag:
* 0 = `Ok(None)` (`0xe9f4: str wzr, [x19]`), rest unspecified;
* 1 = `Ok(Some ck)`: the 36 bytes `chainKeyBytes ck` at `+4`. Stores: tag and key bytes 0..3 at
  `0xe9a0: stp w13, w12, [x19]`; key bytes at `+8..+0x24` (`0xe9a8..0xe9dc`); index at
  `0xe970: str w8, [x19, #0x24]`.
* 2 = `Err(ISE(s))`: the `&'static str` at `+8`. "missing receiver chain key" is rodata `0x54bf8`,
  26 bytes (`0xea0c..0xea20`).

The fourth arm, ISE "invalid chain key" (rodata `0x54a3e`, 17 bytes, `0xea38`), is reached when
the stored key `Vec` is not 32 bytes long (`ChainKey::from_pb`). `optChainKeyAt` fixes the length
at 32, so that arm is dead and has no case here. Other errors are `False`: the model's only other
outcome is `.panic` at an out-of-range index, which `findIdx?` excludes. -/
def findReceiverChainKeyResultAt (r : BitVec 64) : Except SignalProtocolError (Option ChainKey) → SepProp
  | .ok none => (r ↦₃₂ 0#32) ∗ memRegion (r + 4#64) 36
  | .ok (some ck) => (r ↦₃₂ 1#32) ∗ ((r + 4#64) ↦ₛ chainKeyBytes ck)
  | .error (.invalidSessionStructure .missingReceiverChainKey) =>
    (r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
      strRefAt (r + 8#64) (invalidSessionStructureStr .missingReceiverChainKey) ∗ memRegion (r + 24#64) 16
  | .error _ => ⌜False⌝

/-- Ghost state for `find_receiver_chain_key`. -/
structure FindReceiverChainKeyGhost where
  /-- `self: &RatchetState` (`x0`; try_decrypt passes `&TR.ratchet` = TR + 0). -/
  self : BitVec 64
  G : RatchetGhost
  st : RatchetState
  /-- `their_ephemeral: &PublicKey` (`x1`, 32 bytes; try_decrypt passes message + `0x38`). -/
  theirA : BitVec 64
  their : PublicKey
  /-- The sret (`x8`, 40 bytes). -/
  ret : BitVec 64

/-- Contract for `RatchetState::find_receiver_chain_key(&self = x0, their = x1) -> Result<Option<ChainKey>,
InvalidSessionError>` (sret `x8`): loads `receiver_chains.{ptr, len}` (`0xe910`), calls
`find_receiver_chain_index`, bounds-checks the returned index, and reads chain `i`'s `chain_key`
(`cap` at `+0x48`, `ptr` at `+0x50`, `len` at `+0x58`, `index` at `+0x60`), refining
`RatchetState.findReceiverChainKey`. -/
def findReceiverChainKeySpec (A : RustAlloc) (img : Obj.Image) : Spec FindReceiverChainKeyGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret⌝ ∗
        ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ret 40 ∗
        logOff img ∗ stackAt s.sp findReceiverChainKeyStack
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
        findReceiverChainKeyResultAt x.ret (x.st.findReceiverChainKey x.their) ∗
        logOff img ∗ stackAt s0.sp findReceiverChainKeyStack }
    img

/-! ## `ChainKey::message_keys` -/

/-- `MessageKeyGenerator::Seed((seed, counter))` at `r` (40 bytes): `u32` tag `1` at `+0`, seed
`Vec<u8>` at `+8`, and `u32` counter at `+0x20` (matching the `Ok` arm of
`consumeMessageKeyResultAt`). -/
def mkgAt (A : RustAlloc) (r : BitVec 64) (g : MessageKeyGenerator) : SepProp :=
  (r ↦₃₂ 1#32) ∗ memRegion (r + 4#64) 4 ∗ vecU8 A (r + 8#64) g.seed ∗
    ((r + 32#64) ↦₃₂ g.counter) ∗ memRegion (r + 36#64) 4

/-- Ghost of `message_keys` and `next_chain_key`: `(self, chain key, sret)`. -/
abbrev ChainKeyGhost := BitVec 64 × ChainKey × BitVec 64

/-- Contract for `ChainKey::message_keys(&self = x0) -> MessageKeyGenerator` (sret `x8`): computes
`hmac_sha256(sp, self[0..32], [0x01])` (`0x126d8`), allocates a 32-byte `Vec<u8>` (`0x126ec`), and
writes `Seed { cap = 32, ptr, len = 32, counter = index }`, panicking via `handle_error` (`0x1272c`)
only on allocation failure (refining `ChainKey.messageKeys`). -/
def messageKeysSpec (F : ShaCompress) (A : RustAlloc) (img : Obj.Image) : Spec ChainKeyGhost :=
  Spec.inImage
    { pre := fun (self, ck, ret) s =>
        ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = ret⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 40 ∗ A.pool ∗ stackAt s.sp messageKeysStack
      post := fun (self, ck, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗ mkgAt A ret (ck.messageKeys F) ∗
        A.pool ∗ stackAt s0.sp messageKeysStack
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## `ChainKey::next_chain_key` -/

/-- Contract for `ChainKey::next_chain_key(&self = x0) -> ChainKey` (sret `x8`, 36 bytes): computes
`hmac_sha256(sp + 0xc, self[0..32], [0x02])` (`0x12764`), panics via `panic_const_add_overflow`
(`0x127a0`) iff `index = u32::MAX`, and otherwise writes the derived key and `index + 1` (refining
`ChainKey.nextChainKey`). -/
def nextChainKeySpec (F : ShaCompress) (img : Obj.Image) : Spec ChainKeyGhost :=
  Spec.inImage
    { pre := fun (self, ck, ret) s =>
        ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = ret⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 36 ∗ stackAt s.sp nextChainKeyStack
      post := fun (self, ck, ret) s0 sf =>
        ⌜ck.nextChainKey F ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗
        (match ck.nextChainKey F with
          | .ok ck' => ret ↦ₛ chainKeyBytes ck'
          | .error _ => ⌜False⌝) ∗
        stackAt s0.sp nextChainKeyStack
      onPanic := fun (_, ck, _) s0 sf =>
        ⌜ck.nextChainKey F = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## Subroutine Contract Predicates -/

def FindReceiverChainKeyOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr findReceiverChainKeyName)
    (findReceiverChainKeySpec A img)

/-- findReceiverChainKey meets `findReceiverChainKeySpec` on `tripleRatchetProgAt`. -/
def FindReceiverChainKeyOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  FindReceiverChainKeyOkExt img A (tripleRatchetExterns C ctl abs)

def MessageKeysOkExt (img : Obj.Image) (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName) (messageKeysSpec F A img)

/-- `message_keys` meets `messageKeysSpec` on `tripleRatchetProgAt`. -/
def MessageKeysOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  MessageKeysOkExt img C.F A (tripleRatchetExterns C ctl abs)

def NextChainKeyOkExt (img : Obj.Image) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName) (nextChainKeySpec F img)

/-- `next_chain_key` meets `nextChainKeySpec` on `tripleRatchetProgAt`. -/
def NextChainKeyOk (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  NextChainKeyOkExt img C.F (tripleRatchetExterns C ctl abs)

/-! ## `AllocContractsX` (`extHookStack`) stack budget, spec, and `OkX` predicate for `message_keys` -/

/-- `ChainKey::message_keys` stack budget under `AllocContractsX` (`4096 + extHookStack`). -/
abbrev messageKeysStackX : Nat := 4096 + extHookStack

def messageKeysSpecX (F : ShaCompress) (A : RustAlloc) (img : Obj.Image) : Spec ChainKeyGhost :=
  Spec.inImage
    { pre := fun (self, ck, ret) s =>
        ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = ret⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 40 ∗ A.pool ∗ stackAt s.sp messageKeysStackX
      post := fun (self, ck, ret) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        (self ↦ₛ chainKeyBytes ck) ∗ mkgAt A ret (ck.messageKeys F) ∗
        A.pool ∗ stackAt s0.sp messageKeysStackX
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

def MessageKeysOkX (img : Obj.Image) (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName) (messageKeysSpecX F A img)

end CryptoVerification.LibsignalTripleRatchet
