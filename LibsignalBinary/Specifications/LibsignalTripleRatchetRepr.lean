/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSessionRepr
import all Init.Data.String.Defs
public import LibsignalBinary.Specifications.AsmConstants -- shake: keep

/-!
# Memory layouts of libsignal's session state, messages and results in the compiled image

**Trusted in part.** The theorems of the default library (`Computational/Theorems/` outside
`CliElfLib`) use only `ServiceIdParser`, `UuidParser`, `addrBytes`, `hyphenatedLength`, `kindByte`,
`pniPrefix`, `serviceIdParse`, `tryParseHyphenated`, `utf8`, `uuidTryParse`, `hexNibble`,
`decodeHex`, `decodeHex32`, `parseSimple`, `hyphen`, `parseHyphenated`, `urnPrefix` from this file:
read them. To trust the theorems of `Computational/Theorems/Main.lean` (`CliElfLib`), also read `errTag`.
Everything else here is checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

This file gives the separation-logic predicates that say how the Rust values the triple-ratchet
entry points (`LibsignalBinary/Specifications/LibsignalTripleRatchet.lean`) read and write are laid
out in memory, relating bytes to the session model
(`LibsignalBinary/Specifications/CryptoGames/Ratchet/LibsignalSession.lean`). It extends
`LibsignalBinary/Specifications/LibsignalSessionRepr.lean` (whose predicates it reuses:
`chainAt`, `messageKeyAt`, `optChainKeyAt`, `VecGhost`, `VecPin`, ...). The trusted part is the
pure address-parsing model: `uuidTryParse` (uuid 1.26.1's `Uuid::try_parse`), `serviceIdParse`
(libsignal's `ServiceId::parse_from_service_id_string`) and the per-address bytes `addrBytes`, from
which `serializeAddresses` builds the sender / recipient address bytes.

Every layout fact below was read off the disassembly of the session image; the evidence is cited
by instruction offset at each definition. Independently, a Rust replica of the types (110 `const`
assertions compiled by `rustc` 1.98.1 for `aarch64-unknown-linux-gnu`) confirms every offset, size
and niche, including the fields no instruction touches. The niche choices (`-1` for a single-niche
`Option`, `-2` for `Result<Vec<u8>, SPE>::Ok`, `2^63 + i` for the SPE) depend on the `rustc`
version: rerun the replica on any toolchain bump. Kernel-checked guards: `issStr_lengths`,
`macFailedStr_length`, `pniPrefix_word`.

Glossary: SPE = `SignalProtocolError` (48 bytes); SS = `proto::storage::SessionStructure` (the
payload of `SessionState`, 344 bytes); OTR / TR = `OutgoingTripleRatchet` (200 bytes) /
`TripleRatchet`; IK = identity key; srk = sender ratchet key; pq / SPQR = the Sparse Post-Quantum
Ratchet and its serialized state `Vec<u8>`; ISS = `InvalidSessionStructure`; UUID = universally
unique identifier; ACI = Account Identity; PNI = Phone Number Identity; UTF-8 = 8-bit Unicode
Transformation Format; LE = little-endian; RNG = random number generator; prost = the Rust protobuf
(Protocol Buffers) library; niche = an invalid bit pattern of a field reused as an enum
discriminant; sret = the caller-provided result buffer; `Box<[u8]>` = an owned byte slice `(ptr,
len)` (no capacity word); rodata = the image's read-only data (`↦ᵣ`, duplicable read-only
points-to).

## Niches

* `Option<Vec-like>` (`Option<Chain>`, `Option<chain::ChainKey>`, `Option<PendingPreKey>`,
  `Option<PendingKyberPreKey>`, `spqr::MessageKey`): `None` = capacity word `usize::MAX` (`noneCap`).
  Evidence: `OTR::apply_to_session_state` `0xbd00: cmn x22, #1` (SS + 0x90);
  `clear_unacknowledged_pre_key_message` writes `-1` to SS + 0xf8 and SS + 0x128.
* SPE: word 0 = `2^63 + variant index` for every non-dataful variant (`speWord`).
* `Result<Vec<u8>, SPE>` (try_decrypt): `Ok` = word 0 `-2` (`okTagVec`), the `Vec` at +8; `Err` =
  the SPE inline at +0. `Result<T, SPE>` for `T` = `SignalMessage` / `OutgoingTripleRatchet`: `Ok` =
  the payload at +0; `Err` = word 0 `-1` (`errTag`), the SPE at +8.

## What is not modelled (framed byte-exactly by the ghost)

`alice_base_key`, the registration ids, the pending pre-key's ids / timestamp, the whole
`pending_kyber_pre_key`, and every `Vec` the session model does not determine (`VecGhost`).

## Main definitions

* `uuidTryParse` (with `hexNibble`, `decodeHex`, `decodeHex32`, `parseSimple`, `parseHyphenated`,
  `hyphen`, `urnPrefix`): the model of uuid 1.26.1's `Uuid::try_parse`.
* `serviceIdParse` (with `tryParseHyphenated`, `hyphenatedLength`, `pniPrefix`): the model of
  `ServiceId::parse_from_service_id_string`; `ServiceIdParser` / `UuidParser` are their types.
* `addrBytes`, `kindByte`, `serializeAddresses`: the 36-byte sender / recipient encoding
  (`serialize_addresses`).
* `utf8`: a string literal's UTF-8 bytes.
* `noneCap`, `errTag`, `okTagVec`, `speWord`: the niche / tag words.
* `speAt`, `vecResultAt`, `errResultAt`, `signalMessageResultAt`, `otrResultAt`: an SPE and the `Result`
  buffers of the entry points.
* `signalMessageAt`, `protocolAddressAt`, `sessionStateAt`, `otrAt`: a `SignalMessage`, a
  `ProtocolAddress`, a `SessionStructure` and an `OutgoingTripleRatchet` in memory (with their
  ghost structures).
* `tapeAt`, `tapeAfter`, `coinsOf`, `decryptDraws`: the `HookRng` random tape and how much of it a
  decrypt draws.
* `SessionGhost.AfterTryDecrypt`, `SessionGhost.AgreeExceptPq`, `SessionGhost.AfterOutgoingRatchetApply`: how the ghost
  layout may change across each entry point.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchetRepr

open Arm64 CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-! ## Constants -/

/-- `None` of an `Option<Vec-like>`: the capacity word `usize::MAX` (module docstring). Equal to
`LibsignalSessionRepr.optChainKeyNone`. -/
def noneCap : BitVec 64 := asm64% optionVecNoneWord

/-- The `Err` tag word of `Result<T, SPE>` for the 120 / 200-byte payloads (`-1`; try_from
`0x258a4: str x9, [x19]`, `OTR::from_session_state` `0xb93c`, `OTR::encrypt` `0x34058`). -/
def errTag : BitVec 64 := asm64% resultErrTag

/-- The `Ok` tag word of `Result<Vec<u8>, SPE>` (`-2`; try_decrypt `0x34890: mov x8, #-2;
0x34894: str x8, [x19]`). Why `-2`: SPE's only dataful variant is `SessionNotFound` (index 19, its
`Option<ProtocolAddress>` at +0), whose `address = None` niche is word 0 `-1`; so the `Result`
takes the next niche `-2`, and `speWord 19` never occurs (layout replica). -/
def okTagVec : BitVec 64 := asm64% resultVecOkTag

/-- SPE word 0 of the variant with index `i` (declaration order in `rust/protocol/src/error.rs`). -/
def speWord (i : Nat) : BitVec 64 := asm64% speNicheBase + BitVec.ofNat 64 i

/-- A string literal's UTF-8 bytes. -/
def utf8 (s : String) : List (BitVec 8) := s.toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- The `&'static str` of each `InvalidSessionStructure` reason the session model keeps (rodata
literals: `find_receiver_chain_key` `0x54bf8`, `try_decrypt` `0x57fb8`, `OTR::from` `0x53400` /
`0x5476c`, `TR::from` / `OTR::from` `0x53ce0`). -/
def invalidSessionStructureStr : InvalidSessionReason → List (BitVec 8)
  | .missingSenderChain => utf8 "missing sender chain"
  | .missingReceiverChainKey => utf8 "missing receiver chain key"
  | .missingRemoteIdentity => utf8 "missing remote identity key"
  | .versionTooLarge => utf8 "version does not fit in u8"

/-- Guard (kernel-checked): the lengths the binary stores with the literals. -/
theorem issStr_lengths :
    (invalidSessionStructureStr .missingSenderChain).length = 20 ∧ (invalidSessionStructureStr .missingReceiverChainKey).length = 26 ∧
      (invalidSessionStructureStr .missingRemoteIdentity).length = 27 ∧ (invalidSessionStructureStr .versionTooLarge).length = 26 := by
  decide +kernel

/-- `"MAC verification failed"` (`triple_ratchet.rs:264–269`; try_decrypt allocates 23 bytes and
copies them from rodata `0x57fe8`, `0x34cb4..0x34ce8`). -/
def macFailedStr : List (BitVec 8) := utf8 "MAC verification failed"

/-- Guard (kernel-checked): 23 bytes, and `tooFarInFutureStr` is 36 bytes. -/
theorem macFailedStr_length : macFailedStr.length = 23 ∧ tooFarInFutureStr.length = 36 := by
  decide +kernel

/-! ## Small layouts -/

/-- A `&'static str` at `a` (16 bytes `(ptr, len)`, as `Box<[u8]>`: `into_boxed_slice`
`0x1aff8..0x1b030`, layout replica) whose bytes are the literal `lit`, read-only (rodata). The
address of the literal is existential: `rustc` does not merge equal literals, so specs
do not fix it. -/
def strRefAt (a : BitVec 64) (lit : List (BitVec 8)) : SepProp :=
  ∃∗ p : BitVec 64, (a ↦₆₄ p) ∗ ((a + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 lit.length) ∗
    (p ↦ᵣ lit)

/-- An owned `Box<[u8]>` at `a` (16 bytes `(ptr, len)`) holding `bs`: a live block of exactly
`bs.length` bytes with alignment 1, or, if `bs` is empty, a dangling non-null pointer and no
block (`try_clone_from_ref_in` `0xd0b4: cbz x1` → `0xd0f8: mov w0, #0x1`, no allocation; else
`0xd0c0..0xd0c8: __rust_alloc(len, 1)`; `into_boxed_slice` `0x1aff8..0x1b030`). -/
def boxU8At (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ ptr) ∗ ((a + asm64% boxSliceLenOff) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
    (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))

/-- `Option<Box<[u8]>>` at `a` (16 bytes): `None` is a null pointer (`verify_mac_with_addresses`
`0x1d6f8: ldr x23, [x20, #0x58]; 0x1d700: cbz x23`), the length word unspecified. -/
def optBoxU8At (A : RustAlloc) (a ptr : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ 0#64) ∗
    memRegion (a + asm64% boxSliceLenOff) (asm% (boxSliceSize - boxSliceLenOff))
  | some bs => boxU8At A a ptr bs

/-! ## `SignalProtocolError` (48 bytes) -/

/-- The `String` payload of `InvalidMessage(type, reason)`: the exact literal for
`tooFarInFuture` (`LibsignalSessionRepr.tooFarInFutureStr`) and `macFailed`; any owned bytes for the
`format!` reasons (`pqRatchet`, `badCiphertext`), whose text comes from the abstract `format_inner`
hook. `decryptionFailed` is produced only by `try_decrypt_from_record` (inlined in
`message_decrypt_signal`), not by the five entry points of `Specifications/LibsignalTripleRatchet.lean`. -/
def invalidMessageStrAt (A : RustAlloc) (a : BitVec 64) : InvalidMessageReason → SepProp
  | .tooFarInFuture => vecU8 A a tooFarInFutureStr
  | .macFailed => vecU8 A a macFailedStr
  | .pqRatchet => ∃∗ bs : List (BitVec 8), vecU8 A a bs
  | .badCiphertext => ∃∗ bs : List (BitVec 8), vecU8 A a bs
  | .decryptionFailed => ⌜False⌝

/-- **An SPE at `a` (48 bytes)** holding the session model's error `e`. `fnName` is the
`&'static str` of `InvalidState(fnName, String)` (`"decrypt"` in try_decrypt `0x34d3c`, `"encrypt"`
in `OTR::encrypt` `0x34040`). Payload bytes past the variant's fields are `memRegion`. For the
byte-payload variants (`badKeyType`, `legacyCiphertextVersion` / `unrecognized…`) the binary writes
more than the byte at +8 (a zero-extended `u64`, or the byte plus junk); `speAt` pins the byte and
leaves the rest `memRegion`, which is weaker and compatible.

| Variant | Word 0 | Payload |
| --- | --- | --- |
| `invalidState` | `speWord 1` | `String` @+8 (any bytes, from `format_inner`), `&str fnName` @+0x20 |
| `ciphertextMessageTooShort n` | `speWord 3` | `usize` @+8 (try_from `0x258a0`) |
| `legacyCiphertextVersion v` / `unrecognized…` | `speWord 4` / `5` | `u8` @+8 (`0x258e0`) |
| `invalidProtobufEncoding` | `speWord 2` | none (`0x25ca4`) |
| `noKeyTypeIdentifier` | `speWord 7` | none (`0x25e9c`) |
| `badKeyType t` | `speWord 8` | `u8` @+8 (`0x25e9c`) |
| `badKeyLength n` | `speWord 9` | `usize` @+8 (`0x25e9c`) |
| `invalidKeyAgreement` | `speWord 10` | none (`create_chain` `0x14eac`) |
| `invalidSessionStructure r` | `speWord 20` | `&str` @+8 = `invalidSessionStructureStr r` (`0xb934` …) |
| `duplicatedMessage i c` | `speWord 23` | `u32` @+8, `u32` @+12 |
| `invalidMessage t r` | `speWord 24` | `String` @+8, type byte @+0x20 |
| `panic` | – | `False` (a panic never returns) | -/
def speAt (A : RustAlloc) (fnName : List (BitVec 8)) (a : BitVec 64) :
    SignalProtocolError → SepProp
  | .invalidState =>
    (a ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (a + asm64% spePayloadOff) bs) ∗
      strRefAt (a + asm64% speInvalidStateFnOff) fnName
  | .ciphertextMessageTooShort n =>
    (a ↦₆₄ speWord 3) ∗ ((a + asm64% spePayloadOff) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (a + asm64% (spePayloadOff + 8)) (asm% (speSize - (spePayloadOff + 8)))
  | .legacyCiphertextVersion v =>
    (a ↦₆₄ speWord 4) ∗ ((a + asm64% spePayloadOff) ↦₈ v) ∗
      memRegion (a + asm64% (spePayloadOff + 1)) (asm% (speSize - (spePayloadOff + 1)))
  | .unrecognizedCiphertextVersion v =>
    (a ↦₆₄ speWord 5) ∗ ((a + asm64% spePayloadOff) ↦₈ v) ∗
      memRegion (a + asm64% (spePayloadOff + 1)) (asm% (speSize - (spePayloadOff + 1)))
  | .invalidProtobufEncoding =>
    (a ↦₆₄ speWord 2) ∗ memRegion (a + asm64% spePayloadOff) (asm% (speSize - spePayloadOff))
  | .noKeyTypeIdentifier =>
    (a ↦₆₄ speWord 7) ∗ memRegion (a + asm64% spePayloadOff) (asm% (speSize - spePayloadOff))
  | .badKeyType t =>
    (a ↦₆₄ speWord 8) ∗ ((a + asm64% spePayloadOff) ↦₈ t) ∗
      memRegion (a + asm64% (spePayloadOff + 1)) (asm% (speSize - (spePayloadOff + 1)))
  | .badKeyLength n =>
    (a ↦₆₄ speWord 9) ∗ ((a + asm64% spePayloadOff) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (a + asm64% (spePayloadOff + 8)) (asm% (speSize - (spePayloadOff + 8)))
  | .invalidKeyAgreement =>
    (a ↦₆₄ speWord 10) ∗ memRegion (a + asm64% spePayloadOff) (asm% (speSize - spePayloadOff))
  | .invalidSessionStructure r =>
    (a ↦₆₄ speWord 20) ∗ strRefAt (a + asm64% spePayloadOff) (invalidSessionStructureStr r) ∗
      memRegion (a + asm64% (spePayloadOff + boxSliceSize))
        (asm% (speSize - (spePayloadOff + boxSliceSize)))
  | .duplicatedMessage i c =>
    (a ↦₆₄ speWord 23) ∗ ((a + asm64% spePayloadOff) ↦₃₂ i) ∗
      ((a + asm64% speDupCounterOff) ↦₃₂ c) ∗
      memRegion (a + asm64% (speDupCounterOff + 4)) (asm% (speSize - (speDupCounterOff + 4)))
  | .invalidMessage t r =>
    (a ↦₆₄ speWord 24) ∗ invalidMessageStrAt A (a + asm64% spePayloadOff) r ∗
      ((a + asm64% speInvalidMessageTypeOff) ↦₈ msgTypeByte t) ∗
      memRegion (a + asm64% (speInvalidMessageTypeOff + 1))
        (asm% (speSize - (speInvalidMessageTypeOff + 1)))
  | .panic => ⌜False⌝

/-! ## Results -/

/-- `Result<Vec<u8>, SPE>` at `r` (48 bytes, try_decrypt's sret): `Ok` = `okTagVec`, an owned
`Vec<u8>` at +8 (try_decrypt `0x34870..0x34894`), 16 bytes unspecified; `Err` = the SPE inline. -/
def vecResultAt (A : RustAlloc) (r : BitVec 64) : Except SignalProtocolError (List (BitVec 8)) → SepProp
  | .ok pt =>
    (r ↦₆₄ okTagVec) ∗ vecU8 A (r + asm64% decResultVecOff) pt ∗
      memRegion (r + asm64% (decResultVecOff + vecSize)) (asm% (speSize - (decResultVecOff + vecSize)))
  | .error e => speAt A (utf8 "decrypt") r e

/-- The `Err` arm of `Result<T, SPE>` at `r` for a `size`-byte result: `errTag`, the SPE at +8,
the rest unspecified. -/
def errResultAt (A : RustAlloc) (fnName : List (BitVec 8)) (size : Nat) (r : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (r ↦₆₄ errTag) ∗ speAt A fnName (r + asm64% resultErrSpeOff) e ∗
    memRegion (r + asm64% (resultErrSpeOff + speSize)) (size - asm% (resultErrSpeOff + speSize))

/-! ## `SignalMessage` (120 bytes) -/

/-- The ghost of a `SignalMessage` in memory: the `Vec` / `Box` pointers the model does not
determine. -/
structure SignalMessageGhost where
  pqCap : BitVec 64
  pqPtr : BitVec 64
  ctPtr : BitVec 64
  serPtr : BitVec 64
  addrPtr : BitVec 64

/-- **A `SignalMessage` at `a` (120 bytes)** holding the session model's message `m`:
`pq_ratchet: Vec<u8>` @0 (its capacity is the `Result` niche), `ciphertext: Box<[u8]>` @0x18,
`serialized: Box<[u8]>` @0x28, `sender_ratchet_key` (32 bytes) @0x38, `addresses:
Option<Box<[u8]>>` @0x58, `counter` @0x68, `previous_counter` @0x6c, `message_version: u8` @0x70,
7 bytes padding. Size bounds: `serialized` has at least `macLength + 1 = 9` bytes (`try_from` /
`new`; `verify_mac` `0x1d5cc: subs x23, x8, #8; b.lo` relies on it) and fewer than `2^40`; the
other byte strings are shorter than `2^40` (no length arithmetic of the call graph overflows). -/
def signalMessageAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64) (m : SignalMessage) :
    SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + asm64% smCiphertextOff) g.ctPtr m.ciphertext ∗
    boxU8At A (a + asm64% smSerializedOff) g.serPtr m.serialized ∗
    ((a + asm64% smSenderRatchetKeyOff) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + asm64% smAddressesOff) g.addrPtr m.addresses ∗
    ((a + asm64% smCounterOff) ↦₃₂ m.counter) ∗
    ((a + asm64% smPreviousCounterOff) ↦₃₂ m.previousCounter) ∗
    ((a + asm64% smMessageVersionOff) ↦₈ m.messageVersion) ∗
    memRegion (a + asm64% (smMessageVersionOff + 1))
      (asm% (signalMessageSize - (smMessageVersionOff + 1)))

/-- `Result<SignalMessage, SPE>` at `r` (120 bytes; try_from, `OTR::encrypt`): `Ok` = a fresh
owned message at `r`; `Err` = `errResultAt`. -/
def signalMessageResultAt (A : RustAlloc) (fnName : List (BitVec 8)) (r : BitVec 64) :
    Except SignalProtocolError SignalMessage → SepProp
  | .ok m => ∃∗ g : SignalMessageGhost, signalMessageAt A g r m
  | .error e => errResultAt A fnName (asm% signalMessageResultSize) r e

/-! ## `ProtocolAddress` and `serialize_addresses` -/

/-- The ghost of a `ProtocolAddress { name: String, device_id: DeviceId }`: the name's `Vec`,
exactly, and the device byte. -/
structure AddrGhost where
  name : VecGhost
  device : BitVec 8

/-- A `ProtocolAddress` at `a` (32 bytes): `name` @0, `device_id` byte @0x18 (raw byte; the
binary reads it unchecked), 7 bytes padding. -/
def protocolAddressAt (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  vecGhostAt A g.name a ∗ ((a + asm64% addrDeviceOff) ↦₈ g.device) ∗
    memRegion (a + asm64% (addrDeviceOff + 1)) (asm% (protocolAddressSize - (addrDeviceOff + 1)))

/-- A `ServiceId` parser on name bytes: the `ServiceId` of a name, or `none`. The `Bool` is the kind
(`false` = `Aci`, tag 0; `true` = `Pni`, tag 1), the vector the UUID. The session specs use
`serviceIdParse uuidParse` (below), the model of `ServiceId::parse_from_service_id_string`. -/
abbrev ServiceIdParser := List (BitVec 8) → Option (Bool × List.Vector (BitVec 8) 16)

/-- A `uuid::Uuid::try_parse` on the input bytes: the 16 UUID bytes (`Ok`), or `none` (`Err`). The
session specs are generic in it; the statement instantiates them at `uuidTryParse`. -/
abbrev UuidParser := List (BitVec 8) → Option (List.Vector (BitVec 8) 16)

/-! ### `uuid::Uuid::try_parse` (uuid 1.26.1)

Upstream: `~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.26.1/src/parser.rs`.
`Uuid::try_parse(&str)` (`:110–112`) = `try_parse_ascii(input.as_bytes())` (`:136–144`), which maps
`try_parse` (`:147–163`) to `Ok(Uuid::from_bytes(bytes))` (the 16 bytes, unchanged) or to
`Err(Error(ErrorKind::ParseOther))` on every failure. `try_parse` dispatches on the length:
* 32 bytes: `parse_simple` (`:188–225`), 32 hex digits;
* 36 bytes: `parse_hyphenated` (`:228–278`), the whole input;
* 38 bytes `{…}`: `parse_hyphenated` of the 36 bytes inside the braces (`:156`);
* 45 bytes `urn:uuid:…`: `parse_hyphenated` of the 36 bytes after the prefix (`:157`);
* any other length or shape: `Err` (`:161`).
`decode_hex32` (`:283–322`) maps `'0'..='9'` to `0..9` and `'a'..='f'` / `'A'..='F'` (via `| 0x20`)
to `10..15`, and rejects every other byte; byte `j` of the UUID is `(nibble 2j << 4) | nibble 2j+1`.

libsignal only reaches the 36-byte (hyphenated) path: `try_parse_hyphenated`
(`core/src/address.rs:264–271`, `tryParseHyphenated` below) checks the length is
`hyphenatedLength = 36` before it calls `Uuid::try_parse`. The other shapes are modelled so that
`uuidTryParse` is the whole function, as compiled into the image. -/

/-- `decode_hex32`'s per-byte map (`src/parser.rs:289–305`): `digit = c - '0'` if `< 10`, else
`alpha = (c | 0x20) - 'a'` if `< 6`, as `alpha + 10`; any other byte is bad (`none`). -/
def hexNibble (c : BitVec 8) : Option (BitVec 8) :=
  if c - 0x30#8 < 10#8 then some (c - 0x30#8)
  else if (c ||| 0x20#8) - 0x61#8 < 6#8 then some ((c ||| 0x20#8) - 0x61#8 + 10#8)
  else none

/-- `decode_hex32`'s byte assembly (`src/parser.rs:310–321`) on a list of hex digits: each pair
`(hi, lo)` gives `(hi << 4) | lo`; `none` if any digit is bad. -/
def decodeHex : List (BitVec 8) → Option (List (BitVec 8))
  | hi :: lo :: rest => do
    let h ← hexNibble hi
    let l ← hexNibble lo
    let r ← decodeHex rest
    return ((h <<< 4) ||| l) :: r
  | _ => some []

/-- `decode_hex32(hex: &[u8; 32])` (`src/parser.rs:283–322`): the 16 bytes, or `none`. -/
def decodeHex32 (hex : List (BitVec 8)) : Option (List.Vector (BitVec 8) 16) :=
  (decodeHex hex).bind fun bs => if h : bs.length = 16 then some ⟨bs, h⟩ else none

/-- `parse_simple(s, _)` (`src/parser.rs:188–225`): 32 hex digits. -/
def parseSimple (s : List (BitVec 8)) : Option (List.Vector (BitVec 8) 16) :=
  if s.length = 32 then decodeHex32 s else none

/-- The byte `'-'`. -/
def hyphen : BitVec 8 := 0x2d#8

/-- `parse_hyphenated(s)` (`src/parser.rs:228–278`): 36 bytes, `'-'` at positions 8, 13, 18 and 23
(`:244–247`), the other 32 bytes hex digits, gathered in order (`:251–272`). -/
def parseHyphenated (s : List (BitVec 8)) : Option (List.Vector (BitVec 8) 16) :=
  if s.length = 36 ∧ s[8]? = some hyphen ∧ s[13]? = some hyphen ∧ s[18]? = some hyphen ∧
      s[23]? = some hyphen then
    decodeHex32 (s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++
      s.drop 24)
  else none

/-- The prefix `urn:uuid:` (`src/parser.rs:157`). -/
def urnPrefix : List (BitVec 8) := utf8 "urn:uuid:"

/-- **`uuid::Uuid::try_parse`** (uuid 1.26.1, `src/parser.rs:110–112, 136–163`; the shapes are
listed above): `some u` = `Ok(Uuid::from_bytes(u))`, `none` = `Err(ParseOther)`. -/
def uuidTryParse : UuidParser := fun input =>
  if input.length = 32 then parseSimple input
  else if input.length = 36 then parseHyphenated input
  else if input.length = 38 ∧ input.head? = some 0x7b#8 ∧ input.getLast? = some 0x7d#8 then
    parseHyphenated ((input.drop 1).take 36)
  else if input.length = 45 ∧ urnPrefix.isPrefixOf input then
    parseHyphenated (input.drop urnPrefix.length)
  else none

/-- The 16 bytes of a UUID given as hex digits (for the guards below). -/
private def uuidOf (l : List Nat) : Option (List.Vector (BitVec 8) 16) :=
  let bs := l.map (BitVec.ofNat 8)
  if h : bs.length = 16 then some ⟨bs, h⟩ else none

/-- The prefix `"PNI:"` of a PNI's string form (`core/src/address.rs:273`). -/
def pniPrefix : List (BitVec 8) := utf8 "PNI:"

/-- Guard (kernel-checked): `pniPrefix` is the 4 bytes whose little-endian word the compiled
`parse_from_service_id_string` compares the input's first word with (`+0x18: ldr w9, [x0]`;
`+0x1c..+0x20: mov w10, #0x4e50; movk w10, #0x3a49, lsl #16`; `+0x24: cmp w9, w10`). -/
theorem pniPrefix_word : pniPrefix = [0x50#8, 0x4e#8, 0x49#8, 0x3a#8] := by
  decide +kernel

/-- `uuid::fmt::Hyphenated::LENGTH` (uuid 1.26.1, `src/fmt.rs:366`). -/
def hyphenatedLength : Nat := 36

/-- `try_parse_hyphenated` (`core/src/address.rs:264–271`): `Uuid::try_parse(input).ok()` if the
input has exactly `hyphenatedLength` bytes, else `None` without calling it. -/
def tryParseHyphenated (uuidParse : UuidParser) (input : List (BitVec 8)) :
    Option (List.Vector (BitVec 8) 16) :=
  if input.length = hyphenatedLength then uuidParse input else none

/-- **`ServiceId::parse_from_service_id_string` (`core/src/address.rs:263–280`)** over a
`Uuid::try_parse`: if the input starts with `"PNI:"` (`input.strip_prefix("PNI:")`, a byte-prefix
test), the PNI of the rest; otherwise the ACI of the whole input; each `None` unless the parsed part
has exactly 36 bytes and `uuidParse` accepts it. In the image this and `Uuid::try_parse` are
in-image code (`libsignal-core` and `uuid` are whole crates), verified against
`serviceIdParse uuidTryParse`. -/
def serviceIdParse (uuidParse : UuidParser) : ServiceIdParser := fun input =>
  if pniPrefix.isPrefixOf input then
    (tryParseHyphenated uuidParse (input.drop pniPrefix.length)).map fun u => (true, u)
  else
    (tryParseHyphenated uuidParse input).map fun u => (false, u)

/-- `ServiceIdKind`'s byte: the tag of the 17-byte `Option<ServiceId>` that the in-image
`parse_from_service_id_string` writes (`Aci` = 0, `+0x50: strb wzr, [x19]`; `Pni` = 1,
`+0xb4..+0xb8: mov w8, #1; strb w8, [x19]`; `None` = 2, `+0x98..+0x9c`), stored unchanged by
`serialize_addresses` (`core/src/address.rs`'s `ServiceIdKind` order). -/
def kindByte (pni : Bool) : BitVec 8 := if pni then 1#8 else 0#8

/-- The 18 bytes `kind ‖ uuid ‖ device` of one address
(`ServiceId::service_id_fixed_width_binary`, `core/src/address.rs:212–216`, then the device). -/
def addrBytes (sid : Bool × List.Vector (BitVec 8) 16) (device : BitVec 8) : List (BitVec 8) :=
  kindByte sid.1 :: (sid.2.toList ++ [device])

/-- `serialize_addresses(sender, recipient)` (`protocol.rs:237–252`; binary `0x1d4b0`):
the 36 bytes of the sender then the recipient, or `none` if either name does not parse. -/
def serializeAddresses (parse : ServiceIdParser) (sender recipient : AddrGhost) :
    Option (List (BitVec 8)) := do
  let s ← parse sender.name.bytes
  let r ← parse recipient.name.bytes
  return addrBytes s sender.device ++ addrBytes r recipient.device

/-! ## The random tape (`HookRng`) -/

/-- The tape control block at `ctl` (16 bytes: cursor, remaining count) and the remaining bytes
`rest` at the cursor `cur`. `libsignal_session_rng_fill` (the `rngFillHook` of the spec) reads and
advances it. A harness convention shared with `rngFillHook`, not a compiled layout. -/
def tapeAt (ctl cur : BitVec 64) (rest : List (BitVec 8)) : SepProp :=
  ⌜rest.length < 2 ^ 63⌝ ∗ (ctl ↦₆₄ cur) ∗ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
    (cur ↦ₛ rest)

/-- The tape after `k` bytes were drawn: cursor `cur + k`, the remaining bytes `rest.drop k`; the
drawn bytes stay owned (read-only for the program). -/
def tapeAfter (ctl cur : BitVec 64) (rest : List (BitVec 8)) (k : Nat) : SepProp :=
  (ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗
    ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 (rest.length - k)) ∗ (cur ↦ₛ rest)

/-- The decrypt coins: the first 32 tape bytes, zero-padded (what `rngFillHook` writes for a
32-byte request), as the `BitVec 256` of their LE bytes (`KeyPair.generate` takes
`keyToBytesVec32 coins = ` these bytes: `keyToBytes32_bytesToKey32` gives back exactly the 32 tape
bytes). A hook convention, not a compiled layout. -/
def coinsOf (rest : List (BitVec 8)) : BitVec 256 :=
  bytesToKey32 ((rest ++ List.replicate 32 0#8).take 32)

/-- Whether `try_decrypt_with_state` reaches `KeyPair::generate` (the only `rng_fill` call of the
decrypt call graph, try_decrypt `0x34b18`): the TR builds, no receiver chain for `their`, a sender
chain exists and the receiving half-step `create_chain` succeeds. -/
def drawsCoins {PQ : Type} (C : Crypto) (st : SessionState PQ) (their : PublicKey) : Bool :=
  st.remoteIdentity.isSome &&
    match RatchetState.findReceiverChainKey
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
        their with
    | .ok none =>
      match st.senderChain with
      | some sc =>
        match rootCreateChain C st.rootKey their sc.ratchetKey.privateKey with
        | .ok _ => true
        | .error _ => false
      | none => false
    | _ => false

/-- The number of tape bytes a decrypt draws: `min 32 rest.length` if `drawsCoins`, else 0. -/
def decryptDraws {PQ : Type} (C : Crypto) (st : SessionState PQ) (their : PublicKey)
    (rest : List (BitVec 8)) : Nat :=
  if drawsCoins C st their then min 32 rest.length else 0

/-! ## `SessionStructure` (344 bytes) -/

/-- The ghost of the `Some` sender chain at SS + 0x90 (a `session_structure::Chain`): the two key
`Vec`s exactly, the (empty) `message_keys` buffer and the chain-key pin. -/
structure SenderChainGhost where
  srk : VecGhost
  priv : VecGhost
  mkCap : BitVec 64
  mkPtr : BitVec 64
  ck : VecPin

/-- `sender_chain: Option<Chain>` at `a` (104 bytes) holding the model's `Option<SenderChain>`.
`None` = `noneCap` (`OTR::apply` `0xbd00`). `Some`: `sender_ratchet_key` deserializes to the
public key (`PublicKey::deserialize`, via the in-image `try_from`) and is exactly 33 bytes, the
canonical `PublicKey::serialize` that upstream stores (`set_sender_chain`,
`state/session.rs:373–381`; upstream's reader also accepts trailing bytes, such records are
outside the specs); `sender_ratchet_key_private` is exactly the 32 private-key bytes, **stored
clamped** (`PrivateKey::deserialize` clamps, `core/curve/curve25519.rs:170–175`, so only clamped
bytes round trip; upstream always stores clamped keys); `message_keys` empty (a sender chain never
stores skipped keys); `chain_key` present (else `"missing sender chain key"`, which the model does
not have). -/
def optSenderChainAt (A : RustAlloc) (a : BitVec 64) :
    Option SenderChainGhost → Option SenderChain → SepProp
  | none, none => (a ↦₆₄ noneCap) ∗ memRegion (a + asm64% vecPtrOff) (asm% (chainSize - vecPtrOff))
  | some g, some sc =>
    ⌜PublicKey.deserialize g.srk.bytes = .ok sc.ratchetKey.publicKey ∧
      g.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
      g.srk.bytes.length = 33⌝ ∗
      vecGhostAt A g.srk a ∗ vecGhostAt A g.priv (a + asm64% chainPrivOff) ∗
      vecAt A (asm% messageKeySize) (asm% messageKeyAlign) (messageKeyAt A)
        (a + asm64% chainMessageKeysOff) g.mkCap g.mkPtr [] ∗
      optChainKeyAt A g.ck (some sc.chainKey) (a + asm64% chainChainKeyOff)
  | _, _ => ⌜False⌝

/-- An unmodelled `Option<{ Vec<u8>, tail }>` (prost's `PendingPreKey`, 48 bytes, `base_key` first;
`PendingKyberPreKey`, 32 bytes, `ciphertext` first): the `Vec` exactly and the `tail` bytes. -/
structure TailVecGhost where
  vec : VecGhost
  tail : List (BitVec 8)

/-- `Option<{ Vec<u8>, tail }>` at `a` (`size` bytes): `None` = `noneCap` (`clear_unacknowledged_
pre_key_message` writes it), the rest unspecified; `Some` = the `Vec` and the exact tail. -/
def optTailVecAt (A : RustAlloc) (size : Nat) (a : BitVec 64) : Option TailVecGhost → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + asm64% vecPtrOff) (size - asm% vecPtrOff)
  | some g =>
    ⌜g.tail.length = size - asm% vecSize⌝ ∗ vecGhostAt A g.vec a ∗ ((a + asm64% vecSize) ↦ₛ g.tail)

/-- The ghost layout of a `SessionStructure`: every `Vec` the model does not determine, the pins of
those it does, and the unmodelled fields. -/
structure SessionGhost where
  /-- `local_identity_public` (serialized IK (identity key), exactly 33 bytes). -/
  localIk : VecGhost
  /-- `remote_identity_public` (empty = no remote identity, else exactly 33 bytes). -/
  remoteIk : VecGhost
  /-- `root_key`'s `Vec` (exactly the 32 key bytes). -/
  root : VecPin
  /-- `receiver_chains`: buffer and per-chain ghosts (`LibsignalSessionRepr.ChainGhost`). -/
  chainsCap : BitVec 64
  chainsPtr : BitVec 64
  chains : List ChainGhost
  /-- `alice_base_key` (unmodelled). -/
  alice : VecGhost
  /-- `pq_ratchet_state`'s `Vec` (bytes = the model's `pqRatchetState`). -/
  pq : VecPin
  sender : Option SenderChainGhost
  /-- `pending_pre_key` (only `is_some()` is modelled). -/
  pending : Option TailVecGhost
  /-- `pending_kyber_pre_key` (unmodelled). -/
  kyber : Option TailVecGhost
  /-- `remote_registration_id`, `local_registration_id` (8 bytes, unmodelled). -/
  regIds : List (BitVec 8)

/-- **`SessionStructure` at `ss` (344 bytes)** holding the session model's state `st` with ghost
layout `G`: `local_identity_public` @0 (deserializes to `st.localIdentity`),
`remote_identity_public` @0x18 (empty ⇔ `none`, else deserializes; `remote_identity_key`
`strh wzr` on empty), `root_key` @0x30 (the 32 key bytes, else `"invalid root key"`),
`receiver_chains` @0x48 (`LibsignalSessionRepr.chainAt`, element 104 bytes, align 8),
`alice_base_key` @0x60, `pq_ratchet_state` @0x78, `sender_chain` @0x90, `pending_pre_key` @0xf8
(`is_some()` ⇔ `st.pendingPreKey`), `pending_kyber_pre_key` @0x128, `session_version` @0x148,
`previous_counter` @0x14c, the registration ids @0x150. No instruction of the call graph touches
`alice_base_key`, the registration ids (remote @0x150, local @0x154) or the pending pre-keys' tails
(`PendingPreKey`: `pre_key_id` +0x18, `timestamp` +0x20, `signed_pre_key_id` +0x28;
`PendingKyberPreKey`: `pre_key_id` +0x18): their offsets follow by elimination and are confirmed by
the layout replica.

**Well-formed records only**: the predicate requires the identity keys, the root
key and the sender chain's keys to decode. Upstream reaches errors the session model lacks on records
that do not (`"invalid root key"`, undecodable local / remote IK, undecodable sender ratchet key or
a private key ≠ 32 bytes, `"missing sender chain key"`), and silently clamps an unclamped stored
private key; such records are outside the specs.

**Canonical stored keys**: the stored public keys are exactly the 33-byte canonical
`PublicKey::serialize` that upstream writes (`SessionState::new`, `state/session.rs:157–158`, and
`add_receiver_chain` / `set_sender_chain` for the chains, see `chainAt` / `optSenderChainAt`):
`local_identity_public`, `remote_identity_public` when present, every chain's
`sender_ratchet_key`; receiver chains store no private key. Upstream's reader accepts more
(trailing bytes after a key); such records are outside the specs. -/
def sessionStateAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
    vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + asm64% ssRemoteIdentityOff) ∗
    vecU8At A (ss + asm64% ssRootKeyOff) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (ss + asm64% ssReceiverChainsOff)
      G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + asm64% ssAliceBaseKeyOff) ∗
    vecU8At A (ss + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + asm64% ssSenderChainOff) G.sender st.senderChain ∗
    optTailVecAt A (asm% pendingPreKeySize) (ss + asm64% ssPendingPreKeyOff) G.pending ∗
    optTailVecAt A (asm% pendingKyberPreKeySize) (ss + asm64% ssPendingKyberPreKeyOff) G.kyber ∗
    ((ss + asm64% ssSessionVersionOff) ↦₃₂ st.sessionVersion) ∗
    ((ss + asm64% ssPreviousCounterOff) ↦₃₂ st.previousCounter) ∗
    ((ss + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)

/-! ## Ghost relations -/

/-- The fields no session-program entry point writes: both identity keys, `alice_base_key`, the
registration ids. -/
def SessionGhost.Keeps (G G' : SessionGhost) : Prop :=
  G'.localIk = G.localIk ∧ G'.remoteIk = G.remoteIk ∧ G'.alice = G.alice ∧ G'.regIds = G.regIds

/-- The ghost after `try_decrypt_with_state`. `Ok`: both pending pre-keys cleared
(`clear_unacknowledged_pre_key_message`); every other `Vec` may be new (`TR::apply` reallocates the
root key, the sender chain and moves in the receiver chains and the pq state). `Err`: the pending
pre-keys, the root key `Vec` and the sender chain are untouched (`TR::from` only copies them; it
`mem::take`s the receiver chains and the pq state, whose new pins are free). -/
def SessionGhost.AfterTryDecrypt (ok : Bool) (G G' : SessionGhost) : Prop :=
  G.Keeps G' ∧
    if ok then G'.pending = none ∧ G'.kyber = none
    else G'.pending = G.pending ∧ G'.kyber = G.kyber ∧ G'.root = G.root ∧ G'.sender = G.sender

/-! ## `OutgoingTripleRatchet` (200 bytes) -/

/-- **An `OutgoingTripleRatchet` at `o` (200 bytes)** holding the session model's value `ot`, its
pq `Vec` at `(pqCap, pqPtr)`: `pqr_state` @0, `sender_ratchet_key` public @0x18 and private
@0x38 (clamped by `from_session_state`), `local_identity_key` @0x58, `remote_identity_key` @0x78,
`sender_chain_key` (key @0x98, index @0xb8), `previous_counter` @0xbc, `session_version: u8`
@0xc0, 7 bytes padding. -/
def otrAt (A : RustAlloc) (o pqCap pqPtr : BitVec 64) (ot : OutgoingTripleRatchet (List (BitVec 8))) :
    SepProp :=
  vecU8At A o pqCap pqPtr ot.pqrState ∗
    ((o + asm64% otrSenderRatchetPubOff) ↦ₛ ot.senderRatchetKey.publicKey.bytes.toList) ∗
    ((o + asm64% otrSenderRatchetPrivOff) ↦ₛ ot.senderRatchetKey.privateKey.bytes.toList) ∗
    ((o + asm64% otrLocalIdentityOff) ↦ₛ ot.localIdentityKey.publicKey.bytes.toList) ∗
    ((o + asm64% otrRemoteIdentityOff) ↦ₛ ot.remoteIdentityKey.publicKey.bytes.toList) ∗
    ((o + asm64% otrSenderChainKeyOff) ↦ₛ chainKeyBytes ot.senderChainKey) ∗
    ((o + asm64% otrPreviousCounterOff) ↦₃₂ ot.previousCounter) ∗
    ((o + asm64% otrSessionVersionOff) ↦₈ ot.sessionVersion) ∗
    memRegion (o + asm64% (otrSessionVersionOff + 1)) (asm% (otrSize - (otrSessionVersionOff + 1)))

/-- `Result<OutgoingTripleRatchet, SPE>` at `r` (200 bytes): `Ok` = the OTR at `r` with its pq
`Vec` at the given pin; `Err` = `errResultAt` (no `InvalidState` is produced, so `fnName` is
irrelevant: `""`). -/
def otrResultAt (A : RustAlloc) (r : BitVec 64) (pq : VecPin) :
    Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8))) → SepProp
  | .ok ot => otrAt A r pq.cap pq.ptr ot
  | .error e => errResultAt A [] (asm% otrResultSize) r e

end CryptoVerification.LibsignalTripleRatchetRepr
