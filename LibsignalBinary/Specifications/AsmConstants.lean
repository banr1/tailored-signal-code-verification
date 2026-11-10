/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Reduce
public import Lean.Exception

/-!
# Binary-Dependent Layout Constants

**Checked by Lean.** Binary-dependent type sizes, field offsets, niche values, `hashbrown` and
vtable parameters, and the `asm%` / `asm64%` / `asm8%` compile-time elaborators consumed by
`LibsignalSessionRepr.lean` and `LibsignalTripleRatchetRepr.lean`.

Each constant is written `abbrev NAME : Nat := VALUE` on a single line and checked against
`rustc` 1.98.1 (`aarch64-unknown-linux-gnu`) const-eval in section `(a)` or an AArch64 runtime
harness in section `(b)` (`third_party/libsignal/libsignal-session/tools/layout-replica/`).
Section `(c)` fixes harness stack conventions. The `asm%`, `asm64%`, and `asm8%` elaborators
reduce closed `Nat` expressions over `AsmConstants` to inline `Nat`, `BitVec 64`, and `BitVec 8`
numerals at elaboration time.
-/

@[expose] public section

namespace AsmConstants

/-! ## (a) Rust type layout (rustc 1.98.1, `aarch64-unknown-linux-gnu`)

Checked by rustc const-eval (each constant against `size_of` / `offset_of!` / a niche word
of the real vendored type, or of the layout replica for private
fields, whose size is tied to the real type's). The check reads the lines of this section. -/

/-! ### `std` containers -/

/-- `Vec<u8>` / `String`: the capacity word (`RawVec`'s `cap`; carries the `Option` niche). -/
abbrev vecCapOff : Nat := 0
/-- `Vec<u8>` / `String`: the data pointer word. -/
abbrev vecPtrOff : Nat := 8
/-- `Vec<u8>` / `String`: the length word. -/
abbrev vecLenOff : Nat := 16
/-- `size_of::<Vec<u8>>()` = `size_of::<String>()` (also `RawVec<T>::grow_one`'s 24-byte `T`). -/
abbrev vecSize : Nat := 24
/-- `align_of::<Vec<u8>>()` = `align_of::<String>()`. -/
abbrev vecAlign : Nat := 8
/-- `Box<[u8]>` / `&[u8]` / `&str` (a fat pointer): the data pointer word. -/
abbrev boxSlicePtrOff : Nat := 0
/-- `Box<[u8]>` / `&[u8]` / `&str` (a fat pointer): the length word. -/
abbrev boxSliceLenOff : Nat := 8
/-- `size_of::<Box<[u8]>>()` = `size_of::<&str>()`. -/
abbrev boxSliceSize : Nat := 16
/-- `size_of::<std::time::SystemTime>()` (`session_message_encrypt`'s stack argument `now`). -/
abbrev systemTimeSize : Nat := 16
/-- `size_of::<(usize, Option<usize>)>()` (`Iterator::size_hint`'s sret). -/
abbrev sizeHintSize : Nat := 24
/-- `size_of::<Result<Duration, SystemTimeError>>()` (`SystemTime::duration_since`'s sret). -/
abbrev durationSinceResultSize : Nat := 24
/-- The initialized bytes of `std::sys::time::Timespec { tv_sec: i64, tv_nsec: u32 }`:
    `offset_of!(tv_nsec) + size_of::<u32>()` (replica `Timespec`). -/
abbrev timespecDataSize : Nat := 12
/-- `size_of::<hex::BytesToHexChars>()` (hex 0.4; replica `BytesToHexChars`). -/
abbrev hexIterSize : Nat := 32

/-! ### API results (the `libsignalApi` sret buffers) -/

/-- `size_of::<Option<Result<CiphertextMessage, SignalProtocolError>>>()`, the sret of
    `session_message_encrypt`. -/
abbrev encryptSretSize : Nat := 0xf8
/-- The `SignalMessage` payload of `Some(Ok(CiphertextMessage::SignalMessage(_)))` in the encrypt
    result: `offset_of!(EncryptResult, Some.0.Ok.0.SignalMessage.0)`. -/
abbrev encryptResultMessageOff : Nat := 8
/-- `size_of::<Option<Result<Vec<u8>, SignalProtocolError>>>()`, the sret of
    `session_message_decrypt_signal`. -/
abbrev decryptSretSize : Nat := 0x30
/-- `size_of::<Result<SignalMessage, SignalProtocolError>>()`: the sret of
    `session_signal_message_parse` and of `SignalMessage::try_from` / `OTR::encrypt`. -/
abbrev signalMessageResultSize : Nat := 0x78
/-- `size_of::<Result<OutgoingTripleRatchet, SignalProtocolError>>()` (replica OTR). -/
abbrev otrResultSize : Nat := 200
/-- `offset_of!(Result<SignalMessage, SignalProtocolError>, Err.0)`: the SPE of an `Err` whose
    payload type is 120 / 200 bytes (`errResultAt`). -/
abbrev resultErrSpeOff : Nat := 8
/-- `offset_of!(Result<Vec<u8>, SignalProtocolError>, Ok.0)` (`vecResultAt`). -/
abbrev decResultVecOff : Nat := 8

/-! ### Niche values (word 0) -/

/-- `None` of an `Option<Vec-like>` (`Option<Chain>`, `Option<chain::ChainKey>`,
    `Option<PendingPreKey>`, ...): the capacity word `usize::MAX`. -/
abbrev optionVecNoneWord : Nat := 0xFFFFFFFFFFFFFFFF
/-- The `Err` tag word of `Result<T, SPE>` for `T` = `SignalMessage` / `OutgoingTripleRatchet`. -/
abbrev resultErrTag : Nat := 0xFFFFFFFFFFFFFFFF
/-- The `Ok` tag word of `Result<Vec<u8>, SPE>`. -/
abbrev resultVecOkTag : Nat := 0xFFFFFFFFFFFFFFFE
/-- SPE word 0 of the non-dataful variant with index `i` is `speNicheBase + i`. -/
abbrev speNicheBase : Nat := 0x8000000000000000
/-- Word 0 of `Some(Ok(CiphertextMessage::SignalMessage(_)))` in the encrypt result (a niche
    value: rustc's `matches!` on this variant is exactly `word0 = this`). The `send` event's guard. -/
abbrev encryptSignalMessageTag : Nat := 0x8000000000000000
/-- Word 0 of `Some(Ok(_))` in the decrypt result `Option<Result<Vec<u8>, SPE>>` (rustc's
    `matches!` is exactly `word0 = this`). The `accept` event's guard. -/
abbrev decryptOkTag : Nat := 0xFFFFFFFFFFFFFFFE

/-! ### `SignalProtocolError` (SPE) -/

/-- `size_of::<SignalProtocolError>()`. -/
abbrev speSize : Nat := 48
/-- The first payload field of a dataful SPE variant (`offset_of!(SPE, CiphertextMessageTooShort.0)`,
    also `InvalidState.1`, `InvalidSessionStructure.0`, `DuplicatedMessage.0`, `InvalidMessage.1`,
    the `u8` of `BadKeyType` / `*CiphertextVersion`). -/
abbrev spePayloadOff : Nat := 8
/-- `offset_of!(SPE, InvalidState.0)` (the `&'static str` function name). -/
abbrev speInvalidStateFnOff : Nat := 32
/-- `offset_of!(SPE, DuplicatedMessage.1)` (the counter). -/
abbrev speDupCounterOff : Nat := 12
/-- `offset_of!(SPE, InvalidMessage.0)` (the message type byte). -/
abbrev speInvalidMessageTypeOff : Nat := 32

/-! ### `SignalMessage` -/

/-- `size_of::<SignalMessage>()`. -/
abbrev signalMessageSize : Nat := 0x78
/-- `offset_of!(SignalMessage, ciphertext)` (`Box<[u8]>`). -/
abbrev smCiphertextOff : Nat := 0x18
/-- `offset_of!(SignalMessage, serialized)` (`Box<[u8]>`, the wire bytes). -/
abbrev smSerializedOff : Nat := 0x28
/-- `offset_of!(SignalMessage, sender_ratchet_key)` (32 bytes). -/
abbrev smSenderRatchetKeyOff : Nat := 0x38
/-- `offset_of!(SignalMessage, addresses)` (`Option<Box<[u8]>>`). -/
abbrev smAddressesOff : Nat := 0x58
/-- `offset_of!(SignalMessage, counter)` (`u32`). -/
abbrev smCounterOff : Nat := 0x68
/-- `offset_of!(SignalMessage, previous_counter)` (`u32`). -/
abbrev smPreviousCounterOff : Nat := 0x6c
/-- `offset_of!(SignalMessage, message_version)` (`u8`; padding follows to the end). -/
abbrev smMessageVersionOff : Nat := 0x70

/-! ### `ProtocolAddress`, `SessionRecord`, `IdentityKey`, the in-memory stores -/

/-- `size_of::<ProtocolAddress>()` (`name: String` at `+0`). -/
abbrev protocolAddressSize : Nat := 32
/-- `offset_of!(ProtocolAddress, device_id)` (one byte; padding follows to the end). -/
abbrev addrDeviceOff : Nat := 0x18
/-- `size_of::<SessionRecord>()`. -/
abbrev sessionRecordSize : Nat := 0x170
/-- `offset_of!(SessionRecord, current_session)` (the `SessionStructure`; `previous_sessions:
    Vec<Vec<u8>>` is at `+0`). -/
abbrev recordCurrentSessionOff : Nat := 0x18
/-- `size_of::<IdentityKey>()`. -/
abbrev identityKeySize : Nat := 32
/-- `size_of::<(ProtocolAddress, SessionRecord)>()`: the session table's bucket stride. -/
abbrev sessionBucketStride : Nat := 0x190
/-- `offset_of!((ProtocolAddress, SessionRecord), 1)` (the key is at `+0`). -/
abbrev sessionBucketValueOff : Nat := 0x20
/-- `size_of::<(ProtocolAddress, IdentityKey)>()`: the identity table's bucket stride. -/
abbrev identityBucketStride : Nat := 0x40
/-- `offset_of!((ProtocolAddress, IdentityKey), 1)` (the key is at `+0`). -/
abbrev identityBucketValueOff : Nat := 0x20
/-- `offset_of!(InMemSessionStore, sessions)` (implicit in the spec: the table is at the store). -/
abbrev sessionStoreMapOff : Nat := 0
/-- `offset_of!(InMemIdentityKeyStore, known_keys)` (implicit in the spec, as above). -/
abbrev identityStoreMapOff : Nat := 0
/-- `offset_of!(InMemSignalProtocolStore, session_store)` (implicit in the spec, as above). -/
abbrev protoStoreSessionOff : Nat := 0
/-- `offset_of!(InMemSignalProtocolStore, identity_store)`. -/
abbrev protoStoreIdentityOff : Nat := 0xf0

/-! ### `proto::storage::SessionStructure` (SS) and its parts (prost structs; replica) -/

/-- `size_of::<SessionStructure>()` = `size_of::<SessionState>()`. -/
abbrev sessionStructureSize : Nat := 344
/-- `offset_of!(SessionStructure, remote_identity_public)` (`local_identity_public` is at `+0`). -/
abbrev ssRemoteIdentityOff : Nat := 0x18
/-- `offset_of!(SessionStructure, root_key)`. -/
abbrev ssRootKeyOff : Nat := 0x30
/-- `offset_of!(SessionStructure, receiver_chains)`. -/
abbrev ssReceiverChainsOff : Nat := 0x48
/-- `offset_of!(SessionStructure, alice_base_key)`. -/
abbrev ssAliceBaseKeyOff : Nat := 0x60
/-- `offset_of!(SessionStructure, pq_ratchet_state)`. -/
abbrev ssPqRatchetStateOff : Nat := 0x78
/-- `offset_of!(SessionStructure, sender_chain)`. -/
abbrev ssSenderChainOff : Nat := 0x90
/-- `offset_of!(SessionStructure, pending_pre_key)`. -/
abbrev ssPendingPreKeyOff : Nat := 0xf8
/-- `offset_of!(SessionStructure, pending_kyber_pre_key)`. -/
abbrev ssPendingKyberPreKeyOff : Nat := 0x128
/-- `offset_of!(SessionStructure, session_version)` (`u32`). -/
abbrev ssSessionVersionOff : Nat := 0x148
/-- `offset_of!(SessionStructure, previous_counter)` (`u32`). -/
abbrev ssPreviousCounterOff : Nat := 0x14c
/-- `offset_of!(SessionStructure, remote_registration_id)` (then `local_registration_id`, 8 bytes
    in all). -/
abbrev ssRegistrationIdsOff : Nat := 0x150
/-- `size_of::<session_structure::Chain>()` = `size_of::<Option<Chain>>()`. -/
abbrev chainSize : Nat := 104
/-- `align_of::<session_structure::Chain>()`. -/
abbrev chainAlign : Nat := 8
/-- `offset_of!(Chain, sender_ratchet_key_private)` (`sender_ratchet_key` is at `+0`). -/
abbrev chainPrivOff : Nat := 24
/-- `offset_of!(Chain, message_keys)`. -/
abbrev chainMessageKeysOff : Nat := 48
/-- `offset_of!(Chain, chain_key)` (`Option<chain::ChainKey>`). -/
abbrev chainChainKeyOff : Nat := 72
/-- `size_of::<chain::ChainKey>()` = `size_of::<Option<chain::ChainKey>>()` (`key` at `+0`). -/
abbrev chainKeySize : Nat := 32
/-- `offset_of!(chain::ChainKey, index)` (`u32`; padding follows to the end). -/
abbrev chainKeyIndexOff : Nat := 24
/-- `size_of::<chain::MessageKey>()`. -/
abbrev messageKeySize : Nat := 104
/-- `align_of::<chain::MessageKey>()`. -/
abbrev messageKeyAlign : Nat := 8
/-- `offset_of!(chain::MessageKey, mac_key)` (`cipher_key` is at `+0`). -/
abbrev mkMacKeyOff : Nat := 24
/-- `offset_of!(chain::MessageKey, iv)`. -/
abbrev mkIvOff : Nat := 48
/-- `offset_of!(chain::MessageKey, seed)`. -/
abbrev mkSeedOff : Nat := 72
/-- `offset_of!(chain::MessageKey, index)` (`u32`; padding follows to the end). -/
abbrev mkIndexOff : Nat := 96
/-- `size_of::<PendingPreKey>()` = `size_of::<Option<PendingPreKey>>()` (`base_key` at `+0`). -/
abbrev pendingPreKeySize : Nat := 48
/-- `size_of::<PendingKyberPreKey>()` = `size_of::<Option<..>>()` (`ciphertext` at `+0`). -/
abbrev pendingKyberPreKeySize : Nat := 32

/-! ### `OutgoingTripleRatchet` (OTR; replica) -/

/-- `size_of::<OutgoingTripleRatchet>()` (`pqr_state: Vec<u8>` at `+0`). -/
abbrev otrSize : Nat := 200
/-- `offset_of!(OTR, sender_ratchet_key) + offset_of!(KeyPair, public_key)`. -/
abbrev otrSenderRatchetPubOff : Nat := 0x18
/-- `offset_of!(OTR, sender_ratchet_key) + offset_of!(KeyPair, private_key)`. -/
abbrev otrSenderRatchetPrivOff : Nat := 0x38
/-- `offset_of!(OTR, local_identity_key)`. -/
abbrev otrLocalIdentityOff : Nat := 0x58
/-- `offset_of!(OTR, remote_identity_key)`. -/
abbrev otrRemoteIdentityOff : Nat := 0x78
/-- `offset_of!(OTR, sender_chain_key)` (key, then the `u32` index at `+0x20`). -/
abbrev otrSenderChainKeyOff : Nat := 0x98
/-- `offset_of!(OTR, previous_counter)` (`u32`). -/
abbrev otrPreviousCounterOff : Nat := 0xbc
/-- `offset_of!(OTR, session_version)` (`u8`; padding follows to the end). -/
abbrev otrSessionVersionOff : Nat := 0xc0

/-! ## (b) Library internals (`hashbrown` in `std` 1.98.1, trait-object vtables)

Checked by an aarch64 run-time test
(a recording allocator around
`HashMap<ProtocolAddress, SessionRecord>` / `HashMap<ProtocolAddress, IdentityKey>`, and the
vtables of `&dyn SessionStore` / `&dyn IdentityKeyStore`). A table with `n` buckets of `stride`
bytes is one allocation of `n * stride + n + hashbrownGroupWidth` bytes, alignment
`hashbrownTableAlign`; the buckets end at `ctrl`, followed by the `n + hashbrownGroupWidth`
control bytes. -/

/-- `hashbrown`'s `Group::WIDTH` on aarch64 (the NEON / generic 64-bit group; 16 is x86's SSE2
    group). -/
abbrev hashbrownGroupWidth : Nat := 8
/-- `hashbrown`'s `EMPTY` control byte. -/
abbrev hashbrownEmptyCtrl : Nat := 0xff
/-- The bucket count of the smallest allocated table (`capacity_to_buckets` for capacity < 4). -/
abbrev hashbrownMinBuckets : Nat := 4
/-- The table allocation's alignment: `max(align_of::<(K, V)>(), Group::WIDTH)`. -/
abbrev hashbrownTableAlign : Nat := 8
/-- `HashMap<K, V, RandomState>`: the `ctrl` pointer word (`RawTableInner`). Implicit in the spec
    (`tableAt` reads `ctrl` at the table pointer itself). -/
abbrev tableCtrlOff : Nat := 0
/-- `HashMap<K, V, RandomState>`: the `bucket_mask` word (buckets - 1). -/
abbrev tableMaskOff : Nat := 8
/-- `HashMap<K, V, RandomState>`: the `growth_left` word. -/
abbrev tableGrowthLeftOff : Nat := 16
/-- `HashMap<K, V, RandomState>`: the `items` word (the number of full buckets). -/
abbrev tableItemsOff : Nat := 24
/-- `HashMap<K, V, RandomState>`: the `RandomState` hasher (two `u64` keys). -/
abbrev tableHasherOff : Nat := 32
/-- `size_of::<RandomState>()`. -/
abbrev tableHasherSize : Nat := 16
/-- `dyn SessionStore` vtable: `load_session` (after drop, size, align; trait method order). -/
abbrev sessionStoreLoadSlot : Nat := 0x18
/-- `dyn SessionStore` vtable: `store_session`. -/
abbrev sessionStoreStoreSlot : Nat := 0x20
/-- `dyn IdentityKeyStore` vtable: `save_identity`. -/
abbrev identityStoreSaveSlot : Nat := 0x28
/-- `dyn IdentityKeyStore` vtable: `is_trusted_identity`. -/
abbrev identityStoreTrustedSlot : Nat := 0x30

/-! ## (c) Harness conventions (not binary layout; no check script)

Fixed by the statement for the harness, not read off the binary. -/

/-- The call stack the harness gives every API call: `2^18` bytes below `sp`. Equal to
`CryptoVerification.LibsignalTripleRatchet.rootStack`. -/
abbrev rootStack : Nat := 262144

/-! ## The `asm%` elaborators -/

open Lean Elab Term Meta

public meta section

/-- The value of a closed `Nat` term over the constants above (`AsmConstants` is open in it). -/
def evalAsmNat (stx : Syntax) : TermElabM Nat := do
  let e ← elabTermEnsuringType (← `(open AsmConstants in ($(⟨stx⟩) : Nat))) (mkConst ``Nat)
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar then
    throwErrorAt stx "asm%: `{e}` is not a closed `Nat` term"
  let r ← withTransparency .default <| Meta.reduce e
  match r.rawNatLit?, r.nat? with
  | some n, _ => return n
  | none, some n => return n
  | none, none => throwErrorAt stx "asm%: `{e}` does not evaluate to a numeral (got `{r}`)"

/-- `asm% e`: the `Nat` numeral that `e` (a closed `Nat` term over `AsmConstants`) evaluates to. -/
syntax (name := asmNat) "asm% " term:max : term
/-- `asm64% e`: the `BitVec 64` literal `n#64`, where `n` is the value of `e` (as `asm%`). -/
syntax (name := asmBv64) "asm64% " term:max : term
/-- `asm8% e`: the `BitVec 8` literal `n#8`, where `n` is the value of `e` (as `asm%`). -/
syntax (name := asmBv8) "asm8% " term:max : term

@[term_elab asmNat]
def elabAsmNat : TermElab := fun stx _ => do
  let n ← evalAsmNat stx[1]
  elabTerm (Syntax.mkNumLit (toString n)) (some (mkConst ``Nat))

/-- The literal `n#w` (elaborated as written: `BitVec.ofNat w n`). -/
def elabBvLit (w n : Nat) : TermElabM Expr := do
  elabTerm (← `($(Syntax.mkNumLit (toString n)):num#$(Syntax.mkNumLit (toString w)))) none

@[term_elab asmBv64]
def elabAsmBv64 : TermElab := fun stx _ => do elabBvLit 64 (← evalAsmNat stx[1])

@[term_elab asmBv8]
def elabAsmBv8 : TermElab := fun stx _ => do elabBvLit 8 (← evalAsmNat stx[1])

end

end AsmConstants
