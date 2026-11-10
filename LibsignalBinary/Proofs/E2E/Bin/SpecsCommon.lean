/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
public import LibsignalBinary.Proofs.E2E.Bin.Record
public import LibsignalBinary.Proofs.E2E.Bin.Tpidr
public import LibsignalBinary.Proofs.E2E.StoreNew.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Wrapper-Layer Specifications for `libsignal_e2e`

Defines party constants (`ALICE`, `BOB`), symbol and `.data.rel.ro` offset guards, in-memory store
and record layouts, and specifications for `open`, `close`, `pack`, `session_send`, and
`session_recv`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E (partyAddressName partyIdentityKey)
open CryptoVerification.E2E.InMem.HashbrownBin (tableAllocSize sessionBucketStride sessionBucketValueOff
  identityBucketStride identityBucketValueOff table4At table4SingleAt identityBucketEntryAt)

/-! ## Symbol Names and Offsets in `libsignalSessionImage` -/

abbrev openName                  : String := "libsignal_e2e::open"
abbrev recordDeserializeName     : String := "<libsignal_protocol::state::session::SessionRecord>::deserialize"
abbrev recordSerializeName       : String := "<libsignal_protocol::state::session::SessionRecord>::serialize"
abbrev identityKeyDecodeName     : String := "<libsignal_protocol::identity_key::IdentityKey>::decode"
abbrev inMemSessionStoreNewName  : String := "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new"
abbrev inMemIdentityStoreNewName : String := "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new"
abbrev inMemSaveIdentityName     : String := "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity"
abbrev inMemIsTrustedName        : String := "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"
abbrev inMemGetIdKeyPairName     : String := "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"
abbrev inMemGetLocalRegIdName    : String := "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"
abbrev inMemGetIdentityName      : String := "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity"
abbrev inMemStoreSessionName     : String := "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session"
abbrev inMemLoadSessionName      : String := "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session"
abbrev encryptName               : String := "session_message_encrypt"
abbrev decryptSignalName         : String := "session_message_decrypt_signal"
abbrev parseSignalMessageName    : String := "session_signal_message_parse"
abbrev noopWakerCloneName        : String := "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]"
abbrev noopWakerNoopName         : String := "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#2} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]"

abbrev deserializeOff           : BitVec 64 := bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")
abbrev serializeOff             : BitVec 64 := bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")
abbrev identityKeyDecodeOff     : BitVec 64 := bv% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode")
abbrev inMemSessionStoreNewOff  : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new")
abbrev inMemIdentityStoreNewOff : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new")
abbrev inMemSaveIdentityOff     : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity")
abbrev inMemStoreSessionOff     : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session")
abbrev inMemLoadSessionOff      : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session")
abbrev encryptOff               : BitVec 64 := bv% (ls_off% "session_message_encrypt")
abbrev decryptSignalOff         : BitVec 64 := bv% (ls_off% "session_message_decrypt_signal")
abbrev parseSignalMessageOff    : BitVec 64 := bv% (ls_off% "session_signal_message_parse")
abbrev rustAllocOff             : BitVec 64 := bv% (ls_off% "__rustc::__rust_alloc")
abbrev rustNoAllocShimOff       : BitVec 64 := bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
abbrev noopWakerOff             : BitVec 64 := bv% (ls_reloc% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]")))
abbrev noopWakerVtableOff       : BitVec 64 := bv% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]"))
abbrev tlsKeysTpoff             : BitVec 64 := 0x10#64
abbrev emptyCtrlOff             : BitVec 64 := bv% (ls_bytes% "ffffffffffffffff67726f75705f6964")

/-! ## `fnOff` and `.data.rel.ro` Guards -/

section AddrGuards
open ProofLib.ProgramReflection
set_option maxRecDepth 2000000

theorem deserialize_fnOff           : libsignalSessionCode.fnOff recordDeserializeName     = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") := (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")
theorem serialize_fnOff             : libsignalSessionCode.fnOff recordSerializeName       = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") := (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::serialize")
theorem identityKeyDecode_fnOff     : libsignalSessionCode.fnOff identityKeyDecodeName     = num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode") := (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode")
theorem inMemSessionStoreNew_fnOff  : libsignalSessionCode.fnOff inMemSessionStoreNewName  = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new")
theorem inMemIdentityStoreNew_fnOff : libsignalSessionCode.fnOff inMemIdentityStoreNewName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new")
theorem inMemSaveIdentity_fnOff     : libsignalSessionCode.fnOff inMemSaveIdentityName     = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity")
theorem inMemIsTrusted_fnOff        : libsignalSessionCode.fnOff inMemIsTrustedName        = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity")
theorem inMemGetIdKeyPair_fnOff     : libsignalSessionCode.fnOff inMemGetIdKeyPairName     = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")
theorem inMemGetLocalRegId_fnOff    : libsignalSessionCode.fnOff inMemGetLocalRegIdName    = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")
theorem inMemGetIdentity_fnOff      : libsignalSessionCode.fnOff inMemGetIdentityName      = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity")
theorem inMemStoreSession_fnOff     : libsignalSessionCode.fnOff inMemStoreSessionName     = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session")
theorem inMemLoadSession_fnOff      : libsignalSessionCode.fnOff inMemLoadSessionName      = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session") := (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session")
theorem encrypt_fnOff               : libsignalSessionCode.fnOff encryptName               = num% (ls_off% "session_message_encrypt") := (ls_lemma% fnOff "session_message_encrypt")
theorem decryptSignal_fnOff         : libsignalSessionCode.fnOff decryptSignalName         = num% (ls_off% "session_message_decrypt_signal") := (ls_lemma% fnOff "session_message_decrypt_signal")
theorem parseSignalMessage_fnOff    : libsignalSessionCode.fnOff parseSignalMessageName    = num% (ls_off% "session_signal_message_parse") := (ls_lemma% fnOff "session_signal_message_parse")
theorem noopWakerClone_fnOff        : libsignalSessionCode.fnOff noopWakerCloneName        = num% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]") := (ls_lemma% fnOff "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]")
theorem noopWakerNoop_fnOff         : libsignalSessionCode.fnOff noopWakerNoopName         = num% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#2} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]") := (ls_lemma% fnOff "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#2} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]")
theorem rustAlloc_hookAtOff (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase 0#64 ext).hookAtOff? num% (ls_off% "__rustc::__rust_alloc") = ext allocName :=
  (ls_hook% "__rustc::__rust_alloc") ext
theorem rustNoAllocShim_hookAtOff (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase 0#64 ext).hookAtOff? num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") = ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" :=
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") ext

noncomputable def hasRelocAt (secOff target : Nat) : Bool :=
  libsignalSessionImage.relocs.any fun r =>
    decide (r.off = secOff - libsignalSessionImage.dataOff ∧ r.width = 8 ∧ r.target = target)

/-- `noopWakerOff` (`0x50cc8`) relocates to `noopWakerVtableOff` (`0x50bf8`), whose 4 slots
(`clone`, `wake`, `wake_by_ref`, `drop`) relocate to `noopWakerCloneName` (`0x469b4`) and
`noopWakerNoopName` (`0x469c4`). -/
theorem noopWakerVtable_slots_guard :
    hasRelocAt (num% (ls_reloc% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]")))) (num% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]"))) = true ∧
    hasRelocAt (num% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]"))) (libsignalSessionCode.fnOff noopWakerCloneName) = true ∧
    hasRelocAt (num% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]") + 8)) (libsignalSessionCode.fnOff noopWakerNoopName) = true ∧
    hasRelocAt (num% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]") + 16)) (libsignalSessionCode.fnOff noopWakerNoopName) = true ∧
    hasRelocAt (num% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]") + 24)) (libsignalSessionCode.fnOff noopWakerNoopName) = true := by
  rw [noopWakerClone_fnOff, noopWakerNoop_fnOff]
  refine ⟨by rfl_kernel, by rfl_kernel, by rfl_kernel, by rfl_kernel, by rfl_kernel⟩

/-- `emptyCtrlOff` (`0x4a5f0`, `EMPTY_BUCKETS` static control bytes for `hashbrown::RawTable::new`)
guard: `0x4a658` relocates to `0x4a5f0`, which contains 8 `0xFF` (`Group::EMPTY`) bytes (`Group::WIDTH = 8` on ARM64 NEON). -/
theorem emptyCtrl_rodata_guard :
    hasRelocAt (num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964"))) (num% (ls_bytes% "ffffffffffffffff67726f75705f6964")) = true ∧
    (libsignalSessionImage.data.drop (num% (ls_bytes% "ffffffffffffffff67726f75705f6964") - libsignalSessionImage.dataOff)).take 8 =
      List.replicate 8 0xff#8 := by
  refine ⟨by rfl_kernel, by rfl_kernel⟩

end AddrGuards

/-! ## Party Model and `InMem` Store Layouts -/

inductive Role where | alice | bob deriving DecidableEq, Repr

def Role.ofWho (who : BitVec 32) : Option Role :=
  if who = 0#32 then some .alice else if who = 1#32 then some .bob else none
def Role.peer : Role → Role | .alice => .bob | .bob => .alice
def Role.nameBytes : Role → List (BitVec 8) | .alice => aliceNameBytes | .bob => bobNameBytes
def Role.idPubWire : Role → List (BitVec 8) | .alice => aliceIdPubWire | .bob => bobIdPubWire
def Role.idPrivBytes : Role → List (BitVec 8) | .alice => aliceIdPrivBytes | .bob => bobIdPrivBytes
def Role.idKey : Role → IdentityKey | .alice => aliceIdKey | .bob => bobIdKey
def Role.addrVal (r : Role) : AddrVal := ⟨r.nameBytes, 1#8⟩
def Role.keyPairBytes (r : Role) : List (BitVec 8) :=
  r.idKey.publicKey.bytes.toList ++ List.Vector.toList (Ratchet.clampScalar ⟨r.idPrivBytes, by cases r <;> decide⟩)
def Role.toParty : Role → Party | .alice => .A | .bob => .B
def Role.ofParty : Party → Role | .A => .alice | .B => .bob

theorem Role.nameBytes_eq (r : Role) : r.nameBytes = utf8 (partyAddressName r.toParty) := by
  cases r <;> rfl

theorem Role.idKey_eq (r : Role) : r.idKey = partyIdentityKey r.toParty := by
  cases r <;> rfl

abbrev tlsKeysRawAt := CryptoVerification.E2E.StoreNew.tlsKeysRawAt
abbrev tlsKeysInitAt := CryptoVerification.E2E.StoreNew.tlsKeysInitAt
abbrev tlsKeysUninitAt := CryptoVerification.E2E.StoreNew.tlsKeysUninitAt
abbrev tlsKeysAt := CryptoVerification.E2E.StoreNew.tlsKeysAt

abbrev emptyRawTableAt := CryptoVerification.E2E.StoreNew.emptyRawTableAt
abbrev emptyHashMapAt := CryptoVerification.E2E.StoreNew.emptyHashMapAt
abbrev emptyIdentityKeyStoreAt := CryptoVerification.E2E.StoreNew.emptyIdentityKeyStoreAt

/-- 4-bucket `InMemSessionStore` (`48` B at `out`) holding at most one `(peerAddr, rec)` entry:
`none` = freshly constructed empty `HashMap`, `some s` = `HashbrownBin.table4SingleAt A sessionBucketStride`
(`mask = 3`, `items = 1`, `growth_left = 2`, `tableAllocSize 4 sessionBucketStride = 1612`-byte
heap allocation, `singleCtrl4`) with `(peerAddr, ⟨some s⟩)` at bucket `idx < 4`. -/
def inMemSessionStoreAt (A : RustAlloc) (img : Obj.Image) (out : BitVec 64) (peer : Role)
    (opt : Option (Session (List (BitVec 8)))) : SepProp :=
  ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
    match opt with
    | none => emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1
    | some s =>
      ∃∗ idx : Nat, ∃∗ gAddr : AddrGhost, ∃∗ G : SessionGhost,
        ⌜gAddr.val = peer.addrVal ∧ BinCanonSession G s⌝ ∗
        table4SingleAt A sessionBucketStride out k0 k1 idx peer.nameBytes 1#8
          (fun a =>
            protocolAddressAt A gAddr a ∗
            sessionRecordAt A (a + asm64% InMem.HashbrownBin.sessionBucketValueOff) ⟨0#64, 8#64, some G⟩ ⟨some s⟩)

/-- 4-bucket `InMemIdentityKeyStore` (`120` B at `out`) for `me : Role` holding at most one
`(peerAddr, peerKey)` entry (`none` = empty `HashMap`, `some peerKey` =
`HashbrownBin.table4SingleAt A identityBucketStride` with `growth_left = 2`,
`tableAllocSize 4 identityBucketStride = 268`-byte heap allocation, `singleCtrl4`, and
`HashbrownBin.identityBucketEntryAt`). -/
def inMemIdentityStoreAt (A : RustAlloc) (img : Obj.Image) (out : BitVec 64) (me : Role)
    (opt : Option IdentityKey) : SepProp :=
  ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
    ((out + 48#64) ↦ₛ me.keyPairBytes) ∗ ((out + 112#64) ↦₃₂ 0#32) ∗ memRegion (out + 116#64) 4 ∗
    match opt with
    | none => emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1
    | some ik =>
      ∃∗ idx : Nat, ∃∗ gAddr : AddrGhost,
        ⌜gAddr.val = me.peer.addrVal⌝ ∗
        table4SingleAt A identityBucketStride out k0 k1 idx me.peer.nameBytes 1#8
          (identityBucketEntryAt A gAddr ik.publicKey.bytes.toList)

/-- 232-byte `Call` struct at `callPtr`:
`+0x00`: `me : ProtocolAddress` (32 B), `+0x20`: `peer : ProtocolAddress` (32 B),
`+0x40`: `sessions : InMemSessionStore` (48 B), `+0x70`: `identities : InMemIdentityKeyStore` (120 B). -/
def callAt (A : RustAlloc) (img : Obj.Image) (callPtr : BitVec 64) (role : Role)
    (s : Session (List (BitVec 8))) : SepProp :=
  ∃∗ gMe : AddrGhost, ∃∗ gPeer : AddrGhost,
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36⌝ ∗
    protocolAddressAt A gMe callPtr ∗
    protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
    inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer (some s) ∗
    inMemIdentityStoreAt A img (callPtr + 0x70#64) role (some role.peer.idKey)

/-- 232-byte `Option<Call>` at `outPtr`: `some (role, s)` owns `callAt` (where `[outPtr] = ctrlPtr ≠ -1`),
`none` has niche `[outPtr] = -1` (`0xffffffffffffffff`). -/
def openResultAt (A : RustAlloc) (img : Obj.Image) (outPtr : BitVec 64) :
    Option (Role × Session (List (BitVec 8))) → SepProp
  | some (role, s) => callAt A img outPtr role s
  | none => (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (outPtr + 8#64) 224

/-- 32-byte `Option<Vec<u8>>` written by `close` at `outPtr`: tag `-2` (`0xfffffffffffffffe`) + `vecU8`. -/
def serializedVecAt (A : RustAlloc) (outPtr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗ vecU8 A (outPtr + 8#64) bs

/-- Heap block returned by `pack(state, msg)`: `[ls : u64 LE][lm : u64 LE][state][msg]`. -/
def packedOutAt (A : RustAlloc) (ptr : BitVec 64) (stateBytes msgBytes : List (BitVec 8)) : SepProp :=
  let ls := stateBytes.length
  let lm := msgBytes.length
  ⌜ptr ≠ 0#64 ∧ 16 + ls + lm < 2 ^ 63⌝ ∗
    A.live ptr (16 + ls + lm) 1 ∗
    (ptr ↦₆₄ BitVec.ofNat 64 ls) ∗
    ((ptr + 8#64) ↦₆₄ BitVec.ofNat 64 lm) ∗
    ((ptr + 16#64) ↦ₛ stateBytes) ∗
    ((ptr + BitVec.ofNat 64 (16 + ls)) ↦ₛ msgBytes)

/-! ## Callee Specifications -/

abbrev binEntryStack : Nat := 0x4e80 + LibsignalPublicApi.entryStack
abbrev tryFromStack  : Nat := smallRootStack
abbrev openStack     : Nat := 0x3f0 + recordDeserializeStack
abbrev closeStack    : Nat := 0x220 + binEntryStack
abbrev packStack     : Nat := 0x060 + extHookStack
abbrev sendStack     : Nat := 0x540 + binEntryStack
abbrev recvStack     : Nat := 0x560 + binEntryStack

def serializeAddrVal : AddrVal → AddrVal → Option (List (BitVec 8))
  | ⟨sName, sDev⟩, ⟨rName, rDev⟩ => do
    let s ← serviceIdParse uuidTryParse sName
    let r ← serviceIdParse uuidTryParse rName
    return addrBytes s sDev ++ addrBytes r rDev

def storedSession {Addr PQ : Type} (s0 : Session PQ) (calls : List (StoreCall Addr PQ)) : Session PQ :=
  calls.foldl (fun cur c => match c with | .storeSession _ ⟨some s'⟩ => s' | _ => cur) s0

/-- `<IdentityKey>::decode` (`0x0ae58`): decodes 33-byte `0x05 ‖ pk` into 40-byte `Result<IdentityKey, SPE>` at `x8`. -/
def identityKeyDecodeSpec : Spec (BitVec 64 × BitVec 64 × Role) where
  pre := fun (ret, keyPtr, r) s =>
    ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = keyPtr ∧ s.readReg64 .x1 = 33#64⌝ ∗
      (keyPtr ↦ₛ r.idPubWire) ∗ memRegion ret 40 ∗ stackAt s.sp 0x60
  post := fun (ret, keyPtr, r) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (keyPtr ↦ₛ r.idPubWire) ∗
      (ret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((ret + 8#64) ↦ₛ r.idKey.publicKey.bytes.toList) ∗ stackAt s0.sp 0x60

/-- `<InMemSignedPreKeyStore>::new` (`0x127d8`, ICF-shared with `InMemSessionStore::new`). -/
def sessionStoreNewSpec (img : Obj.Image) : Spec (BitVec 64 × Option (BitVec 64 × BitVec 64)) :=
  Spec.inImage
    { pre := fun (out, st) s =>
        ⌜s.readReg64 .x8 = out⌝ ∗ memRegion out 48 ∗
          tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) st ∗ stackAt s.sp (0x20 + extHookStack)
      post := fun (out, _) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
            emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗
              tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
          stackAt s0.sp (0x20 + extHookStack) }
    img

/-- `<InMemIdentityKeyStore>::new` (`0x0c238`). -/
def identityStoreNewSpec (img : Obj.Image) : Spec (BitVec 64 × BitVec 64 × Role × Option (BitVec 64 × BitVec 64)) :=
  Spec.inImage
    { pre := fun (out, kpPtr, me, st) s =>
        ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = kpPtr ∧ s.readReg32 .x1 = 0#32⌝ ∗
          memRegion out 120 ∗ (kpPtr ↦ₛ me.keyPairBytes) ∗
          tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) st ∗ stackAt s.sp (0x30 + extHookStack)
      post := fun (out, kpPtr, me, _) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
            emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 me.keyPairBytes 0#32 ∗
              tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
          (kpPtr ↦ₛ me.keyPairBytes) ∗ stackAt s0.sp (0x30 + extHookStack) }
    img

/-- `InMemIdentityKeyStore::save_identity` (`0x2ddc0`) + `poll_once`: inserts `(peerAddr, peer.idKey)`
and writes `Poll::Ready(Ok(IdentityChange::NewOrUnchanged))` (`[pollOut] = -2`). -/
def inMemSaveIdentitySpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × AddrGhost × Role) :=
  Spec.inImage
    { pre := fun (self, addrPtr, keyPtr, pollOut, gPeer, me) s =>
        ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = addrPtr ∧ s.readReg64 .x2 = keyPtr ∧
          s.readReg64 .x8 = pollOut ∧ gPeer.val = me.peer.addrVal⌝ ∗
          inMemIdentityStoreAt A img self me none ∗ protocolAddressAt A gPeer addrPtr ∗
          (keyPtr ↦ₛ me.peer.idKey.publicKey.bytes.toList) ∗ memRegion pollOut 48 ∗
          A.pool ∗ stackAt s.sp (0x800 + extHookStack)
      post := fun (self, addrPtr, keyPtr, pollOut, gPeer, me) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          inMemIdentityStoreAt A img self me (some me.peer.idKey) ∗ protocolAddressAt A gPeer addrPtr ∗
          (keyPtr ↦ₛ me.peer.idKey.publicKey.bytes.toList) ∗
          (pollOut ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (pollOut + 8#64) 40 ∗
          A.pool ∗ stackAt s0.sp (0x800 + extHookStack)
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- `InMemSessionStore::store_session` (`0x2f458`) + `poll_once`: clones `s` into `self[peerAddr]`
and writes `Poll::Ready(Ok(()))` (`[pollOut] = -2`). -/
def inMemStoreSessionSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × AddrGhost × Role × RecordGhost × Session (List (BitVec 8))) :=
  Spec.inImage
    { pre := fun (self, addrPtr, recPtr, pollOut, gPeer, peer, gRec, sess) s =>
        ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = addrPtr ∧ s.readReg64 .x2 = recPtr ∧
          s.readReg64 .x8 = pollOut ∧ gPeer.val = peer.addrVal ∧ CanonRecord gRec ⟨some sess⟩⌝ ∗
          inMemSessionStoreAt A img self peer none ∗ protocolAddressAt A gPeer addrPtr ∗
          sessionRecordAt A recPtr gRec ⟨some sess⟩ ∗ memRegion pollOut 48 ∗
          A.pool ∗ stackAt s.sp (0x800 + extHookStack)
      post := fun (self, addrPtr, recPtr, pollOut, gPeer, peer, gRec, sess) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          inMemSessionStoreAt A img self peer (some sess) ∗ protocolAddressAt A gPeer addrPtr ∗
          sessionRecordAt A recPtr gRec ⟨some sess⟩ ∗
          (pollOut ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (pollOut + 8#64) 40 ∗
          A.pool ∗ stackAt s0.sp (0x800 + extHookStack)
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

abbrev inMemLoadPollOff : BitVec 64 := bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")
abbrev inMemLoadFutVtOff : BitVec 64 := bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") - 24)

/-- 24-byte heap-allocated `load_session` future box `[self, addrPtr, state = 0#8]` returned by
`<InMemSessionStore as SessionStore>::load_session` (`0x2f408`). -/
def inMemLoadFutAt (A : RustAlloc) (futPtr self addrPtr : BitVec 64) : SepProp :=
  ⌜futPtr ≠ 0#64⌝ ∗ A.live futPtr 24 8 ∗
    (futPtr ↦₆₄ self) ∗ ((futPtr + 8#64) ↦₆₄ addrPtr) ∗
    ((futPtr + 16#64) ↦₈ 0#8) ∗ memRegion (futPtr + 17#64) 7

/-- `<InMemSessionStore as SessionStore>::load_session` shim (`0x2f408`): allocates the 24-byte
future box and returns `(x0 = futPtr, x1 = img.base + 0x4dea8#64)`. -/
def inMemLoadShimSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64) :=
  Spec.inImage
    { pre := fun (self, addrPtr) s =>
        ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = addrPtr⌝ ∗
          A.pool ∗ stackAt s.sp (0x20 + extHookStack)
      post := fun (self, addrPtr) s0 sf =>
        ⌜sf.trace = s0.trace ∧ sf.readReg64 .x1 = img.base + inMemLoadFutVtOff⌝ ∗
          ((img.base + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemSessionStore as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))) ↦₆₄ᵣ (img.base + inMemLoadPollOff)) ∗
          inMemLoadFutAt A (sf.readReg64 .x0) self addrPtr ∗
          A.pool ∗ stackAt s0.sp (0x20 + extHookStack)
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- `<InMemSessionStore as SessionStore>::load_session::{closure#0}` poll (`0x08ce4`): looks up
`peerAddr` in `self` and clones `⟨some sess⟩` into `pollOut` (`Ready(Ok(Some(rec)))`). -/
def inMemLoadSessionSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × AddrGhost × Role × Session (List (BitVec 8))) :=
  Spec.inImage
    { pre := fun (futPtr, self, addrPtr, pollOut, gPeer, peer, sess) s =>
        ⌜s.readReg64 .x0 = futPtr ∧ s.readReg64 .x8 = pollOut ∧
          gPeer.val = peer.addrVal ∧ gPeer.name.bytes.length = 36 ∧
          RecordInScope ⟨some sess⟩⌝ ∗
          inMemLoadFutAt A futPtr self addrPtr ∗
          inMemSessionStoreAt A img self peer (some sess) ∗ protocolAddressAt A gPeer addrPtr ∗
          memRegion pollOut 368 ∗ A.pool ∗ stackAt s.sp (0xc00 + extHookStack)
      post := fun (_, self, addrPtr, pollOut, gPeer, peer, sess) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          inMemSessionStoreAt A img self peer (some sess) ∗ protocolAddressAt A gPeer addrPtr ∗
          (∃∗ G : SessionGhost, ⌜BinCanonSession G sess⌝ ∗
            sessionRecordAt A pollOut ⟨0#64, 8#64, some G⟩ ⟨some sess⟩) ∗
          A.pool ∗ stackAt s0.sp (0xc00 + extHookStack) ∗ anyHeap
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Identity-key invariant for `role`: `remoteIdentity = some role.peer.idKey` and
`localIdentity = role.idKey`. -/
def RoleSessionIds (role : Role) (s : Session (List (BitVec 8))) : Prop :=
  s.state.remoteIdentity = some role.peer.idKey ∧ s.state.localIdentity = role.idKey

/-- Canonical encoding predicate for `SessionRecord::deserialize` (`0x16ed4`) in `open`. -/
def RecordCanonical (stateBytes : List (BitVec 8)) (s : Session (List (BitVec 8))) : Prop :=
  stateBytes = encodeRecord ⟨some s⟩ ∧ Record.DeserializeGeneral.DeserializeScope ⟨some s⟩ ∧ ∃ G, BinCanonSession G s

/-- `SessionRecord::deserialize` (`0x16ed4`) on a canonical encoded `SessionRecord`. -/
def recordDeserializeOpenSpec (A : RustAlloc) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) where
  pre := fun (ptr, bs, out, sess) st =>
    ⌜st.readReg64 .x0 = ptr ∧ (st.readReg64 .x1).toNat = bs.length ∧
      st.readReg64 .x8 = out ∧ RecordCanonical bs sess⌝ ∗
      (ptr ↦ₛ bs) ∗ memRegion out 0x170 ∗ A.pool ∗ stackAt st.sp recordDeserializeStack
  post := fun (ptr, bs, out, sess) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ bs) ∗
      (∃∗ G : SessionGhost, ⌜BinCanonSession G sess⌝ ∗
        sessionRecordAt A out ⟨0#64, 8#64, some G⟩ ⟨some sess⟩) ∗
      A.pool ∗ stackAt s0.sp recordDeserializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Deterministic `StoreAnswers` for `InMem` stores populated by `open(role, ⟨some s⟩)`:
`load_session` returns `.ok (some ⟨some s⟩)`, `is_trusted_identity` returns `.ok true`,
`save_identity` returns `.ok .newOrUnchanged`, `store_session` returns `.ok ()`. -/
def inMemAnswers (s : Session (List (BitVec 8))) : StoreAnswers (List (BitVec 8)) Unit where
  loadSession := .ok (some ⟨some s⟩)
  isTrustedIdentity := .ok true
  saveIdentity := .ok .newOrUnchanged
  storeSession := .ok ()

/-- Exact RNG tape bytes drawn by `messageEncrypt` on `s` (`0` when `s.state.pqRatchetState = []`). -/
def sendDraws (S : SpqrModel) (s : Session (List (BitVec 8))) (rest : List (BitVec 8)) : Nat :=
  match execOk OutgoingTripleRatchet.fromSessionState s.state with
  | .ok (otr, taken) =>
    if taken.remoteIdentity.isSome then
      match s.pendingPreKey with
      | none => S.draws otr.pqrState rest
      | some items =>
        match (SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat).bind
            (·.checkedAddSecs maxUnacknowledgedSessionAge) with
        | some expiry => if expiry.lt SystemTime.unixEpoch then 0 else S.draws otr.pqrState rest
        | none => 0
    else 0
  | .error _ => 0

/-- RNG tape bytes drawn by `messageDecryptSignal` on `s` and `msg`:
`decryptDraws C s.state msg.senderRatchetKey rest` when the version check passes, else `0`. -/
def recvDraws (C : Crypto) (s : Session (List (BitVec 8))) (msg : SignalMessage)
    (rest : List (BitVec 8)) : Nat :=
  if s.state.version.toNat = msg.messageVersion.toNat then
    decryptDraws C s.state msg.senderRatchetKey rest
  else 0

/-- Unwrap `CiphertextMessage` wire bytes: both `SignalMessage` and `PreKeySignalMessage`
return the inner `SignalMessage.serialized` wire bytes (`e2e/src/lib.rs:321–325`). -/
def unwrapCiphertextBytes : CiphertextMessage → Option (List (BitVec 8))
  | .signalMessage sm => some sm.serialized
  | .preKeySignalMessage psm => some psm.message.serialized

/-- 248-byte `Result<CiphertextMessage, SignalProtocolError>` at `ret` (`sp + 0xf8` in `session_send`):
- `.ok (.signalMessage sm)`: word 0 = `0x8000000000000000#64`, `sm` at `ret + 8` (`sm.serialized` at `ret + 0x30`),
- `.ok (.preKeySignalMessage psm)`: word 0 `w` with `w.toNat < 2 ^ 63`, `psm.message.serialized` at `ret + 0x28`,
- `.error _`: word 0 = `0xffffffffffffffff#64` (`errTag`). -/
def apiEncResultAtLoose (A : RustAlloc) (ret : BitVec 64) :
    Except (ApiError AddrVal Unit) CiphertextMessage → SepProp
  | .ok (.signalMessage sm) =>
    (ret ↦₆₄ 0x8000000000000000#64) ∗
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (ret + 8#64) sm) ∗
      memRegion (ret + 128#64) 120
  | .ok (.preKeySignalMessage psm) =>
    (∃∗ w : BitVec 64, ⌜w.toNat < 2 ^ 63⌝ ∗ (ret ↦₆₄ w)) ∗ memRegion (ret + 8#64) 32 ∗
      (∃∗ serPtr : BitVec 64, boxU8At A (ret + 0x28#64) serPtr psm.message.serialized) ∗
      memRegion (ret + 0x38#64) 192 ∗ anyHeap
  | .error _ =>
    (ret ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ret + 8#64) 240 ∗ anyHeap

/-- `session_signal_message_parse` (`0x3dab8`), wrapping `SignalMessage.tryFrom protoSignalCodec`. -/
def parseSignalMessageSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  Spec.inImage
    { pre := fun (ret, ctPtr, ctext) s =>
        ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = ctPtr ∧ (s.readReg64 .x1).toNat = ctext.length ∧
          ctext.length < 2 ^ 32⌝ ∗
          (ctPtr ↦ₛ ctext) ∗ memRegion ret 120 ∗ logOff img ∗ A.pool ∗ stackAt s.sp tryFromStack
      post := fun (ret, ctPtr, ctext) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          signalMessageResultAt A [] ret (SignalMessage.tryFrom protoSignalCodec ctext) ∗
          (ctPtr ↦ₛ ctext) ∗ logOff img ∗ A.pool ∗ stackAt s0.sp tryFromStack
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## Wrapper Layer Specifications -/

structure OpenGhost where
  outPtr     : BitVec 64
  who        : BitVec 32
  statePtr   : BitVec 64
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  tlsInit    : Option (BitVec 64 × BitVec 64)

def evalOpen (who : BitVec 32) (sess : Session (List (BitVec 8))) :
    Option (Role × Session (List (BitVec 8))) :=
  match Role.ofWho who with
  | some r => some (r, sess)
  | none => none

/-- `libsignal_e2e::open` (`0x43a38..0x43d1c`). -/
def openSpec (A : RustAlloc) (img : Obj.Image) : Spec OpenGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x0 = g.outPtr ∧ s.readReg32 .x1 = g.who ∧
          s.readReg64 .x2 = g.statePtr ∧ (s.readReg64 .x3).toNat = g.stateBytes.length ∧
          g.stateBytes.length < 2 ^ 63 ∧ RecordCanonical g.stateBytes g.sess ∧
          s.spAligned = true ∧ openStack ≤ s.sp.toNat ∧
          ExecOnlyIn (Program.ofImage img) s.mem⌝ ∗
        memRegion g.outPtr 232 ∗ (g.statePtr ↦ₛ g.stateBytes) ∗
        tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗ A.pool ∗ stackAt s.sp openStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          openResultAt A img g.outPtr (evalOpen g.who g.sess) ∗
          (g.statePtr ↦ₛ g.stateBytes) ∗
          (∃∗ tlsFinal, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsFinal) ∗
          A.pool ∗ stackAt s0.sp openStack ∗ anyHeap
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure CloseGhost where
  outPtr  : BitVec 64
  callPtr : BitVec 64
  role    : Role
  sess    : Session (List (BitVec 8))

/-- Inlined `close(c: Call) -> Option<Vec<u8>>` (`send+0x124..+0x198`, `recv+0x12c..+0x1a0`). -/
def closeSpec (A : RustAlloc) (img : Obj.Image) : Spec CloseGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.callPtr ∧
          s.spAligned = true ∧ closeStack ≤ s.sp.toNat⌝ ∗
        memRegion g.outPtr 32 ∗ callAt A img g.callPtr g.role g.sess ∗ A.pool ∗ stackAt s.sp closeStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          serializedVecAt A g.outPtr (encodeRecord ⟨some g.sess⟩) ∗
          memRegion g.callPtr 232 ∗ A.pool ∗ stackAt s0.sp closeStack ∗ anyHeap
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure PackGhost where
  statePtr   : BitVec 64
  stateBytes : List (BitVec 8)
  msgPtr     : BitVec 64
  msgBytes   : List (BitVec 8)

/-- Inlined `pack(state: &[u8], msg: &[u8]) -> *mut u8` (`send+0x198..+0x208`, `recv+0x1a0..+0x210`),
requiring `16 + stateBytes.length + msgBytes.length < 2 ^ 63`. -/
def packSpec (A : RustAlloc) (img : Obj.Image) : Spec PackGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x0 = g.statePtr ∧ (s.readReg64 .x1).toNat = g.stateBytes.length ∧
          s.readReg64 .x2 = g.msgPtr ∧ (s.readReg64 .x3).toNat = g.msgBytes.length ∧
          16 + g.stateBytes.length + g.msgBytes.length < 2 ^ 63 ∧
          s.spAligned = true ∧ packStack ≤ s.sp.toNat⌝ ∗
        (g.statePtr ↦ₛ g.stateBytes) ∗ (g.msgPtr ↦ₛ g.msgBytes) ∗ A.pool ∗ stackAt s.sp packStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          packedOutAt A (sf.readReg64 .x0) g.stateBytes g.msgBytes ∗
          (g.statePtr ↦ₛ g.stateBytes) ∗ (g.msgPtr ↦ₛ g.msgBytes) ∗ A.pool ∗ stackAt s0.sp packStack
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure SendGhost where
  who        : BitVec 32
  statePtr   : BitVec 64
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  ptextPtr   : BitVec 64
  ptextBytes : List (BitVec 8)
  cur        : BitVec 64
  rest       : List (BitVec 8)
  tlsInit    : Option (BitVec 64 × BitVec 64)

/-- Pure outcome of `session_send`. -/
def evalSend (C : Crypto) (S : SpqrModel) (g : SendGhost) :
    Option (List (BitVec 8) × List (BitVec 8) × Nat) :=
  if g.statePtr = 0#64 ∧ g.stateBytes.length ≠ 0 then none
  else if g.ptextPtr = 0#64 ∧ g.ptextBytes.length ≠ 0 then none
  else
    match evalOpen g.who g.sess with
    | none => none
    | some (role, sess) =>
      let (res, calls) := messageEncrypt C protoSignalCodec S.spqr (serializeAddrVal)
        (inMemAnswers sess) g.ptextBytes role.peer.addrVal role.addrVal SystemTime.unixEpoch g.rest
      match res with
      | .ok cm =>
        match unwrapCiphertextBytes cm with
        | some ctBytes =>
          some (Record.encodeRecord ⟨some (storedSession sess calls)⟩, ctBytes, sendDraws S sess g.rest)
        | none => none
      | .error _ => none

/-- `session_send` (`0x47cd8..0x47f20`). -/
def sendSpec (C : Crypto) (A : RustAlloc) (S : SpqrModel) (ctl : BitVec 64)
    (img : Obj.Image) : Spec SendGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg32 .x0 = g.who ∧ s.readReg64 .x1 = g.statePtr ∧
          (s.readReg64 .x2).toNat = g.stateBytes.length ∧ s.readReg64 .x3 = g.ptextPtr ∧
          (s.readReg64 .x4).toNat = g.ptextBytes.length ∧
          g.stateBytes.length < 2 ^ 62 ∧ g.ptextBytes.length < 2 ^ 32 ∧
          g.rest.length < 2 ^ 63 ∧ RecordCanonical g.stateBytes g.sess ∧
          RecordInScope ⟨some g.sess⟩ ∧ RecordPqEmpty ⟨some g.sess⟩ ∧
          (∀ role, Role.ofWho g.who = some role → RoleSessionIds role g.sess) ∧
          s.spAligned = true ∧ sendStack ≤ s.sp.toNat ∧
          ExecOnlyIn (Program.ofImage img) s.mem⌝ ∗
        (g.statePtr ↦ₛ g.stateBytes) ∗ (g.ptextPtr ↦ₛ g.ptextBytes) ∗
        tapeAt ctl g.cur g.rest ∗ logOff img ∗
        StoreNew.tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗ A.pool ∗ stackAt s.sp sendStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace ∧
          (∀ role sess,
            ¬(g.statePtr = 0#64 ∧ g.stateBytes.length ≠ 0) →
            ¬(g.ptextPtr = 0#64 ∧ g.ptextBytes.length ≠ 0) →
            evalOpen g.who g.sess = some (role, sess) →
            (messageEncrypt C protoSignalCodec S.spqr (serializeAddrVal)
              (inMemAnswers sess) g.ptextBytes role.peer.addrVal role.addrVal
              SystemTime.unixEpoch g.rest).1 ≠ .error .panic)⌝ ∗
          (g.statePtr ↦ₛ g.stateBytes) ∗ (g.ptextPtr ↦ₛ g.ptextBytes) ∗
          logOff img ∗ (∃∗ tlsFinal, StoreNew.tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsFinal) ∗
          A.pool ∗ stackAt s0.sp sendStack ∗
          match evalSend C S g with
          | some (stateBytes', ctBytes, draws) =>
            packedOutAt A (sf.readReg64 .x0) stateBytes' ctBytes ∗
              tapeAfter ctl g.cur g.rest draws ∗ anyHeap
          | none =>
            ⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (∃∗ draws : Nat, tapeAfter ctl g.cur g.rest draws) ∗ anyHeap
      onPanic := fun g s0 sf =>
        ⌜(allocFailedIn s0 sf ∨
            ∃ role sess,
              evalOpen g.who g.sess = some (role, sess) ∧
              (messageEncrypt C protoSignalCodec S.spqr (serializeAddrVal)
                (inMemAnswers sess) g.ptextBytes role.peer.addrVal role.addrVal
                SystemTime.unixEpoch g.rest).1 = .error .panic) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure RecvGhost where
  who        : BitVec 32
  statePtr   : BitVec 64
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  ctextPtr   : BitVec 64
  ctextBytes : List (BitVec 8)
  cur        : BitVec 64
  rest       : List (BitVec 8)
  tlsInit    : Option (BitVec 64 × BitVec 64)

/-- Pure outcome of `session_recv`, drawing `recvDraws C sess msg g.rest` RNG bytes. -/
def evalRecv (C : Crypto) (S : SpqrModel) (g : RecvGhost) :
    Option (List (BitVec 8) × List (BitVec 8) × Nat) :=
  if g.statePtr = 0#64 ∧ g.stateBytes.length ≠ 0 then none
  else if g.ctextPtr = 0#64 ∧ g.ctextBytes.length ≠ 0 then none
  else
    match SignalMessage.tryFrom protoSignalCodec g.ctextBytes with
    | .error _ => none
    | .ok msg =>
      match evalOpen g.who g.sess with
      | none => none
      | some (role, sess) =>
        let (res, calls) := messageDecryptSignal C S.spqr (serializeAddrVal)
          (inMemAnswers sess) msg role.peer.addrVal role.addrVal (coinsOf g.rest)
        match res with
        | .ok ptBytes =>
          some (Record.encodeRecord ⟨some (storedSession sess calls)⟩, ptBytes, recvDraws C sess msg g.rest)
        | .error _ => none

/-- `session_recv` (`0x469c8..0x46c20`). -/
def recvSpec (C : Crypto) (A : RustAlloc) (S : SpqrModel) (ctl : BitVec 64)
    (img : Obj.Image) : Spec RecvGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg32 .x0 = g.who ∧ s.readReg64 .x1 = g.statePtr ∧
          (s.readReg64 .x2).toNat = g.stateBytes.length ∧ s.readReg64 .x3 = g.ctextPtr ∧
          (s.readReg64 .x4).toNat = g.ctextBytes.length ∧
          g.stateBytes.length < 2 ^ 62 ∧ g.ctextBytes.length < 2 ^ 32 ∧
          32 ≤ g.rest.length ∧ RecordCanonical g.stateBytes g.sess ∧
          RecordInScope ⟨some g.sess⟩ ∧ RecordPqEmpty ⟨some g.sess⟩ ∧
          (∀ role, Role.ofWho g.who = some role → RoleSessionIds role g.sess) ∧
          s.spAligned = true ∧ recvStack ≤ s.sp.toNat ∧
          ExecOnlyIn (Program.ofImage img) s.mem⌝ ∗
        (g.statePtr ↦ₛ g.stateBytes) ∗ (g.ctextPtr ↦ₛ g.ctextBytes) ∗
        tapeAt ctl g.cur g.rest ∗ logOff img ∗
        StoreNew.tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗ A.pool ∗ stackAt s.sp recvStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace ∧
          (∀ msg role sess,
            ¬(g.statePtr = 0#64 ∧ g.stateBytes.length ≠ 0) →
            ¬(g.ctextPtr = 0#64 ∧ g.ctextBytes.length ≠ 0) →
            SignalMessage.tryFrom protoSignalCodec g.ctextBytes = .ok msg →
            evalOpen g.who g.sess = some (role, sess) →
            (messageDecryptSignal C S.spqr (serializeAddrVal)
              (inMemAnswers sess) msg role.peer.addrVal role.addrVal (coinsOf g.rest)).1 ≠
              .error .panic)⌝ ∗
          (g.statePtr ↦ₛ g.stateBytes) ∗ (g.ctextPtr ↦ₛ g.ctextBytes) ∗
          logOff img ∗ (∃∗ tlsFinal, StoreNew.tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsFinal) ∗
          A.pool ∗ stackAt s0.sp recvStack ∗
          match evalRecv C S g with
          | some (stateBytes', ptBytes, draws) =>
            packedOutAt A (sf.readReg64 .x0) stateBytes' ptBytes ∗
              tapeAfter ctl g.cur g.rest draws ∗ anyHeap
          | none =>
            ⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (∃∗ draws : Nat, tapeAfter ctl g.cur g.rest draws) ∗ anyHeap
      onPanic := fun g s0 sf =>
        ⌜(allocFailedIn s0 sf ∨
            ∃ msg role sess,
              SignalMessage.tryFrom protoSignalCodec g.ctextBytes = .ok msg ∧
              evalOpen g.who g.sess = some (role, sess) ∧
              (messageDecryptSignal C S.spqr (serializeAddrVal)
                (inMemAnswers sess) msg role.peer.addrVal role.addrVal (coinsOf g.rest)).1 =
                .error .panic) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## Pure Model Lemmas for `inMemDecryptSignalSpec` -/

private theorem flatMap_blockToBytesLE_length (cs : List CBC.Block) :
    (cs.flatMap CBC.blockToBytesLE).length = 16 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, CBC.blockToBytesLE,
      List.length_ofFn]
    omega

private theorem cbcDecryptBlocks_length (g : CBC.Block → CBC.Block) (prev : CBC.Block)
    (cs : List CBC.Block) :
    (CBC.cbcDecryptBlocks g prev cs).length = cs.length := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih => simp [CBC.cbcDecryptBlocks, ih]

private theorem pkcs7Unpad_length_le {bs pt : List (BitVec 8)} (h : CBC.pkcs7Unpad bs = some pt) :
    pt.length ≤ bs.length := by
  unfold CBC.pkcs7Unpad at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [List.length_take]
        omega
      · contradiction

theorem aesCbcDecrypt_length_le {D : CBC.AesKey → CBC.Block → CBC.Block}
    {k : CBC.AesKey} {iv : CBC.Block} {ct pt : List (BitVec 8)}
    (hdec : aesCbcDecrypt D k iv ct = some pt) :
    pt.length ≤ ct.length := by
  unfold aesCbcDecrypt CBC.cbcDecRaw at hdec
  split at hdec
  · simp at hdec
  · have hle := pkcs7Unpad_length_le hdec
    rw [flatMap_blockToBytesLE_length, cbcDecryptBlocks_length, CBC.chunks16,
      List.length_ofFn] at hle
    omega

@[local simp] private theorem exec_pure' {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := rfl

@[local simp] private theorem exec_throw' {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

@[local simp] private theorem exec_get' {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

@[local simp] private theorem exec_modify' {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl

@[local simp] private theorem exec_modifyGet' {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

@[local simp] private theorem exec_liftE' {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r) s = (r, s) := by
  cases r <;> rfl

@[local simp] private theorem exec_bind' {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

theorem tripleRatchet_decrypt_pt_length_le {PQ PQC : Type} (C : Crypto) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (msg : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (tr tr' : TripleRatchet PQ) (pt : List (BitVec 8))
    (h : (TripleRatchet.decrypt C spqr expected msg msgType coins).exec tr = (.ok pt, tr')) :
    pt.length ≤ msg.ciphertext.length := by
  unfold TripleRatchet.decrypt at h
  rw [exec_bind'] at h
  rcases h1 : (TripleRatchet.onRatchet (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)).exec tr with ⟨e1 | ck, tr1⟩
  · simp [h1] at h
  · simp only [h1, exec_bind'] at h
    rcases h2 : (TripleRatchet.onRatchet (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType)).exec tr1 with ⟨e2 | mkg, tr2⟩
    · simp [h2] at h
    · simp only [h2, exec_get'] at h
      cases hpan : spqr.recvPanics tr2.pqrState msg.pqRatchet
      case true => simp [hpan] at h
      simp only [hpan, Bool.false_eq_true, ↓reduceIte] at h
      rcases h3 : spqr.recv tr2.pqrState msg.pqRatchet with (_ | _) | ⟨newPqr, pqrKey⟩
      · simp [h3] at h
      · simp [h3] at h
      · simp only [h3, exec_pure', exec_bind'] at h
        split_ifs at h
        · simp at h
        · rcases hdec : aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
              (mkg.generateKeys C.F pqrKey).iv msg.ciphertext with _ | ptext
          · simp [hdec] at h
          · simp [hdec] at h
            rcases h with ⟨rfl, _⟩
            exact aesCbcDecrypt_length_le hdec

theorem tryDecryptFromRecord_pt_length_le {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState PQ) (pt : List (BitVec 8))
    (h : SessionState.tryDecryptFromRecord C spqr expected msg msgType coins st = (.ok pt, st')) :
    pt.length ≤ msg.ciphertext.length := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hdec : (SessionState.tryDecryptWithState C spqr expected msg msgType coins).exec st with ⟨e | ptext, updated⟩
    · simp [hdec] at h
    · rw [hdec] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨rfl, _⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hdec
      simp only [exec_bind', exec_modifyGet', exec_get'] at hdec
      cases hrem : st.remoteIdentity with
      | none => simp [hrem] at hdec
      | some remote =>
        simp only [hrem, exec_pure', exec_liftE'] at hdec
        rcases htr : (TripleRatchet.decrypt C spqr expected msg msgType coins).exec
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
             st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · simp [htr] at hdec
        · simp only [htr, exec_modify', Prod.mk.injEq, Except.ok.injEq] at hdec
          rcases hdec with ⟨rfl, _⟩
          exact tripleRatchet_decrypt_pt_length_le C spqr expected msg msgType coins _ _ pt' htr

theorem messageDecryptSignal_pt_length_le {Addr PQ PQC E : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (ser : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (msg : SignalMessage) (remote loc : Addr) (coins : BitVec 256)
    (pt : List (BitVec 8))
    (h : (messageDecryptSignal C spqr ser answers msg remote loc coins).1 = .ok pt) :
    pt.length ≤ msg.ciphertext.length := by
  rw [messageDecryptSignal_eq_flat] at h
  unfold decryptFlat at h
  rcases hload : answers.loadSession with _ | (_ | record)
  · simp [hload] at h
  · simp [hload] at h
  · simp only [hload] at h
    unfold SessionRecord.tryDecryptFromRecord at h
    rcases hcur : record.currentSession with _ | session
    · simp [hcur] at h
    · simp only [hcur] at h
      rcases hdec : SessionState.tryDecryptFromRecord C spqr (ser remote loc) msg .whisper coins session.state with ⟨ed | ptext, st'⟩
      · simp [hdec] at h
      · simp only [hdec] at h
        have hle := tryDecryptFromRecord_pt_length_le C spqr (ser remote loc) msg .whisper coins session.state st' ptext hdec
        rcases hrem : st'.remoteIdentity with _ | theirKey
        · simp [hrem, Option.bind] at h
        · simp only [hrem, Option.bind] at h
          rcases htr : answers.isTrustedIdentity with _ | (_ | _)
          · simp [htr] at h
          · simp [htr] at h
          · simp only [htr] at h
            rcases hsave : answers.saveIdentity with _ | chg
            · simp [hsave] at h
            · simp only [hsave] at h
              rcases hstore : answers.storeSession with _ | ⟨⟩
              · simp [hstore] at h
              · simp only [hstore, Except.ok.injEq] at h
                subst h
                exact hle

end CryptoVerification.E2E.Bin
