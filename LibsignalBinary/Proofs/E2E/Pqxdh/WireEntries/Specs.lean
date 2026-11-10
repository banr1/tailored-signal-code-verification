/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP
import GeneratedLean.LibsignalSessionCode -- shake: keep


/-!
# Wrapper-Layer Specifications for `libsignal_pqxdh_e2e` Wire Entries

Defines symbol names, address and `.data.rel.ro`/`.rodata` guards, `InMem` store and `Call` layouts
(`inMemIdentityStoreAtP`, `callAtP`), and subroutine specifications (`packSpecP`, `closeSpecP`,
`openSpecP`, `sendWireSpec`, `recvWireSpec`, `recvWireRejectSpec`) for `libsignal_pqxdh_e2e`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E (partyAddressName partyIdentityKey)
abbrev sendWireName : String := "session_send_wire"
abbrev recvWireName : String := "session_recv_wire"
abbrev encodeRecord := Bin.encodeRecord
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.InMem.HashbrownBin (tableAllocSize sessionBucketStride
  sessionBucketValueOff
  identityBucketStride identityBucketValueOff table4At table4SingleAt identityBucketEntryAt)

/-! ## Symbol Names and Image Offsets -/

abbrev openPqxdhName              : String := "libsignal_pqxdh_e2e::open"
abbrev packPqxdhName              : String := "libsignal_pqxdh_e2e::pack"
abbrev closePqxdhName             : String := "libsignal_pqxdh_e2e::close"
abbrev remoteIdentityKeyBytesName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::remote_identity_key_bytes"
abbrev identityKeyPairTryFromName : String :=
  "<libsignal_protocol::identity_key::IdentityKeyPair as " ++
  "core::convert::TryFrom<libsignal_core::curve::PrivateKey>>::try_from"
abbrev noopWakerClonePqxdhName : String :=
  "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as " ++
  "core::ops::function::FnOnce<(*const (),)>>::call_once [local#3]"
abbrev noopWakerNoopPqxdhName : String :=
  "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#2} as " ++
  "core::ops::function::FnOnce<(*const (),)>>::call_once [local#3]"

abbrev openPqxdhOff              : BitVec 64 := 0x7602c#64
abbrev packPqxdhOff              : BitVec 64 := 0x76364#64
abbrev closePqxdhOff             : BitVec 64 := 0x76420#64
abbrev sendWireOff               : BitVec 64 := 0x78848#64
abbrev recvWireOff               : BitVec 64 := 0x786a0#64
abbrev remoteIdentityKeyBytesOff : BitVec 64 := 0x17c94#64
abbrev identityKeyPairTryFromOff : BitVec 64 := 0x287e8#64
abbrev noopWakerClonePqxdhOff    : BitVec 64 := 0x7738c#64
abbrev noopWakerNoopPqxdhOff     : BitVec 64 := 0x7739c#64

abbrev openPqxdhStack  : Nat := 0x40000 + 0x4b0
abbrev closePqxdhStack : Nat := 0x30000 + 0x330
abbrev packPqxdhStack  : Nat := 0x50 + allocHookStack
abbrev sendWireStack   : Nat := 0x280000
abbrev recvWireStack   : Nat := 0x280000

/-! ## Kernel-Checked Address and Data Guards -/

section AddrGuards
open ProofLib.ProgramReflection
set_option maxRecDepth 2000000

theorem remoteIdentityKeyBytes_fnOff :
    libsignalSessionCode.fnOff remoteIdentityKeyBytesName = 0x17c94 :=
  libsignalSessionCode_fnOff_0x17c94
theorem identityKeyPairTryFrom_fnOff :
    libsignalSessionCode.fnOff identityKeyPairTryFromName = 0x287e8 :=
  libsignalSessionCode_fnOff_0x287e8
end AddrGuards

/-! ## `InMemIdentityKeyStore` and `Call` Layouts -/

/-- 4-bucket `InMemIdentityKeyStore` (`120` B at `out`) for `me : Role` with caller-supplied
64-byte `keyPairBytes` at `+48` and `regId : BitVec 32` at `+112`, holding at most one
`(me.peer.addrVal, peerKey)` entry (`none` = empty `HashMap`, `some peerKey` = single entry). -/
def inMemIdentityStoreAtP (A : RustAlloc) (img : Obj.Image) (out : BitVec 64) (me : Role)
    (keyPairBytes : List (BitVec 8)) (regId : BitVec 32) (opt : Option IdentityKey) : SepProp :=
  ⌜keyPairBytes.length = 64⌝ ∗
  ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
    ((out + 48#64) ↦ₛ keyPairBytes) ∗ ((out + 112#64) ↦₃₂ regId) ∗ memRegion (out + 116#64) 4 ∗
    match opt with
    | none => emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1
    | some ik =>
      ∃∗ idx : Nat, ∃∗ gAddr : AddrGhost,
        ⌜gAddr.val = me.peer.addrVal⌝ ∗
        table4SingleAt A identityBucketStride out k0 k1 idx me.peer.nameBytes 1#8
          (identityBucketEntryAt A gAddr ik.publicKey.bytes.toList)

/-- 232-byte `Call` struct at `callPtr` populated by `libsignal_pqxdh_e2e::open` on a non-empty
session record `⟨some s⟩`:
- `+0x00`: `me : ProtocolAddress` (32 B, `role.addrVal`)
- `+0x20`: `peer : ProtocolAddress` (32 B, `role.peer.addrVal`)
- `+0x40`: `sessions : InMemSessionStore` (48 B, `some s` under `role.peer`)
- `+0x70`: `identities : InMemIdentityKeyStore` (120 B, `some peerKey` under `role.peer` where
  `s.state.remoteIdentity = some peerKey`). -/
def callAtP (A : RustAlloc) (img : Obj.Image) (callPtr : BitVec 64) (role : Role)
    (keyPairBytes : List (BitVec 8)) (regId : BitVec 32)
    (s : Session (List (BitVec 8))) : SepProp :=
  ∃∗ gMe : AddrGhost, ∃∗ gPeer : AddrGhost, ∃∗ peerKey : IdentityKey,
    ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal ∧
      gMe.name.bytes.length = 36 ∧ gPeer.name.bytes.length = 36 ∧
      s.state.remoteIdentity = some peerKey⌝ ∗
    protocolAddressAt A gMe callPtr ∗
    protocolAddressAt A gPeer (callPtr + 0x20#64) ∗
    inMemSessionStoreAt A img (callPtr + 0x40#64) role.peer (some s) ∗
    inMemIdentityStoreAtP A img (callPtr + 0x70#64) role keyPairBytes regId (some peerKey)

/-- 232-byte `Option<Call>` at `outPtr` returned by `libsignal_pqxdh_e2e::open`. -/
def openResultAtP (A : RustAlloc) (img : Obj.Image) (outPtr : BitVec 64)
    (keyPairBytes : List (BitVec 8)) (regId : BitVec 32) :
    Option (Role × Session (List (BitVec 8))) → SepProp
  | some (r, s) => callAtP A img outPtr r keyPairBytes regId s
  | none        => (outPtr ↦₆₄ errTag) ∗ memRegion (outPtr + 8#64) 224

/-! ## Helper Specifications (`packSpecP`, `closeSpecP`, `openSpecP`) -/

/-- `libsignal_pqxdh_e2e::pack(state: &[u8], msg: &[u8]) -> *mut u8` (`0x76280..0x76338`, 47 insns).
Requires `0 < g.stateBytes.length` and `16 + g.stateBytes.length + g.msgBytes.length < 2 ^ 63`. -/
def packSpecP (A : RustAlloc) (img : Obj.Image) : Spec PackGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x0 = g.statePtr ∧ (s.readReg64 .x1).toNat = g.stateBytes.length ∧
          s.readReg64 .x2 = g.msgPtr ∧ (s.readReg64 .x3).toNat = g.msgBytes.length ∧
          0 < g.stateBytes.length ∧
          16 + g.stateBytes.length + g.msgBytes.length < 2 ^ 63 ∧
          s.spAligned = true ∧ packPqxdhStack ≤ s.sp.toNat⌝ ∗
        (g.statePtr ↦ₛ g.stateBytes) ∗ (g.msgPtr ↦ₛ g.msgBytes) ∗
          A.pool ∗ stackAt s.sp packPqxdhStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          packedOutAt A (sf.readReg64 .x0) g.stateBytes g.msgBytes ∗
          (g.statePtr ↦ₛ g.stateBytes) ∗ (g.msgPtr ↦ₛ g.msgBytes) ∗
            A.pool ∗ stackAt s0.sp packPqxdhStack
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

structure CloseGhostP where
  callPtr      : BitVec 64
  role         : Role
  keyPairBytes : List (BitVec 8)
  regId        : BitVec 32
  sess         : Session (List (BitVec 8))

/-- `libsignal_pqxdh_e2e::close(c: &Call) -> Option<&'static [u8]>` (`0x7633c..0x4f4b8`, 47 insns).
Loads `c.sessions[&c.peer]`, serializes the `SessionRecord`, leaks the resulting `Vec<u8>`,
and returns `(x0 = ptr ≠ 0, x1 = (encodeRecord ⟨some g.sess⟩).length)`
with `(x0 ↦ₛ encodeRecord ⟨some g.sess⟩)`. -/
def closeSpecP (A : RustAlloc) (img : Obj.Image) : Spec CloseGhostP :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x0 = g.callPtr ∧
          RecordInScope ⟨some g.sess⟩ ∧
          (encodeRecord ⟨some g.sess⟩).length < 2 ^ 32 ∧
          s.spAligned = true ∧ closePqxdhStack ≤ s.sp.toNat ∧
          ExecOnlyIn (Program.ofImage img) s.mem⌝ ∗
        callAtP A img g.callPtr g.role g.keyPairBytes g.regId g.sess ∗
        A.pool ∗ stackAt s.sp closePqxdhStack
      post := fun g s0 sf =>
        let bs := encodeRecord ⟨some g.sess⟩
        ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          (sf.readReg64 .x1).toNat = bs.length⌝ ∗
          (sf.readReg64 .x0 ↦ₛ bs) ∗
          callAtP A img g.callPtr g.role g.keyPairBytes g.regId g.sess ∗
          A.pool ∗ stackAt s0.sp closePqxdhStack ∗ anyHeap
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- `<SessionRecord>::remote_identity_key_bytes` (`0x17c94..0x17e10`, 95 insns):
reads `sess.state.remoteIdentity = some peerKey`, serializes `peerKey.publicKey` as 33 bytes
`0x05 :: peerKey.publicKey.bytes.toList`, allocates a 33-byte `Vec<u8>`, and writes
`Ok(Some(vec))` (`[out] = -2`, `vecU8 A (out + 8) (0x05 :: peerKey.publicKey.bytes.toList)`)
at `x8 = out`. -/
def remoteIdentityKeyBytesSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) × IdentityKey) where
  pre := fun (recPtr, out, G, sess, peerKey) s =>
    ⌜s.readReg64 .x0 = recPtr ∧ s.readReg64 .x8 = out ∧
      BinCanonSession G sess ∧ sess.state.remoteIdentity = some peerKey⌝ ∗
      sessionRecordAt A recPtr ⟨0#64, 8#64, some G⟩ ⟨some sess⟩ ∗
      memRegion out 32 ∗ logOff img ∗ A.pool ∗ stackAt s.sp (128 + publicKeySerializeStack)
  post := fun (recPtr, out, G, sess, peerKey) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionRecordAt A recPtr ⟨0#64, 8#64, some G⟩ ⟨some sess⟩ ∗
      (out ↦₆₄ okTagVec) ∗
      vecU8 A (out + 8#64) (0x05#8 :: peerKey.publicKey.bytes.toList) ∗
      logOff img ∗ A.pool ∗ stackAt s0.sp (128 + publicKeySerializeStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def identityKeyDecodeAnySpec : Spec (BitVec 64 × BitVec 64 × IdentityKey) where
  pre := fun (ret, keyPtr, ik) s =>
    ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = keyPtr ∧ s.readReg64 .x1 = 33#64⌝ ∗
      (keyPtr ↦ₛ (0x05#8 :: ik.publicKey.bytes.toList)) ∗ memRegion ret 40 ∗ stackAt s.sp 0x60
  post := fun (ret, keyPtr, ik) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (keyPtr ↦ₛ (0x05#8 :: ik.publicKey.bytes.toList)) ∗
      (ret ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((ret + 8#64) ↦ₛ ik.publicKey.bytes.toList) ∗ stackAt s0.sp 0x60

/-- Generalized `<InMemIdentityKeyStore>::new` (`0x0c238`) for arbitrary 64-byte
`keyPairBytes` and `regId : BitVec 32`. -/
def identityStoreNewAnySpec (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 32 × Option (BitVec 64 × BitVec 64)) :=
  Spec.inImage
    { pre := fun (out, kpPtr, keyPairBytes, regId, st) s =>
        ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = kpPtr ∧ s.readReg32 .x1 = regId ∧
          keyPairBytes.length = 64⌝ ∗
          memRegion out 120 ∗ (kpPtr ↦ₛ keyPairBytes) ∗
          tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) st ∗ stackAt s.sp (0x30 + extHookStack)
      post := fun (out, kpPtr, keyPairBytes, regId, _) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
            emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 keyPairBytes regId ∗
              tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
          (kpPtr ↦ₛ keyPairBytes) ∗ stackAt s0.sp (0x30 + extHookStack) }
    img

/-- Generalized `InMemIdentityKeyStore::save_identity` (`0x2ddc0`) + `poll_once` for arbitrary
`keyPairBytes`, `regId`, and `peerKey : IdentityKey`. -/
def inMemSaveIdentityAnySpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × AddrGhost × Role ×
      List (BitVec 8) × BitVec 32 × IdentityKey) :=
  Spec.inImage
    { pre := fun (self, addrPtr, keyPtr, pollOut, gPeer, me, keyPairBytes, regId, peerKey) s =>
        ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x1 = addrPtr ∧ s.readReg64 .x2 = keyPtr ∧
          s.readReg64 .x8 = pollOut ∧ gPeer.val = me.peer.addrVal⌝ ∗
          inMemIdentityStoreAtP A img self me keyPairBytes regId none ∗
          protocolAddressAt A gPeer addrPtr ∗
          (keyPtr ↦ₛ peerKey.publicKey.bytes.toList) ∗ memRegion pollOut 48 ∗
          A.pool ∗ stackAt s.sp (0x800 + extHookStack)
      post := fun (self, addrPtr, keyPtr, pollOut, gPeer, me, keyPairBytes, regId, peerKey) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          inMemIdentityStoreAtP A img self me keyPairBytes regId (some peerKey) ∗
          protocolAddressAt A gPeer addrPtr ∗
          (keyPtr ↦ₛ peerKey.publicKey.bytes.toList) ∗
          (pollOut ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (pollOut + 8#64) 40 ∗
          A.pool ∗ stackAt s0.sp (0x800 + extHookStack)
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Derive the 64-byte `IdentityKeyPair` representation (`pub[32] ++ clamped_priv[32]`) from a
36-byte `me` slice (`id_priv[32] ‖ reg_id:u32`). -/
def meKeyPairBytes (pubKey : PubKeyFn) (meBytes : List (BitVec 8)) : List (BitVec 8) :=
  if h : (meBytes.take 32).length = 32 then
    let sk := Ratchet.clampScalar ⟨meBytes.take 32, h⟩
    (pubKey sk).toList ++ sk.toList
  else List.replicate 64 0#8

theorem meKeyPairBytes_length (pubKey : PubKeyFn) (meBytes : List (BitVec 8)) :
    (meKeyPairBytes pubKey meBytes).length = 64 := by
  unfold meKeyPairBytes
  split_ifs with h <;> simp

/-- Extract the 32-bit little-endian registration id from `me[32..36]`. -/
def meRegId (meBytes : List (BitVec 8)) : BitVec 32 :=
  let b0 := meBytes.getD 32 0#8
  let b1 := meBytes.getD 33 0#8
  let b2 := meBytes.getD 34 0#8
  let b3 := meBytes.getD 35 0#8
  b3 ++ b2 ++ b1 ++ b0

structure OpenGhostP where
  outPtr     : BitVec 64
  who        : BitVec 32
  mePtr      : BitVec 64
  meBytes    : List (BitVec 8)
  statePtr   : BitVec 64
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  tlsInit    : Option (BitVec 64 × BitVec 64)

/-- Canonical encoding predicate for `SessionRecord::deserialize` (`0x16ed4`) in `open` under
`RecordX.DeserializeScopeP`. -/
def RecordCanonical (stateBytes : List (BitVec 8)) (s : Session (List (BitVec 8))) : Prop :=
  stateBytes = encodeRecord ⟨some s⟩ ∧
    RecordX.DeserializeScopeP ⟨some s⟩ ∧ ∃ G, BinCanonSession G s

theorem recordCanonical_length_pos {bs : List (BitVec 8)} {s : Session (List (BitVec 8))}
    (h : RecordCanonical bs s) : 0 < bs.length := by
  rcases h with ⟨rfl, _⟩
  simp only [encodeRecord, Bin.encodeRecord, CryptoVerification.E2E.Record.encodeRecord,
    CryptoVerification.E2E.Record.msgField, CryptoVerification.E2E.Record.lenField,
    Option.map_some, List.length_append]
  have : 0 < (encodeKey 1 WireType.lengthDelimited).length := by decide
  omega

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

/-- `libsignal_pqxdh_e2e::open(who, me, state)` (`0x75f48..0x7627c`, 206 insns) on a non-empty
canonical session record `stateBytes = encodeRecord ⟨some sess⟩`
with `sess.state.remoteIdentity.isSome`. -/
def openSpecP (C : Crypto) (A : RustAlloc) (img : Obj.Image) : Spec OpenGhostP :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x0 = g.outPtr ∧ s.readReg32 .x1 = g.who ∧
          s.readReg64 .x2 = g.mePtr ∧ s.readReg64 .x3 = 36#64 ∧
          g.meBytes.length = 36 ∧
          s.readReg64 .x4 = g.statePtr ∧ (s.readReg64 .x5).toNat = g.stateBytes.length ∧
          g.stateBytes.length < 2 ^ 63 ∧ RecordCanonical g.stateBytes g.sess ∧
          g.sess.state.remoteIdentity.isSome ∧
          s.spAligned = true ∧ openPqxdhStack ≤ s.sp.toNat ∧
          ExecOnlyIn (Program.ofImage img) s.mem⌝ ∗
        memRegion g.outPtr 232 ∗ (g.mePtr ↦ₛ g.meBytes) ∗ (g.statePtr ↦ₛ g.stateBytes) ∗
        logOff img ∗ tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗
          A.pool ∗ stackAt s.sp openPqxdhStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          openResultAtP A img g.outPtr (meKeyPairBytes C.pubKey g.meBytes) (meRegId g.meBytes)
            (evalOpen g.who g.sess) ∗
          (g.mePtr ↦ₛ g.meBytes) ∗ (g.statePtr ↦ₛ g.stateBytes) ∗
          logOff img ∗ (∃∗ tlsFinal, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsFinal) ∗
          A.pool ∗ stackAt s0.sp openPqxdhStack ∗ anyHeap
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## `inMemEncryptSpecP` and `inMemDecryptSignalSpecP` -/

/-- `CiphertextMessage` wire tag and inner serialized bytes for `session_send_wire`
(`pqxdh/src/lib.rs:403–407`):
- `SignalMessage sm` -> `(2#8, sm.serialized)` (`WIRE_WHISPER`),
- `PreKeySignalMessage psm` -> `(3#8, psm.serialized)` (`WIRE_PREKEY`). -/
def unwrapWireCiphertext : CiphertextMessage → BitVec 8 × List (BitVec 8)
  | .signalMessage sm => (2#8, sm.serialized)
  | .preKeySignalMessage psm => (3#8, psm.serialized)

/-- 248-byte `Result<CiphertextMessage, SignalProtocolError>` at `ret`
(`sp + 0xf8` in `session_send_wire`):
- `.ok (.signalMessage sm)`: word 0 = `0x8000000000000000#64`, `sm` at `ret + 8`
  (`sm.serialized` at `ret + 0x30`),
- `.ok (.preKeySignalMessage psm)`: word 0 `w` with `w.toNat < 2 ^ 63`,
  `psm.serialized` at `ret + 0x80`,
- `.error _`: word 0 = `0xffffffffffffffff#64` (`errTag`). -/
def apiEncResultAtWire (A : RustAlloc) (ret : BitVec 64) :
    Except (ApiError AddrVal Unit) CiphertextMessage → SepProp
  | .ok (.signalMessage sm) =>
    (ret ↦₆₄ 0x8000000000000000#64) ∗
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (ret + 8#64) sm) ∗
      memRegion (ret + 128#64) 120
  | .ok (.preKeySignalMessage psm) =>
    (∃∗ w : BitVec 64, ⌜w.toNat < 2 ^ 63⌝ ∗ (ret ↦₆₄ w)) ∗ memRegion (ret + 8#64) 120 ∗
      (∃∗ serPtr : BitVec 64, boxU8At A (ret + 0x80#64) serPtr psm.serialized) ∗
      memRegion (ret + 0x90#64) 104 ∗ anyHeap
  | .error _ =>
    (ret ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (ret + 8#64) 240 ∗ anyHeap

/-! ## Top-Level Wire Entry Specifications (`sendWireSpec`, `recvWireSpec`, `recvWireRejectSpec`) -/

structure SendWireGhost where
  who        : BitVec 32
  aPtr       : BitVec 64
  meBytes    : List (BitVec 8)
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  ptextPtr   : BitVec 64
  ptextBytes : List (BitVec 8)
  cur        : BitVec 64
  rest       : List (BitVec 8)
  tlsInit    : Option (BitVec 64 × BitVec 64)

/-- Pure outcome of `session_send_wire`: encrypts `g.ptextBytes`, prepends the 1-byte wire tag
(`2` for `SignalMessage`, `3` for `PreKeySignalMessage`), and packs `(new_state, tag :: body)`. -/
def evalSendWire (C : Crypto) (S : SpqrModel) (_uuidParse : UuidParser) (g : SendWireGhost) :
    Option (List (BitVec 8) × List (BitVec 8) × Nat) :=
  if g.aPtr = 0#64 then none
  else if g.ptextPtr = 0#64 ∧ g.ptextBytes.length ≠ 0 then none
  else
    match evalOpen g.who g.sess with
    | none => none
    | some (role, sess) =>
      let (res, calls) := messageEncrypt C protoSignalCodec S.spqr (serializeAddrVal)
        (inMemAnswers sess) g.ptextBytes role.peer.addrVal role.addrVal SystemTime.unixEpoch g.rest
      match res with
      | .ok cm =>
        let (tag, body) := unwrapWireCiphertext cm
        some (Record.encodeRecord ⟨some (storedSession sess calls)⟩,
          tag :: body, sendDraws S sess g.rest)
      | .error _ => none

def sendWireSpec (C : Crypto) (A : RustAlloc) (S : SpqrModel) (ctl : BitVec 64)
    (_uuidParse : UuidParser) (img : Obj.Image) : Spec SendWireGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg32 .x0 = g.who ∧ s.readReg64 .x1 = g.aPtr ∧
          (s.readReg64 .x2).toNat = 36 + g.stateBytes.length ∧
          g.meBytes.length = 36 ∧
          s.readReg64 .x3 = g.ptextPtr ∧ (s.readReg64 .x4).toNat = g.ptextBytes.length ∧
          g.stateBytes.length < 2 ^ 62 ∧ g.ptextBytes.length < 2 ^ 32 ∧
          g.rest.length < 2 ^ 63 ∧ RecordCanonical g.stateBytes g.sess ∧
          RecordInScope ⟨some g.sess⟩ ∧ RecordPqEmpty ⟨some g.sess⟩ ∧
          g.sess.state.remoteIdentity.isSome ∧
          s.spAligned = true ∧ sendWireStack ≤ s.sp.toNat ∧
          ExecOnlyIn (Program.ofImage img) s.mem⌝ ∗
        (g.aPtr ↦ₛ (g.meBytes ++ g.stateBytes)) ∗ (g.ptextPtr ↦ₛ g.ptextBytes) ∗
        tapeAt ctl g.cur g.rest ∗ logOff img ∗
        StoreNew.tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗
          A.pool ∗ stackAt s.sp sendWireStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace ∧
          (∀ role sess,
            g.aPtr ≠ 0#64 →
            ¬(g.ptextPtr = 0#64 ∧ g.ptextBytes.length ≠ 0) →
            evalOpen g.who g.sess = some (role, sess) →
            (messageEncrypt C protoSignalCodec S.spqr (serializeAddrVal)
              (inMemAnswers sess) g.ptextBytes role.peer.addrVal role.addrVal
              SystemTime.unixEpoch g.rest).1 ≠ .error .panic)⌝ ∗
          (g.aPtr ↦ₛ (g.meBytes ++ g.stateBytes)) ∗ (g.ptextPtr ↦ₛ g.ptextBytes) ∗
          logOff img ∗ (∃∗ tlsFinal, StoreNew.tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsFinal) ∗
          A.pool ∗ stackAt s0.sp sendWireStack ∗
          match evalSendWire C S _uuidParse g with
          | some (stateBytes', wireBytes, draws) =>
            packedOutAt A (sf.readReg64 .x0) stateBytes' wireBytes ∗
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

structure RecvWireGhost where
  who        : BitVec 32
  aPtr       : BitVec 64
  meBytes    : List (BitVec 8)
  stateBytes : List (BitVec 8)
  sess       : Session (List (BitVec 8))
  wirePtr    : BitVec 64
  wireBytes  : List (BitVec 8)
  cur        : BitVec 64
  rest       : List (BitVec 8)
  tlsInit    : Option (BitVec 64 × BitVec 64)

/-- Pure outcome of `session_recv_wire`: requires `wireBytes = 2#8 :: body`, parses `body` as a
`SignalMessage`, decrypts it via `messageDecryptSignal`, and packs `(new_state, ptBytes)`. -/
def evalRecvWire (C : Crypto) (S : SpqrModel) (_uuidParse : UuidParser) (g : RecvWireGhost) :
    Option (List (BitVec 8) × List (BitVec 8) × Nat) :=
  if g.aPtr = 0#64 then none
  else if g.wirePtr = 0#64 ∧ g.wireBytes.length ≠ 0 then none
  else
    match g.wireBytes with
    | 2#8 :: body =>
      match SignalMessage.tryFrom protoSignalCodec body with
      | .error _ => none
      | .ok msg =>
        match evalOpen g.who g.sess with
        | none => none
        | some (role, sess) =>
          let (res, calls) := messageDecryptSignal C S.spqr (serializeAddrVal)
            (inMemAnswers sess) msg role.peer.addrVal role.addrVal (coinsOf g.rest)
          match res with
          | .ok ptBytes =>
            some (Record.encodeRecord ⟨some (storedSession sess calls)⟩,
              ptBytes, recvDraws C sess msg g.rest)
          | .error _ => none
    | _ => none

def recvWireSpec (C : Crypto) (A : RustAlloc) (S : SpqrModel) (ctl : BitVec 64)
    (_uuidParse : UuidParser) (img : Obj.Image) : Spec RecvWireGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg32 .x0 = g.who ∧ s.readReg64 .x1 = g.aPtr ∧
          (s.readReg64 .x2).toNat = 36 + g.stateBytes.length ∧
          g.meBytes.length = 36 ∧
          s.readReg64 .x3 = g.wirePtr ∧ (s.readReg64 .x4).toNat = g.wireBytes.length ∧
          g.stateBytes.length < 2 ^ 62 ∧ g.wireBytes.length < 2 ^ 32 ∧
          32 ≤ g.rest.length ∧ RecordCanonical g.stateBytes g.sess ∧
          RecordInScope ⟨some g.sess⟩ ∧ RecordPqEmpty ⟨some g.sess⟩ ∧
          g.sess.state.remoteIdentity.isSome ∧
          s.spAligned = true ∧ recvWireStack ≤ s.sp.toNat ∧
          ExecOnlyIn (Program.ofImage img) s.mem⌝ ∗
        (g.aPtr ↦ₛ (g.meBytes ++ g.stateBytes)) ∗ (g.wirePtr ↦ₛ g.wireBytes) ∗
        tapeAt ctl g.cur g.rest ∗ logOff img ∗
        StoreNew.tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) g.tlsInit ∗
          A.pool ∗ stackAt s.sp recvWireStack
      post := fun g s0 sf =>
        ⌜sf.trace = s0.trace ∧
          (∀ body msg role sess,
            g.aPtr ≠ 0#64 →
            ¬(g.wirePtr = 0#64 ∧ g.wireBytes.length ≠ 0) →
            g.wireBytes = 2#8 :: body →
            SignalMessage.tryFrom protoSignalCodec body = .ok msg →
            evalOpen g.who g.sess = some (role, sess) →
            (messageDecryptSignal C S.spqr (serializeAddrVal)
              (inMemAnswers sess) msg role.peer.addrVal role.addrVal (coinsOf g.rest)).1 ≠
              .error .panic)⌝ ∗
          (g.aPtr ↦ₛ (g.meBytes ++ g.stateBytes)) ∗ (g.wirePtr ↦ₛ g.wireBytes) ∗
          logOff img ∗ (∃∗ tlsFinal, StoreNew.tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsFinal) ∗
          A.pool ∗ stackAt s0.sp recvWireStack ∗
          match evalRecvWire C S _uuidParse g with
          | some (stateBytes', ptBytes, draws) =>
            packedOutAt A (sf.readReg64 .x0) stateBytes' ptBytes ∗
              tapeAfter ctl g.cur g.rest draws ∗ anyHeap
          | none =>
            ⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (∃∗ draws : Nat, tapeAfter ctl g.cur g.rest draws) ∗ anyHeap
      onPanic := fun g s0 sf =>
        ⌜(allocFailedIn s0 sf ∨
            ∃ body msg role sess,
              g.wireBytes = 2#8 :: body ∧
              SignalMessage.tryFrom protoSignalCodec body = .ok msg ∧
              evalOpen g.who g.sess = some (role, sess) ∧
              (messageDecryptSignal C S.spqr (serializeAddrVal)
                (inMemAnswers sess) msg role.peer.addrVal role.addrVal (coinsOf g.rest)).1 =
                .error .panic) ∧
          s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- Tag-2 rejection specification for `session_recv_wire` (`0x785bc..0x51688`, `0x517e4..0x517e8`):
when `wireBytes.head? ≠ some 2#8` (for arbitrary `a` and `who`), `session_recv_wire` immediately
returns `x0 = 0` without touching the stack, heap, or RNG tape (`PqxdhRejects` conjunct 3). -/
def recvWireRejectSpec (img : Obj.Image) : Spec (BitVec 64 × List (BitVec 8)) :=
  Spec.inImage
    { pre := fun (wirePtr, wireBytes) s =>
        ⌜s.readReg64 .x3 = wirePtr ∧ (s.readReg64 .x4).toNat = wireBytes.length ∧
          wireBytes.length < 2 ^ 64 ∧ wireBytes.head? ≠ some 2#8⌝ ∗
        (wirePtr ↦ₛ wireBytes)
      post := fun (wirePtr, wireBytes) s0 sf =>
        ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ (wirePtr ↦ₛ wireBytes) }
    img

end CryptoVerification.E2E.Pqxdh.WireEntries
