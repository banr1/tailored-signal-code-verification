/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
import LibsignalBinary.Proofs.E2E.Record.Support.Repr -- shake: keep

/-!
# Shared `SessionRecord` Layout and Canonical Protobuf Codec

Fixed E2E party literals (`ALICE`, `BOB`), canonical `storage.proto` encoders (`encodeSession`,
`encodeRecord`), 368-byte in-memory `SessionRecord` representation (`sessionRecordAt`), and
`SessionRecord::{deserialize,serialize}` specifications.
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
export CryptoVerification.E2E.Record (AddrVal OptU32Rel PendingRel KyberRel
  sessionStateReprAt RecordGhost sessionRecordAt RecordInScope RecordPqEmpty RecordRepr InScope)

/-! ## Fixed E2E Party Literals -/

/-- `"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b"` (36 bytes, `.rodata` `0x59ba0`). -/
def aliceNameBytes : List (BitVec 8) :=
  "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b".toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- `"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6"` (36 bytes, `.rodata` `0x59b7c`). -/
def bobNameBytes : List (BitVec 8) :=
  "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6".toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- `ALICE.id_pub[1..33]` (`e2e/src/lib.rs:152–156`, `.rodata` `0x59d48` after `0x05`). -/
def aliceIdPub32 : List (BitVec 8) :=
  [ 0x48#8, 0x3e#8, 0xf1#8, 0x07#8, 0x2a#8, 0xa0#8, 0x66#8, 0x42#8,
    0x4f#8, 0x02#8, 0x3f#8, 0x4b#8, 0x14#8, 0x50#8, 0x7c#8, 0x5f#8,
    0x66#8, 0xa4#8, 0xcd#8, 0xff#8, 0xe8#8, 0xfc#8, 0x3c#8, 0x97#8,
    0x0a#8, 0x95#8, 0x8b#8, 0xd5#8, 0xdb#8, 0xdf#8, 0x9d#8, 0x3e#8 ]

def aliceIdPubBytes : List.Vector (BitVec 8) 32 := ⟨aliceIdPub32, by decide⟩
def aliceIdPubWire : List (BitVec 8) := 0x05#8 :: aliceIdPub32
def aliceIdKey : IdentityKey := ⟨⟨aliceIdPubBytes⟩⟩

/-- `ALICE.id_priv` (`e2e/src/lib.rs:157–161`, `.rodata` `0x59d28`). -/
def aliceIdPrivBytes : List (BitVec 8) :=
  [ 0x70#8, 0xcd#8, 0x22#8, 0x32#8, 0xfd#8, 0xa1#8, 0x4a#8, 0x25#8,
    0xff#8, 0x1d#8, 0x71#8, 0x91#8, 0xc8#8, 0x4b#8, 0x3f#8, 0xa9#8,
    0xf5#8, 0x03#8, 0xda#8, 0x51#8, 0x12#8, 0xc1#8, 0x25#8, 0x0e#8,
    0x98#8, 0x60#8, 0xfe#8, 0x63#8, 0x56#8, 0x46#8, 0x6c#8, 0x47#8 ]

/-- `BOB.id_pub[1..33]` (`e2e/src/lib.rs:167–171`, `.rodata` `0x59ca0` after `0x05`). -/
def bobIdPub32 : List (BitVec 8) :=
  [ 0xce#8, 0x04#8, 0x50#8, 0xdd#8, 0x2f#8, 0x12#8, 0x34#8, 0x24#8,
    0x84#8, 0x52#8, 0xb2#8, 0x37#8, 0x17#8, 0x1b#8, 0x66#8, 0x02#8,
    0x11#8, 0x0f#8, 0x10#8, 0x7c#8, 0x14#8, 0x1f#8, 0xfc#8, 0x0d#8,
    0x19#8, 0x41#8, 0x07#8, 0x08#8, 0x42#8, 0xd7#8, 0xc9#8, 0x3c#8 ]

def bobIdPubBytes : List.Vector (BitVec 8) 32 := ⟨bobIdPub32, by decide⟩
def bobIdPubWire : List (BitVec 8) := 0x05#8 :: bobIdPub32
def bobIdKey : IdentityKey := ⟨⟨bobIdPubBytes⟩⟩

/-- `BOB.id_priv` (`e2e/src/lib.rs:172–176`, `.rodata` `0x59c80`). -/
def bobIdPrivBytes : List (BitVec 8) :=
  [ 0xd8#8, 0x55#8, 0x60#8, 0xbe#8, 0x0c#8, 0xbe#8, 0x21#8, 0xa1#8,
    0xa6#8, 0x4a#8, 0xea#8, 0x46#8, 0xf0#8, 0xb4#8, 0x82#8, 0x36#8,
    0x61#8, 0xc7#8, 0x47#8, 0x29#8, 0xba#8, 0xef#8, 0xa9#8, 0x2e#8,
    0xdf#8, 0xe8#8, 0x85#8, 0xf7#8, 0xb7#8, 0x4e#8, 0x1a#8, 0x74#8 ]

/-! ## Canonical Protobuf Encoding -/

abbrev encodeSession : Session (List (BitVec 8)) → List (BitVec 8) :=
  CryptoVerification.E2E.Record.encSession

abbrev encodeRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8) :=
  CryptoVerification.E2E.Record.encodeRecord

/-! ## In-Memory `Session` and `SessionRecord` Representation -/

def BinCanonSession (G : SessionGhost) (s : Session (List (BitVec 8))) : Prop :=
  CryptoVerification.E2E.Record.Serialization.CanonSession G s ∧
  s.Wf ∧ G.localIk.bytes = s.state.localIdentity.serialize ∧
    (match s.state.remoteIdentity with | none => G.remoteIk.bytes = [] | some ik => G.remoteIk.bytes = ik.serialize) ∧
    (match G.sender, s.state.senderChain with
     | none, none => True | some sg, some sc => sg.srk.bytes = sc.ratchetKey.publicKey.serialize | _, _ => False) ∧
    s.state.receiverChains.length ≤ maxReceiverChains ∧
    (∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys ∧
      ∀ mkg ∈ rc.messageKeys, mkg.seed.length = 32) ∧
    (∀ cg ∈ G.chains, cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []) ∧
    s.aliceBaseKey.length < 2 ^ 32 ∧
    (match s.pendingKyberPreKey with | none => True | some pkp => pkp.ciphertext.length < 2 ^ 32) ∧
    s.state.pqRatchetState.length < 2 ^ 32 ∧ (encodeSession s).length < 2 ^ 62

theorem BinCanonSession.toCanonSession {G : SessionGhost} {s : Session (List (BitVec 8))} :
    BinCanonSession G s → CryptoVerification.E2E.Record.Serialization.CanonSession G s :=
  fun h => h.1

def CanonRecord (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  match g.cur, r.currentSession with | none, none => True | some G, some s => BinCanonSession G s | _, _ => False

abbrev recordDeserializeStack : Nat := 262144
abbrev recordSerializeStack : Nat := num% (page% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignalProtocolStore as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used" + 92))

structure RecordDeserializeGhost where
  ptr : BitVec 64
  s : Session (List (BitVec 8))
  out : BitVec 64

def recordDeserializeSpec (A : RustAlloc) : Spec RecordDeserializeGhost where
  pre := fun x st =>
    let bs := encodeRecord ⟨some x.s⟩
    ⌜st.readReg64 .x0 = x.ptr ∧ (st.readReg64 .x1).toNat = bs.length ∧
      st.readReg64 .x8 = x.out ∧ (∃ G, BinCanonSession G x.s)⌝ ∗
      (x.ptr ↦ₛ bs) ∗ memRegion x.out 0x170 ∗ A.pool ∗ stackAt st.sp recordDeserializeStack
  post := fun x s0 sf =>
    let bs := encodeRecord ⟨some x.s⟩
    ⌜sf.trace = s0.trace⌝ ∗ (x.ptr ↦ₛ bs) ∗
      (∃∗ G : SessionGhost, ⌜BinCanonSession G x.s⌝ ∗
        sessionRecordAt A x.out ⟨0#64, 8#64, some G⟩ ⟨some x.s⟩) ∗
      A.pool ∗ stackAt s0.sp recordDeserializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure RecordSerializeGhost where
  self : BitVec 64
  g : RecordGhost
  r : SessionRecord (List (BitVec 8))
  out : BitVec 64

def recordSerializeSpec (A : RustAlloc) : Spec RecordSerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      CanonRecord x.g x.r ∧ (encodeRecord x.r).length < 2 ^ 32⌝ ∗
      sessionRecordAt A x.self x.g x.r ∗ memRegion x.out 48 ∗
      A.pool ∗ stackAt s.sp recordSerializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionRecordAt A x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecord x.r) ∗
      memRegion (x.out + 32#64) 16 ∗ A.pool ∗ stackAt s0.sp recordSerializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.E2E.Bin
