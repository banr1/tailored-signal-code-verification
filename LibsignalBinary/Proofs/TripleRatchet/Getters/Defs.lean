/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Specifications for Identity Getters, `is_same_account`, `clear_unacknowledged_pre_key_message`, and Drop Glue

Defines symbol names, stack budgets, ghost states, and fixed-image / relocatable `[LibsignalPlacement]`
contracts for:
1. `<SessionState>::local_identity_key` (`0x119f4`) and `remote_identity_key` (`0x11b04`)
2. `<SessionState>::clear_unacknowledged_pre_key_message` (`0x12404`)
3. `<IdentityKey>::is_same_account` (`0xacec`) and `<PublicKey as PartialEq>::eq` (`0x3ebf0`)
4. `drop_glue` for `session_structure::Chain` (`0x35dc8`), `Vec<chain::MessageKey>` (`0x1f28`),
   `Vec<session_structure::Chain>` (`0x1e74`), and `SignalProtocolError` (`0x2374`)
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Symbol names -/

/-- `<libsignal_protocol::state::session::SessionState>::local_identity_key` (image offset `0x119f4`). -/
abbrev localIdentityKeyName : String :=
  "<libsignal_protocol::state::session::SessionState>::local_identity_key"

/-- `<libsignal_protocol::state::session::SessionState>::remote_identity_key` (image offset `0x11b04`). -/
abbrev remoteIdentityKeyName : String :=
  "<libsignal_protocol::state::session::SessionState>::remote_identity_key"

/-- `<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message` (image offset `0x12404`). -/
abbrev clearUpkName : String :=
  "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message"

/-- `<libsignal_protocol::identity_key::IdentityKey>::is_same_account` (image offset `0xacec`). -/
abbrev isSameAccountName : String :=
  "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"

/-- `core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain>` (image offset `0x35dc8`). -/
abbrev dropChainName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#1]"

/-- `core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>` (image offset `0x1f28`). -/
abbrev dropVecMessageKeyName : String :=
  "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"

/-- `core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>` (image offset `0x1e74`). -/
abbrev dropVecChainName : String :=
  "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"

/-- `core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError>` (image offset `0x2374`). -/
abbrev dropSpeName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]"

/-- Base-program `<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq` (image offset `0x3ebf0`). -/
abbrev publicKeyEqName : String :=
  "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"

/-! ## Stack budgets -/

/-- Own frame of `local_identity_key` (`0x119f4: sub sp, sp, #0x50` = 80 B; `pkTryFromHook` is a leaf hook). -/
abbrev localIdentityKeyStack : Nat := 80

/-- Own frame of `remote_identity_key` (`0x11b04: sub sp, sp, #0x90` = 144 B; `pkTryFromHook` is a leaf hook). -/
abbrev remoteIdentityKeyStack : Nat := 144

/-- Own frame of `clear_unacknowledged_pre_key_message` (`0x12404: stp x29, x30, [sp, #-32]!` = 32 B)
plus `allocHookStack` (4096 B) for `__rust_dealloc` (`+0x024`, `+0x044`). -/
abbrev clearUpkStack : Nat := 32 + allocHookStack

/-- Own frame of `is_same_account` (`0xacec: sub sp, sp, #0x50` = 80 B) plus `PublicKey::eq` (16 B)
and `ct_eq` (48 B) at `+0x020`. -/
abbrev isSameAccountStack : Nat := 80 + 64

/-- Own frame of `drop_glue<Chain>` (`0x35dc8: stp x29, x30, [sp, #-48]!` = 48 B)
plus `allocHookStack` (4096 B) for `__rust_dealloc` (`+0x024`, `+0x038`, `+0x050`, `+0x080`,
`+0x094`, `+0x0a8`, `+0x0bc`, and tail `b` at `+0x0e8`). -/
abbrev dropChainStack : Nat := 48 + allocHookStack

/-- Own frame of `drop_glue<Vec<MessageKey>>` (`0x1f28: stp x29, x30, [sp, #-48]!` = 48 B)
plus `allocHookStack` (4096 B) for `__rust_dealloc` (`+0x040`, `+0x054`, `+0x068`, `+0x07c`,
and tail `b` at `+0x0a8`). -/
abbrev dropVecMessageKeyStack : Nat := 48 + allocHookStack

/-- Own frame of `drop_glue<Vec<Chain>>` (`0x1e74: stp x29, x30, [sp, #-48]!` = 48 B)
plus `dropVecMessageKeyStack` (48 + 4096 B) for `bl drop_glue<Vec<MessageKey>>` at `+0x028`
(and `__rust_dealloc` at `+0x048`, `+0x05c`, `+0x074`, tail `b` at `+0x0a0`). -/
abbrev dropVecChainStack : Nat := 48 + dropVecMessageKeyStack

/-- Own frame of `drop_glue<SignalProtocolError>` (`0x2374: stp x29, x30, [sp, #-32]!` = 32 B)
plus `allocHookStack` (4096 B) for the tail call `b __rust_dealloc` at `+0x058`. -/
abbrev dropSpeStack : Nat := 32 + allocHookStack

/-- Own frame of `drop_glue<Chain>` (48 B) plus `extHookStack` (16384 B) under `AllocContractsX`. -/
abbrev dropChainStackX : Nat := 48 + extHookStack

/-- Own frame of `drop_glue<SignalProtocolError>` (32 B) plus `extHookStack` (16384 B) under `AllocContractsX`. -/
abbrev dropSpeStackX : Nat := 32 + extHookStack

/-! ## 1. `SessionState::local_identity_key` (`0x119f4`, 68 insns) -/

/-- Ghost arguments `(ss, g, ik, ret)` for `<SessionState>::local_identity_key` (`0x119f4`). -/
structure LocalIdentityKeyGhost where
  /-- `self: &SessionState` (`x0`). -/
  ss : BitVec 64
  /-- `local_identity_public` `Vec<u8>` ghost at `ss + 0`. -/
  g : VecGhost
  /-- Decoded `IdentityKey` (`SessionState.localIdentity`). -/
  ik : IdentityKey
  /-- Sret buffer (`x8`, 33 bytes written on `Ok`). -/
  ret : BitVec 64

/-- Sret layout of `Result<IdentityKey, InvalidSessionError>::Ok(ik)` at `ret` (33 bytes):
tag `0#8` at `ret + 0` and 32-byte public key at `ret + 1 .. ret + 33`. -/
def localIdentityOkAt (ret : BitVec 64) (ik : IdentityKey) : SepProp :=
  (ret ↦₈ 0#8) ∗ ((ret + 1#64) ↦ₛ ik.publicKey.bytes.toList)

/-- Specification of `<SessionState>::local_identity_key` (`0x119f4`): deserializes
`local_identity_public` (`PublicKey.deserialize g.bytes = .ok ik.publicKey`), writes
`localIdentityOkAt x.ret x.ik`, and preserves `vecGhostAt A x.g x.ss`. -/
def localIdentityKeySpec (A : RustAlloc) (img : Obj.Image) : Spec LocalIdentityKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret ∧
      PublicKey.deserialize x.g.bytes = .ok x.ik.publicKey⌝ ∗
      vecGhostAt A x.g x.ss ∗ memRegion x.ret 33 ∗ logOff img ∗ stackAt s.sp localIdentityKeyStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecGhostAt A x.g x.ss ∗ localIdentityOkAt x.ret x.ik ∗ logOff img ∗
      stackAt s0.sp localIdentityKeyStack

/-! ## 2. `SessionState::remote_identity_key` (`0x11b04`, 101 insns) -/

/-- Ghost arguments `(ss, g, rem, ret)` for `<SessionState>::remote_identity_key` (`0x11b04`). -/
structure RemoteIdentityKeyGhost where
  /-- `self: &SessionState` (`x0`). -/
  ss : BitVec 64
  /-- `remote_identity_public` `Vec<u8>` ghost at `ss + 0x18`. -/
  g : VecGhost
  /-- Decoded `Option IdentityKey` (`SessionState.remoteIdentity`). -/
  rem : Option IdentityKey
  /-- Sret buffer (`x8`, 34 bytes). -/
  ret : BitVec 64

/-- Sret layout of `Result<Option<IdentityKey>, InvalidSessionError>::Ok(rem)` at `ret` (34 bytes):
- `none`: bytes `0..2` equal `0#8, 0#8`, bytes `2..34` unspecified (`memRegion`);
- `some ik`: bytes `0..2` equal `0#8, 1#8`, key bytes at `ret + 2 .. ret + 34`. -/
def remoteIdentityOkAt (ret : BitVec 64) : Option IdentityKey → SepProp
  | none => (ret ↦₈ 0#8) ∗ ((ret + 1#64) ↦₈ 0#8) ∗ memRegion (ret + 2#64) 32
  | some ik => (ret ↦₈ 0#8) ∗ ((ret + 1#64) ↦₈ 1#8) ∗ ((ret + 2#64) ↦ₛ ik.publicKey.bytes.toList)

/-- Specification of `<SessionState>::remote_identity_key` (`0x11b04`): returns `Ok(None)` when
`remote_identity_public` is empty, or deserializes `ik` and writes `remoteIdentityOkAt x.ret x.rem`
while preserving `vecGhostAt A x.g (x.ss + 0x18#64)`. -/
def remoteIdentityKeySpec (A : RustAlloc) (img : Obj.Image) : Spec RemoteIdentityKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret ∧
      (match x.rem with
       | none => x.g.bytes = []
       | some ik => PublicKey.deserialize x.g.bytes = .ok ik.publicKey)⌝ ∗
      vecGhostAt A x.g (x.ss + 0x18#64) ∗ memRegion x.ret 34 ∗ logOff img ∗
      stackAt s.sp remoteIdentityKeyStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecGhostAt A x.g (x.ss + 0x18#64) ∗ remoteIdentityOkAt x.ret x.rem ∗ logOff img ∗
      stackAt s0.sp remoteIdentityKeyStack

/-! ## 3. `SessionState::clear_unacknowledged_pre_key_message` (`0x12404`, 22 insns) -/

/-- Ghost arguments `(ss, G, st)` for `<SessionState>::clear_unacknowledged_pre_key_message`. -/
structure ClearUpkGhost where
  /-- `self: &mut SessionState` (`x0`). -/
  ss : BitVec 64
  /-- Session ghost layout (`pending` at `ss + 0xf8`, `kyber` at `ss + 0x128`). -/
  G : SessionGhost
  /-- `SessionState` model value. -/
  st : SessionState (List (BitVec 8))

/-- Specification of `<SessionState>::clear_unacknowledged_pre_key_message` (`0x12404`):
deallocates `pending_pre_key.base_key` (`ss + 0xf8`) and `pending_kyber_pre_key.ciphertext`
(`ss + 0x128`) when present, sets both niche capacities to `-1`, and establishes `sessionStateAt`
for `st.clearUnacknowledgedPreKeyMessage` with `{ G with pending := none, kyber := none }`. -/
def clearUpkSpec (A : RustAlloc) : Spec ClearUpkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp clearUpkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionStateAt A x.ss { x.G with pending := none, kyber := none }
        x.st.clearUnacknowledgedPreKeyMessage ∗
      A.pool ∗ stackAt s0.sp clearUpkStack

/-! ## 4. `IdentityKey::is_same_account` (`0xacec`, 48 insns) -/

/-- Specification of `<PublicKey as PartialEq>::eq` (`0x3ebf0`, calling `ct_eq` at `0x3ecc4`). -/
noncomputable def publicKeyEqSpec : Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
      (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
      stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64)
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
      stackFrameFor libsignalSessionImage "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64)

/-- Base-program hypothesis: `<PublicKey as PartialEq>::eq` meets `publicKeyEqSpec` on `tripleRatchetProgAt`. -/
def PublicKeyEqOk (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr publicKeyEqName)
    publicKeyEqSpec

def PublicKeyEqOkExt (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr publicKeyEqName)
    publicKeyEqSpec

def PublicKeyEqOk_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Prop :=
  PublicKeyEqOkExt b (trTrapExterns C abs)

/-- Ghost of an `is_same_account` call (`0xacec`):
* `localIkA`: pointer to `local_identity: &IdentityKey` (`x0`);
* `localIk`: `IdentityKey` model value at `localIkA`;
* `remoteIkA`: pointer to `other_identity: &IdentityKey` (`x2`, moved to `x1` at `+0x018`);
* `remoteIk`: `IdentityKey` model value at `remoteIkA` (with `localIk ≠ remoteIk`).
(`x1 = local_address` and `x3 = other_address` are saved in `x20`, `x19` at `+0x014`, `+0x01c` and
never dereferenced on the `localIk ≠ remoteIk` path.) -/
structure IsSameAccountGhost where
  /-- `self: &IdentityKey` (`x0`). -/
  localIkA : BitVec 64
  /-- Local `IdentityKey` model value. -/
  localIk : IdentityKey
  /-- `other_identity: &IdentityKey` (`x2`). -/
  remoteIkA : BitVec 64
  /-- Remote `IdentityKey` model value. -/
  remoteIk : IdentityKey

/-- Specification of `<IdentityKey>::is_same_account` (`0xacec`) when `x.localIk ≠ x.remoteIk`:
`PublicKey::eq` returns `0`, returning `w0 = 0` without dereferencing the address arguments. -/
def isSameAccountSpec : Spec IsSameAccountGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.localIkA ∧ s.readReg64 .x2 = x.remoteIkA ∧ x.localIk ≠ x.remoteIk⌝ ∗
      (x.localIkA ↦ₛ x.localIk.publicKey.bytes.toList) ∗
      (x.remoteIkA ↦ₛ x.remoteIk.publicKey.bytes.toList) ∗
      stackAt s.sp isSameAccountStack
  post := fun x s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
      (x.localIkA ↦ₛ x.localIk.publicKey.bytes.toList) ∗
      (x.remoteIkA ↦ₛ x.remoteIk.publicKey.bytes.toList) ∗
      stackAt s0.sp isSameAccountStack

/-! ## 5. `drop_glue<session_structure::Chain>` (`0x35dc8`, 63 insns) -/

/-- Ghost of a `drop_glue<Chain>` call (`0x35dc8`):
* `a`: pointer to the 104-byte `session_structure::Chain` (`x0`, kept in `x19` at `+0x014`);
* `gc`: `(ChainGhost, ReceiverChain)` describing the `Chain` at `a`. -/
structure DropChainGhost where
  /-- Pointer to `Chain` (`x0`, 104 bytes). -/
  a : BitVec 64
  /-- Ghost and model value of the `Chain`. -/
  gc : ChainGhost × ReceiverChain

/-- Specification of `core::ptr::drop_glue::<session_structure::Chain>` (`0x35dc8`):
deallocates `sender_ratchet_key`, `sender_ratchet_key_private`, `chain_key.key`, all element buffers
of `message_keys`, and the `message_keys` buffer itself, leaving `memRegion x.a 104`. -/
def dropChainSpec (A : RustAlloc) : Spec DropChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chainAt A x.gc x.a ∗ A.pool ∗ stackAt s.sp dropChainStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗ A.pool ∗ stackAt s0.sp dropChainStack

/-- Common `session_structure::Chain` layout without `priv.bytes = []` or `srk.bytes.length = 33`,
satisfied by both receiver chains (`chainAt`) and `Some` sender chains (`optSenderChainAt`). -/
def protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧
    gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

/-- Specification of `core::ptr::drop_glue::<session_structure::Chain>` (`0x35dc8..0x35ec0`) on
`protoChainAt` (arbitrary `priv.bytes`), used when dropping a `Some` sender chain at `ss + 0x90`. -/
def dropProtoChainSpec (A : RustAlloc) : Spec DropChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChainAt A x.gc x.a ∗ A.pool ∗ stackAt s.sp dropChainStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗ A.pool ∗ stackAt s0.sp dropChainStack

/-! ## 6. `drop_glue<Vec<chain::MessageKey>>` (`0x1f28`, 47 insns) -/

/-- Ghost of a `drop_glue<Vec<MessageKey>>` call (`0x1f28`):
* `v`: pointer to the 24-byte `Vec<MessageKey>` header (`x0`, kept in `x20` at `+0x014`);
* `cap`, `ptr`: buffer capacity and pointer (`+0x010: ldp x19, x21, [x0, #8]`, `+0x084: ldr x8, [x20]`);
* `mks`: the list of `(MessageKeyGhost × MessageKeyGenerator)` elements. -/
structure DropVecMessageKeyGhost where
  /-- Pointer to `Vec<MessageKey>` header (`x0`, 24 bytes). -/
  v : BitVec 64
  /-- Buffer capacity (`[v + 0]`). -/
  cap : BitVec 64
  /-- Buffer pointer (`[v + 8]`). -/
  ptr : BitVec 64
  /-- Stored message keys. -/
  mks : List (MessageKeyGhost × MessageKeyGenerator)

/-- Specification of `core::ptr::drop_glue::<Vec<chain::MessageKey>>` (`0x1f28`):
deallocates `cipher_key`, `mac_key`, `iv`, and `seed` of each element and frees the outer buffer,
leaving `memRegion x.v 24`. -/
def dropVecMessageKeySpec (A : RustAlloc) : Spec DropVecMessageKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A 104 8 (messageKeyAt A) x.v x.cap x.ptr x.mks ∗ A.pool ∗
      stackAt s.sp dropVecMessageKeyStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗ A.pool ∗ stackAt s0.sp dropVecMessageKeyStack

/-! ## 7. `drop_glue<Vec<session_structure::Chain>>` (`0x1e74`, 45 insns) -/

/-- Ghost of a `drop_glue<Vec<Chain>>` call (`0x1e74`):
* `v`: pointer to the 24-byte `Vec<Chain>` header (`x0`, kept in `x20` at `+0x014`);
* `cap`, `ptr`: buffer capacity and pointer (`+0x010: ldp x19, x22, [x0, #8]`, `+0x07c: ldr x8, [x20]`);
* `cs`: the list of `(ChainGhost × ReceiverChain)` elements. -/
structure DropVecChainGhost where
  /-- Pointer to `Vec<Chain>` header (`x0`, 24 bytes). -/
  v : BitVec 64
  /-- Buffer capacity (`[v + 0]`). -/
  cap : BitVec 64
  /-- Buffer pointer (`[v + 8]`). -/
  ptr : BitVec 64
  /-- Receiver chains. -/
  cs : List (ChainGhost × ReceiverChain)

/-- Specification of `core::ptr::drop_glue::<Vec<session_structure::Chain>>` (`0x1e74`):
drops each element's owned buffers and `message_keys` vector, frees the outer buffer, and leaves
`memRegion x.v 24`. -/
def dropVecChainSpec (A : RustAlloc) : Spec DropVecChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A 104 8 (chainAt A) x.v x.cap x.ptr x.cs ∗ A.pool ∗
      stackAt s.sp dropVecChainStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗ A.pool ∗ stackAt s0.sp dropVecChainStack

/-! ## 8. `drop_glue<SignalProtocolError>` (`0x2374`, 46 insns) -/

/-- 28-byte `.rodata` jump table at image offset `0x52000` dispatching `drop_glue<SignalProtocolError>`:
- indices `{0, 1, 12, 18, 22, 24, 25, 27}` → `+0x040`: frees the `String` payload at `a + 8`;
- indices `2..11, 13..17, 20, 21, 23` → `+0x0ac`: no-op epilogue;
- index `19` (`SessionNotFound`) and index `26` (`ApplicationCallbackError`) are excluded by `speAt`. -/
def speJumpTable : List (BitVec 8) :=
  [0x00#8, 0x00#8, 0x1b#8, 0x1b#8, 0x1b#8, 0x1b#8, 0x1b#8, 0x1b#8,
   0x1b#8, 0x1b#8, 0x1b#8, 0x1b#8, 0x00#8, 0x1b#8, 0x1b#8, 0x1b#8,
   0x1b#8, 0x1b#8, 0x00#8, 0x13#8, 0x1b#8, 0x1b#8, 0x00#8, 0x1b#8,
   0x00#8, 0x00#8, 0x07#8, 0x00#8]

/-- Ghost of a `drop_glue<SignalProtocolError>` call (`0x2374`):
* `a`: pointer to the 48-byte `SignalProtocolError` (`x0`);
* `fnName`: the `&'static str` bytes of `InvalidState(fnName, String)`;
* `e`: the `SignalProtocolError` model value (`speAt A fnName a e`; `e = .panic` has `speAt = ⌜False⌝`). -/
structure DropSpeGhost where
  /-- Pointer to `SignalProtocolError` (`x0`, 48 bytes). -/
  a : BitVec 64
  /-- Function-name literal for `.invalidState`. -/
  fnName : List (BitVec 8)
  /-- Error variant. -/
  e : SignalProtocolError

/-- Specification of `core::ptr::drop_glue::<SignalProtocolError>` (`0x2374`, used via `.inImage img`
for the `.rodata` jump table `speJumpTable`): consumes `speAt A x.fnName x.a x.e` and leaves
`memRegion x.a 48`. -/
def dropSpeSpec (A : RustAlloc) : Spec DropSpeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      speAt A x.fnName x.a x.e ∗ A.pool ∗ stackAt s.sp dropSpeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 48 ∗ A.pool ∗ stackAt s0.sp dropSpeStack

def dropSpeSpecX (A : RustAlloc) : Spec DropSpeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      speAt A x.fnName x.a x.e ∗ A.pool ∗ stackAt s.sp dropSpeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 48 ∗ A.pool ∗ stackAt s0.sp dropSpeStackX

def dropChainSpecX (A : RustAlloc) : Spec DropChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chainAt A x.gc x.a ∗ A.pool ∗ stackAt s.sp dropChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗ A.pool ∗ stackAt s0.sp dropChainStackX

def dropProtoChainSpecX (A : RustAlloc) : Spec DropChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChainAt A x.gc x.a ∗ A.pool ∗ stackAt s.sp dropChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗ A.pool ∗ stackAt s0.sp dropChainStackX

/-- `clear_unacknowledged_pre_key_message` frame (32 B) + `extHookStack`. -/
abbrev clearUpkStackX : Nat := 32 + extHookStack

/-- `drop_glue<Vec<MessageKey>>` frame (48 B) + `extHookStack`. -/
abbrev dropVecMessageKeyStackX : Nat := 48 + extHookStack

/-- `drop_glue<Vec<Chain>>` frame (48 B) + `dropVecMessageKeyStackX`. -/
abbrev dropVecChainStackX : Nat := 48 + dropVecMessageKeyStackX

def clearUpkSpecX (A : RustAlloc) : Spec ClearUpkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp clearUpkStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionStateAt A x.ss { x.G with pending := none, kyber := none }
        x.st.clearUnacknowledgedPreKeyMessage ∗
      A.pool ∗ stackAt s0.sp clearUpkStackX

def dropVecMessageKeySpecX (A : RustAlloc) : Spec DropVecMessageKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A 104 8 (messageKeyAt A) x.v x.cap x.ptr x.mks ∗ A.pool ∗
      stackAt s.sp dropVecMessageKeyStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗ A.pool ∗ stackAt s0.sp dropVecMessageKeyStackX

def dropVecChainSpecX (A : RustAlloc) : Spec DropVecChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A 104 8 (chainAt A) x.v x.cap x.ptr x.cs ∗ A.pool ∗
      stackAt s.sp dropVecChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗ A.pool ∗ stackAt s0.sp dropVecChainStackX

/-! ## 9. Stacked `PublicKey::eq` & `IdentityKey::is_same_account` (`extHookStack = 16384`) -/

/-- Stack budget of `<PublicKey as PartialEq>::eq` (`16` B) + `ct_eq` (`48` B) + `extHookStack`
(`16384` B) = `16448` bytes under `CliExt.blackBoxSpec`. -/
abbrev publicKeyEqStackExt : Nat := 64 + extHookStack

/-- Contract of `<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq` (`0x3ebf0`) with
`publicKeyEqStackExt = 64 + extHookStack = 16448` B stack (for 32-bit stacked `CliExt.blackBoxSpec`). -/
def publicKeyEqSpecExt : Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
      (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
      stackAt sp publicKeyEqStackExt
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
      stackAt sp publicKeyEqStackExt

/-- Stacked 32-bit `black_box` hypothesis: `<PublicKey as PartialEq>::eq` meets `publicKeyEqSpecExt`
(`64 + extHookStack = 16448` B stack) on `tripleRatchetProgAtExt b ext`. -/
def PublicKeyEqOkExt32 (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr publicKeyEqName)
    publicKeyEqSpecExt

/-- Stack budget of `IdentityKey::is_same_account` (`80` B) + `publicKeyEqStackExt` (`16448` B) =
`16528` bytes under `PublicKeyEqOkExt32`. -/
abbrev isSameAccountStackExt : Nat := 80 + publicKeyEqStackExt

/-- `isSameAccountSpec` at `isSameAccountStackExt = 80 + 64 + extHookStack` (`16528` B). -/
def isSameAccountSpecExt : Spec IsSameAccountGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.localIkA ∧ s.readReg64 .x2 = x.remoteIkA ∧ x.localIk ≠ x.remoteIk⌝ ∗
      (x.localIkA ↦ₛ x.localIk.publicKey.bytes.toList) ∗
      (x.remoteIkA ↦ₛ x.remoteIk.publicKey.bytes.toList) ∗
      stackAt s.sp isSameAccountStackExt
  post := fun x s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
      (x.localIkA ↦ₛ x.localIk.publicKey.bytes.toList) ∗
      (x.remoteIkA ↦ₛ x.remoteIk.publicKey.bytes.toList) ∗
      stackAt s0.sp isSameAccountStackExt

/-! ## 10. Relocatable `[LibsignalPlacement]` Specs for `local_identity_key` and `remote_identity_key` -/

/-- Relocatable specification of `<SessionState>::local_identity_key` (Block `28`) under `[LibsignalPlacement]`. -/
def localIdentityKeyPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec LocalIdentityKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret ∧
      PublicKey.deserialize x.g.bytes = .ok x.ik.publicKey⌝ ∗
      vecGhostAt A x.g x.ss ∗ memRegion x.ret 33 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s.sp localIdentityKeyStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecGhostAt A x.g x.ss ∗ localIdentityOkAt x.ret x.ik ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp localIdentityKeyStack

/-- Relocatable specification of `<SessionState>::remote_identity_key` (Block `29`) under `[LibsignalPlacement]`. -/
def remoteIdentityKeyPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec RemoteIdentityKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret ∧
      (match x.rem with
       | none => x.g.bytes = []
       | some ik => PublicKey.deserialize x.g.bytes = .ok ik.publicKey)⌝ ∗
      vecGhostAt A x.g (x.ss + 0x18#64) ∗ memRegion x.ret 34 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s.sp remoteIdentityKeyStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecGhostAt A x.g (x.ss + 0x18#64) ∗ remoteIdentityOkAt x.ret x.rem ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp remoteIdentityKeyStack

end CryptoVerification.LibsignalTripleRatchet.Getters
