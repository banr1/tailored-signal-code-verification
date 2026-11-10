/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwned

/-!
# Abstract Callee Semantics and Caller-Side Wrapper Slot Specifications (`Sem.lean`)

Fixes the concrete ARM64 ABI and separation-logic footprint of each wrapper callee invoked by
`signal_session::run` while keeping its functional semantics (`S : RunSem`) abstract:
- `RunSem` specifies the abstract transition (`SlotAns`: panic, reject, or accept with updated
  `StoresGhost` and return value) for `encrypt`, `decryptSignal`, `initiate`, and `decryptPrekey`,
  the all-inputs parser `pksmParse`, and the input domain predicates `filesOk`, `encOk`, `initOk`,
  and `decPkOk`.
- `encSlotSpec`, `decSigSlotSpec`, `initSlotSpec`, and `decPkSlotSpec` specify the caller-side ABI
  registers, vtable pointers, stack slots, opened stores, coins, and `SpeOwned`-widened error
  layouts (`encResAt`, `decResAt`, `initResAt`) at each call site in `run`.
- `slotsOf A img S needs` packages the four wrapper slots together with `cliKemDeserializeSpec`
  into `RunSlots`.
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.RecordCodecs

abbrev Bytes := List (BitVec 8)

/-! ## 1. The abstract semantics -/

/-- A wrapper callee's answer: `none` = panic; `some none` = reject (`Err`, or `None`/pending,
which `run` maps to `Rejected` too); `some (some (g', v))` = accept with the stores `g'` after the
call and the value `v`. -/
abbrev SlotAns (α : Type) := Option (Option (StoresGhost × α))

/-- The `PreKeyBundle` `read_bundle` builds (`public.rs:93`), on its values: the identity key,
the registration id, the device id (the peer's), the signed pre-key (id, key, signature), the
Kyber pre-key (id, the 1568 key bytes after the `0x08` type byte, signature) and the optional
one-time pre-key (id, key). -/
structure BundleV where
  idKey : IdentityKey
  regId : BitVec 32
  device : BitVec 8
  spkId : BitVec 32
  spk : PublicKey
  spkSig : Bytes
  kpkId : BitVec 32
  kpk : Bytes
  kpkSig : Bytes
  opk : Option (BitVec 32 × PublicKey)

/-- Abstract semantics of `signal_session::run`'s four stateful wrapper callees, the all-inputs
`PreKeySignalMessage` parser, and their store/input domain preconditions. `F` is the run-entry
filesystem (`(initFsState (cliInputs i)).files`) and `coins` is `coinsOf i`; the stores at every
wrapper call are `StoresGhost.opened`. -/
structure RunSem where
  /-- `signal_session_ratchet::encrypt(ptext, peer, me, stores, now = UNIX_EPOCH)`. -/
  encrypt : FsFiles → AddrVal → AddrVal → Bytes → Bytes → SlotAns CiphertextMessage
  /-- `signal_session_ratchet::decrypt_signal(msg, peer, me, stores)`; `msg` is the parsed
  `SignalMessage` (`SignalMessage.tryFrom protoSignalCodec` of the wire bytes after the type
  byte). -/
  decryptSignal : FsFiles → AddrVal → AddrVal → SignalMessage → Bytes → SlotAns Bytes
  /-- `signal_session_handshake::initiate(peer, me, stores, bundle, now = UNIX_EPOCH)`. -/
  initiate : FsFiles → AddrVal → AddrVal → BundleV → Bytes → SlotAns Unit
  /-- `signal_session_handshake::decrypt_prekey(pksm, peer, me, stores)`. -/
  decryptPrekey : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Bytes → SlotAns Bytes
  /-- All-inputs `PreKeySignalMessage::try_from` parser on the wire bytes after the tag byte. -/
  pksmParse : Bytes → Option PreKeySignalMessage
  /-- Store-file well-formedness precondition assumed by all four wrapper slots (`files`, `peer`,
  `me`), ensuring the session, identity, and pre-key store files decode cleanly. -/
  filesOk : FsFiles → AddrVal → AddrVal → Prop
  /-- Encrypt-slot domain precondition (`files`, `peer`, `coins`), e.g. `64 ≤ coins.length` or an
  empty PQ ratchet state on the peer session. -/
  encOk : FsFiles → AddrVal → Bytes → Prop
  /-- Initiate-slot domain precondition (`files`, `peer`, `me`), e.g. absence of an existing peer
  session when using 1-session `sessionRecordAt`, plus local/remote identity invariants. -/
  initOk : FsFiles → AddrVal → AddrVal → Prop
  /-- Decrypt-prekey-slot domain precondition (`files`, `peer`, `me`, parsed message `pm`). -/
  decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop

/-- Stack budgets of the four stateful wrapper slots. -/
structure RunNeeds where
  encrypt : Nat
  decryptSignal : Nat
  initiate : Nat
  decryptPrekey : Nat

/-! ## 2. Layout pieces -/

/-- Store vtable addresses passed by `signal_session::run` to the wrapper callees, defined via
`ls_reloc%` data-relocation slots so they track binary relinks automatically and match `KitInst`'s
vtable offsets (`sessVt_eq`..`kyberVt_eq`). -/
def sessVt (img : Obj.Image) : BitVec 64 :=
  img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") - 0x18)
def idVt (img : Obj.Image) : BitVec 64 :=
  img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28)
def oneTimeVt (img : Obj.Image) : BitVec 64 :=
  img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") - 0x18)
def signedVt (img : Obj.Image) : BitVec 64 :=
  img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key") - 0x18)
def kyberVt (img : Obj.Image) : BitVec 64 :=
  img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key") - 0x18)

/-! Layout guards: the vtable offsets in the current export, so a re-export that moves a vtable
fails here first, not deep in a slot proof. Update the numerals mechanically on a relink. -/
theorem sessVt_eq (img : Obj.Image) : sessVt img = img.base + 0x98c38#64 := rfl
theorem idVt_eq (img : Obj.Image) : idVt img = img.base + 0x98c60#64 := rfl
theorem oneTimeVt_eq (img : Obj.Image) : oneTimeVt img = img.base + 0x98ca0#64 := rfl
theorem signedVt_eq (img : Obj.Image) : signedVt img = img.base + 0x98cd0#64 := rfl
theorem kyberVt_eq (img : Obj.Image) : kyberVt img = img.base + 0x98cf8#64 := rfl

/-- `now : SystemTime` by value at `p` (16 bytes, matching `MessageEncrypt.nowAt`); `run` passes
`UNIX_EPOCH` (all zero). -/
def nowCellAt (p : BitVec 64) (t : SystemTime) : SepProp :=
  (p ↦₆₄ t.tvSec) ∗ ((p + 8#64) ↦₃₂ t.tvNsec) ∗ memRegion (p + 12#64) 4

/-- `SystemTime::UNIX_EPOCH`. -/
def unixEpoch : SystemTime := ⟨0#64, 0#32⟩

/-- 48-byte `Option<Result<Vec<u8>, SignalProtocolError>>` return layout shared by
`decrypt_prekey` and `decrypt_signal`: `Ok` matches `apiDecResultAt` (`okTagVec = -2` at `+0` and
plaintext `Vec<u8>` at `+8`), while `Err` widens `apiDecResultAt` to any droppable
`RunDrop.speOwnedAt` at `+0` so CLI-store `InvalidState` and bad-prekey-id errors are covered. -/
def decResAt (A : RustAlloc) (r : BitVec 64) : Except (ApiError AddrVal Unit) Bytes → SepProp
  | .ok pt => vecResultAt A r (.ok pt)
  | .error _ => ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k

/-- `decResAt`'s `Ok` arm is the public entry's (`apiDecResultAt`): only the `Err` arm widens. -/
theorem decResAt_ok (A : RustAlloc) (r : BitVec 64) (pt : Bytes) :
    decResAt A r (.ok pt) = apiDecResultAt A r (.ok pt) := rfl

/-- 248-byte `Result<CiphertextMessage, SignalProtocolError>` return layout of `encrypt`: `Ok`
matches `apiEncResultAt`, while `Err` places `errTag` at `+0`, any droppable `RunDrop.speOwnedAt`
at `+8`, and 192 unspecified trailing bytes at `+56`. -/
def encResAt (A : RustAlloc) (r : BitVec 64) :
    Except (ApiError AddrVal Unit) CiphertextMessage → SepProp
  | .ok m => apiEncResultAt A r (.ok m)
  | .error _ =>
    (r ↦₆₄ errTag) ∗ (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A (r + 8#64) k) ∗
      memRegion (r + 56#64) 192

/-- `encResAt`'s `Ok` arm is the public entry's (`apiEncResultAt`): only the `Err` arm widens. -/
theorem encResAt_ok (A : RustAlloc) (r : BitVec 64) (m : CiphertextMessage) :
    encResAt A r (.ok m) = apiEncResultAt A r (.ok m) := rfl

/-- 48-byte `Option<Result<(), SignalProtocolError>>` return layout of `initiate`: `Ok(())` has
word `0` equal to `-2`, while `Err` holds any droppable `RunDrop.speOwnedAt` at `+0` (including
`SignatureValidationFailed` = `speWord 11`). -/
def initResAt (A : RustAlloc) (r : BitVec 64) : Except (ApiError AddrVal Unit) Unit → SepProp
  | .ok () => (r ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (r + 8#64) 40
  | .error _ => ∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A r k

/-- 192-byte (`0xc0`) `PreKeyBundle` layout passed by reference (`&bundle`) from
`signal_session::run` to `initiate` at `a`, together with its three caller-freed heap buffers
(`spkSig` 64 B at `+0x00..+0x18`, `kpkSig` 64 B at `+0x40..+0x58`, `kpk` 1568 B at `+0x58..+0x68`),
`spkId` (`+0x38`), `kpkId` (`+0x68`), `opk` (`+0x70..+0x98`, flag `+0x9c`), `regId` (`+0x98`), and
`device` (`+0xbd`). -/
def cliBundleAt (a : BitVec 64) (b : BundleV) (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) :
    SepProp :=
  let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
  ∃∗ opkId : BitVec 32,
    ⌜b.spkSig.length = 64 ∧ b.kpkSig.length = 64 ∧ b.kpk.length = 1568 ∧
      ∀ p, b.opk = some p → opkId = p.1⌝ ∗
    (a ↦₆₄ 64#64) ∗ ((a + 8#64) ↦₆₄ spkSigPtr) ∗ ((a + 16#64) ↦₆₄ 64#64) ∗
    (spkSigPtr ↦ₛ b.spkSig) ∗
    ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗
    ((a + 56#64) ↦₃₂ b.spkId) ∗ memRegion (a + 60#64) 4 ∗
    ((a + 64#64) ↦₆₄ 64#64) ∗ ((a + 72#64) ↦₆₄ kpkSigPtr) ∗ ((a + 80#64) ↦₆₄ 64#64) ∗
    (kpkSigPtr ↦ₛ b.kpkSig) ∗
    ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ b.kpk) ∗
    ((a + 104#64) ↦₃₂ b.kpkId) ∗ memRegion (a + 108#64) 4 ∗
    ((a + 112#64) ↦₃₂ opkFlag) ∗ ((a + 116#64) ↦₃₂ opkId) ∗
    ((a + 120#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗ ((a + 152#64) ↦₃₂ b.regId) ∗
    ((a + 156#64) ↦₈ opkFlag.truncate 8) ∗
    (match b.opk with
     | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
     | none => memRegion (a + 157#64) 32) ∗
    ((a + 189#64) ↦₈ b.device) ∗ memRegion (a + 190#64) 2

/-! ## 3. The slot specs -/

/-- What every wrapper call site shares: the two address ghosts and pointers, the stores, the
result slot, the coin pointer, and the run-entry values `F` / `coins` that `S` reads. -/
structure SlotCtx where
  peer : AddrGhost
  peerA : BitVec 64
  me : AddrGhost
  meA : BitVec 64
  stores : BitVec 64
  ret : BitVec 64
  coinsP : BitVec 64
  F : FsFiles
  coins : Bytes

/-- Common wrapper-slot precondition footprint: opened stores, peer and local addresses, installed
coins with `coins.length < 2 ^ 63`, `TokenInit`, `logOff`, and allocator pool. -/
def slotFrame (A : RustAlloc) (img : Obj.Image) (x : SlotCtx) : SepProp :=
  ⌜x.coins.length < 2 ^ 63⌝ ∗
  storesAt A x.stores StoresGhost.opened ∗ protocolAddressAt A x.peer x.peerA ∗
    protocolAddressAt A x.me x.meA ∗ coinsInstalled img x.coinsP x.coins ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗ logOff img ∗ A.pool

/-- The common post facts: the trace only grows; files and stdout unchanged. -/
def slotTrace (s0 sf : State) : Prop :=
  s0.trace <+: sf.trace ∧ sf.fs.files = s0.fs.files ∧
    ProcessOutcome.traceStreamBytes .stdout sf.trace =
      ProcessOutcome.traceStreamBytes .stdout s0.trace

/-- Links the wrapper return value `e` and post-call stores `g'` to the abstract answer `ans`:
`Ok v` iff `ans = some (some (g', v))` with `cliWrOk` write paths, and `Err` (excluding `store ()`)
iff `ans = some none`. -/
def slotOut {α : Type} (ans : SlotAns α) (g' : StoresGhost)
    (e : Except (ApiError AddrVal Unit) α) (_s0 _sf : State) : Prop :=
  e ≠ .error .panic ∧ e ≠ .error (.store ()) ∧
    match e with
    | .ok v => ans = some (some (g', v)) ∧ ∀ pw ∈ g'.writes, cliWrOk pw.1
    | .error _ => ans = some none

/-- Ghost of the `encrypt` call: the shared context and the plaintext. -/
structure EncGhost extends SlotCtx where
  ptA : BitVec 64
  ptext : Bytes

/-- Caller-side slot specification for `signal_session_ratchet::encrypt`: `x0, x1` = plaintext,
`x2` = peer, `x3` = me (`x.meA ≠ 0#64`), `x4` = `stores + 0xf0` (sessions), `x5` = session vtable,
`x6` = `stores` (identity), `x7` = identity vtable, `x8` = 248-byte `encResAt` result, and
`UNIX_EPOCH` at `[sp]`. On `Ok (.preKeySignalMessage m)`, `m.serialized.length < 2 ^ 42` so
`3 ‖ serialized` cannot overflow `cliConcat2Spec`. -/
def encSlotSpec (A : RustAlloc) (img : Obj.Image) (S : RunSem) (stk : Nat) : Spec EncGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.peerA ∧ s.readReg64 .x3 = x.meA ∧
          s.readReg64 .x4 = x.stores + 0xf0#64 ∧ s.readReg64 .x5 = sessVt img ∧
          s.readReg64 .x6 = x.stores ∧ s.readReg64 .x7 = idVt img ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          S.encOk x.F x.peer.val x.coins ∧ stk ≤ s.sp.toNat ∧ x.meA ≠ 0#64⌝ ∗
        slotFrame A img x.toSlotCtx ∗ (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s.sp unixEpoch ∗
        memRegion x.ret 248 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) CiphertextMessage,
          ⌜slotTrace s0 sf ∧
            slotOut (S.encrypt x.F x.peer.val x.me.val x.ptext x.coins) g' e s0 sf ∧
            (∀ m : PreKeySignalMessage, e = .ok (.preKeySignalMessage m) →
              m.serialized.length < 2 ^ 42)⌝ ∗
          storesAt A x.stores g' ∗ encResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          (x.ptA ↦ₛ x.ptext) ∗ nowCellAt s0.sp unixEpoch ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.encrypt x.F x.peer.val x.me.val x.ptext x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }
    img

/-- Ghost of the `decrypt_signal` call: the shared context and the parsed message (built by
`SignalMessage::try_from`, borrowed; `run` drops it after the call). -/
structure DecSigGhost extends SlotCtx where
  msgA : BitVec 64
  msgG : SignalMessageGhost
  msg : SignalMessage

/-- Caller-side slot specification for `signal_session_ratchet::decrypt_signal`: `x0` = borrowed
`SignalMessage`, `x1` = peer, `x2` = me, `x3` = `stores + 0xf0`, `x4` = session vtable,
`x5` = `stores`, `x6` = identity vtable, and `x8` = 48-byte `decResAt` result. -/
def decSigSlotSpec (A : RustAlloc) (img : Obj.Image) (S : RunSem) (stk : Nat) :
    Spec DecSigGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
          s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = sessVt img ∧
          s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = idVt img ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          stk ≤ s.sp.toNat⌝ ∗
        slotFrame A img x.toSlotCtx ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
        memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
          ⌜slotTrace s0 sf ∧
            slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf⌝ ∗
          storesAt A x.stores g' ∗ decResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }
    img

/-- Ghost of the `initiate` call: the shared context, the bundle (borrowed at `bundleA`) and its
three heap pointers (which `run` frees after the call). -/
structure InitGhost extends SlotCtx where
  bundleA : BitVec 64
  bundle : BundleV
  spkSigPtr : BitVec 64
  kpkSigPtr : BitVec 64
  kpkPtr : BitVec 64

/-- Caller-side slot specification for `signal_session_handshake::initiate`: `x0` = peer,
`x1` = me, `x2` = `stores + 0xf0`, `x3` = session vtable, `x4` = `stores`, `x5` = identity vtable,
`x6` = borrowed `cliBundleAt` (returned unchanged at the same three heap pointers), `x7` = `0`
(`now.tv_sec`), `[sp]` = `0` (`now.tv_nsec`), and `x8` = 48-byte `initResAt` result. -/
def initSlotSpec (A : RustAlloc) (img : Obj.Image) (S : RunSem) (stk : Nat) : Spec InitGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.peerA ∧ s.readReg64 .x1 = x.meA ∧
          s.readReg64 .x2 = x.stores + 0xf0#64 ∧ s.readReg64 .x3 = sessVt img ∧
          s.readReg64 .x4 = x.stores ∧ s.readReg64 .x5 = idVt img ∧
          s.readReg64 .x6 = x.bundleA ∧ s.readReg64 .x7 = 0#64 ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧
          S.filesOk x.F x.peer.val x.me.val ∧ S.initOk x.F x.peer.val x.me.val ∧
          stk ≤ s.sp.toNat⌝ ∗
        slotFrame A img x.toSlotCtx ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Unit,
          ⌜slotTrace s0 sf ∧
            slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins) g' e s0 sf⌝ ∗
          storesAt A x.stores g' ∗ initResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }
    img

/-- Ghost of the `decrypt_prekey` call: the shared context and the parsed message (borrowed). -/
structure DecPkGhost extends SlotCtx where
  msgA : BitVec 64
  msgG : PreKeyMsgGhost
  msg : PreKeySignalMessage

/-- Caller-side slot specification for `signal_session_handshake::decrypt_prekey`: `x0` = borrowed
`PreKeySignalMessage`, `x1` = peer, `x2` = me, `x3` = `stores + 0xf0`, `x4` = session vtable,
`x5` = `stores`, `x6` = identity vtable, `x7` = `stores + 0xc8` (one-time pre-keys), stack
arguments `[sp]` = one-time vtable, `[sp+8]` = `stores + 0x50` (signed), `[sp+0x10]` = signed
vtable, `[sp+0x18]` = `stores + 0x78` (Kyber), `[sp+0x20]` = Kyber vtable, and `x8` = 48-byte
`decResAt` result. -/
def decPkSlotSpec (A : RustAlloc) (img : Obj.Image) (S : RunSem) (stk : Nat) :
    Spec DecPkGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
          s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = sessVt img ∧
          s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = idVt img ∧
          s.readReg64 .x7 = x.stores + 0xc8#64 ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
          S.decPkOk x.F x.peer.val x.me.val x.msg ∧ stk ≤ s.sp.toNat⌝ ∗
        slotFrame A img x.toSlotCtx ∗ preKeyMsgAt A x.msgG x.msgA x.msg ∗
        (s.sp ↦₆₄ oneTimeVt img) ∗ ((s.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
        ((s.sp + 16#64) ↦₆₄ signedVt img) ∗ ((s.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
        ((s.sp + 32#64) ↦₆₄ kyberVt img) ∗
        memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
          ⌜slotTrace s0 sf ∧
            slotOut (S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf⌝ ∗
          storesAt A x.stores g' ∗ decResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          preKeyMsgAt A x.msgG x.msgA x.msg ∗
          (s0.sp ↦₆₄ oneTimeVt img) ∗ ((s0.sp + 8#64) ↦₆₄ (x.stores + 0x50#64)) ∗
          ((s0.sp + 16#64) ↦₆₄ signedVt img) ∗ ((s0.sp + 24#64) ↦₆₄ (x.stores + 0x78#64)) ∗
          ((s0.sp + 32#64) ↦₆₄ kyberVt img) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.decryptPrekey x.F x.peer.val x.me.val x.msg x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }
    img

/-- Ghost of an all-inputs `PreKeySignalMessage::try_from` call. -/
structure PksmGhost where
  ptr : BitVec 64
  bytes : Bytes
  ret : BitVec 64

/-- 248-byte return layout of `PreKeySignalMessage::try_from`: `preKeyMsgAt` at `+0` when
`S.pksmParse` returns `some`, or `errTag` at `+0` with an owned `SignalProtocolError` at `+8` when
`none`, together with `anyHeap` for residual parser allocations. -/
def pksmResAt (A : RustAlloc) (r : BitVec 64) : Option PreKeySignalMessage → SepProp
  | some m => (∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g r m) ∗ anyHeap
  | none => (r ↦₆₄ errTag) ∗ (∃∗ fn : Bytes, ∃∗ e : SignalProtocolError, speAt A fn (r + 8#64) e) ∗
      memRegion (r + 56#64) 192 ∗ anyHeap

/-- All-inputs caller-side slot specification for `PreKeySignalMessage::try_from`, with result
determined by `S.pksmParse` on every byte slice of length `< 2 ^ 32`. -/
def pksmSlotSpec (A : RustAlloc) (img : Obj.Image) (S : RunSem) : Spec PksmGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptr ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ≤ s.sp.toNat⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ logOff img ∗
        stackAt s.sp CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗ pksmResAt A x.ret (S.pksmParse x.bytes) ∗ (x.ptr ↦ₛ x.bytes) ∗
          logOff img ∗
          stackAt s0.sp CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack ∗ A.pool
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-! ## 4. The slots -/

/-- A slot from a spec family and a need (`Spec.inImage` is inside each spec). -/
def mkSlot {G : Type} (spec : Nat → Spec G) (need : Nat) : CalleeSlot := ⟨G, spec, need⟩

/-- Wrapper and `cliKemDeserializeSpec` (`48 + extHookStack`) callee slots at which `run_ok'` is
stated. -/
def slotsOf (A : RustAlloc) (img : Obj.Image) (S : RunSem) (needs : RunNeeds) : RunSlots where
  encrypt := mkSlot (encSlotSpec A img S) needs.encrypt
  decryptSignal := mkSlot (decSigSlotSpec A img S) needs.decryptSignal
  initiate := mkSlot (initSlotSpec A img S) needs.initiate
  decryptPrekey := mkSlot (decPkSlotSpec A img S) needs.decryptPrekey
  kemDeserialize := mkSlot (fun stk => (RunProofs.cliKemDeserializeSpec A stk).inImage img)
    (48 + extHookStack)

end CryptoVerification.SignalSession.Cli.RunCompose
