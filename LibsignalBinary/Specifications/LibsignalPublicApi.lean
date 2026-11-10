/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop

/-!
# Public Session API Specifications over Store Hooks (`LibsignalPublicApi`)

**Checked by Lean.** Hoare specifications (`decryptSignalSpec`, `encryptSpec`) for
`session_message_decrypt_signal` and `session_message_encrypt` against the session-API model
(`messageDecryptSignal`, `messageEncrypt` in `LibsignalSessionApi.lean`) over any store
implementation satisfying `PublicApiHooks`.

## Store-Hook Scope and Panic Boundary

* Loaded records satisfy `RecordInScope` (and `sessionRecordAt`, which enforces no previous
  sessions): any current session has `remoteIdentity ≠ some localIdentity` (DEV-LS28), 32-byte
  stored seeds (`SeedsLen32`, DEV-LS9), fewer than `2^32` receiver chains, and a pending Kyber
  ciphertext shorter than `2^32` bytes.
* Borrowed inputs (message/plaintext and remote/local addresses) are separate heap blocks (`∗`).
* On panic, `onPanic` guarantees that the trace extends `s0.trace` (and `s0.trace ++ [loadEvent …]`
  after the load), without ruling out subsequent trace events permitted by underlying panic
  contracts.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol names -/

/-- The decrypt entry (`0x3a4a8`, 2451 instructions; `src/lib.rs`). -/
abbrev decryptEntryName : String := "session_message_decrypt_signal"
/-- The encrypt entry (`0x3caf4`, 1009 instructions; `src/lib.rs`). -/
abbrev encryptEntryName : String := "session_message_encrypt"
/-- `message_encrypt::<HookRng>` on `dyn` stores (`0x3caf4`, 1009 instructions; `src/lib.rs`). -/
abbrev encryptWithStoresName : String := "session_message_encrypt"

/-- The store hooks (`stores/src/lib.rs:49–76`). -/
abbrev loadSessionHookName : String := "libsignal_session_load_session"
abbrev storeSessionHookName : String := "libsignal_session_store_session"
abbrev isTrustedHookName : String := "libsignal_session_is_trusted_identity"
abbrev saveIdentityHookName : String := "libsignal_session_save_identity"

/-- The four store hooks. -/
def storeHookNames : List String :=
  [loadSessionHookName, storeSessionHookName, isTrustedHookName, saveIdentityHookName]

/-! ## Store-hook contracts -/

/-- Stack of a store hook (no bound of its own; as the triple ratchet's other abstract hooks). -/
abbrev storeHookStack : Nat := extHookStack

/-- The status word `w` (the hook's `u32` result, `w0`) of an answer class: `some false` / `some
true` = the first / second `Ok` answer (status 0 / 1), `none` = an error (any other status). -/
def StatusIs (w : BitVec 32) : Option Bool → Prop
  | some false => w = 0#32
  | some true => w = 1#32
  | none => w ≠ 0#32 ∧ w ≠ 1#32

/-- The status word `w` of a `store_session` answer, whose only `Ok` answer is status 0: any other
status, including 1, is an error (`stores/src/lib.rs:58–59, 125–127`). -/
def StoreStatusIs (w : BitVec 32) : Except Unit Unit → Prop
  | .ok () => w = 0#32
  | .error () => w ≠ 0#32

/-- The class of a `load_session` answer (`Ok(None)` = 0, `Ok(Some _)` = 1). -/
def loadClass : Except Unit (Option (SessionRecord (List (BitVec 8)))) → Option Bool
  | .ok none => some false
  | .ok (some _) => some true
  | .error () => none

/-- The class of an `Except Unit` answer by a Boolean view of its `Ok` value. -/
def exceptClass {α : Type} (f : α → Bool) : Except Unit α → Option Bool
  | .ok a => some (f a)
  | .error () => none

/-- **Scope of a loaded record (trusted assumption on the store).** The current session,
if any, has remote IK ≠ local IK (DEV-LS28; decrypt's `self_session` check needs it, encrypt
does not, so this is stronger than encrypt needs), 32-byte stored seeds (`SeedsLen32`, DEV-LS9),
fewer than `2^32` receiver chains and a pending Kyber ciphertext shorter than `2^32` bytes
(ML-KEM-1024's is 1568; it makes the capacity-overflow and `encode(..).expect` panics of
`PreKeySignalMessage::new` refutable by arithmetic). "No previous sessions" is the other half of
the scope and is enforced by `sessionRecordAt`. -/
def RecordInScope (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s →
    s.state.remoteIdentity ≠ some s.state.localIdentity ∧ SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 32

/-- A `load_session` call: the address (`x0`) and the `MaybeUninit<SessionRecord>` buffer (`x1`,
368 bytes; the poll's frame, `0x42a78: add x1, sp, #0x140`). -/
structure LoadCall where
  addrA : BitVec 64
  addr : AddrGhost
  out : BitVec 64

/-- **`libsignal_session_load_session(address, record_out) -> u32`.** Some answer `ans`: the
status is `ans`'s, the trace grew by `loadEvent encRecord address ans`; on `Ok(Some r)` the buffer
holds a fresh in-scope record `r` (owning its heap blocks), else it holds arbitrary bytes
(`memRegion`); the address is
given back. -/
def loadSessionSpec (A : RustAlloc) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec LoadCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.addrA ∧ s.readReg64 .x1 = x.out⌝ ∗ protocolAddressAt A x.addr x.addrA ∗
      memRegion x.out 368 ∗ A.pool ∗ stackAt s.sp storeHookStack
  post := fun x s0 sf =>
    ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
      ⌜StatusIs ((sf.readReg64 .x0).setWidth 32) (loadClass ans) ∧
        sf.trace = s0.trace ++ [loadEvent encRecord x.addr.val ans]⌝ ∗
      (match ans with
       | .ok (some r) => ⌜RecordInScope r⌝ ∗ ∃∗ g : RecordGhost, sessionRecordAt A x.out g r
       | _ => memRegion x.out 368) ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp storeHookStack

/-- A `store_session` call: the address (`x0`) and the borrowed record (`x1`). -/
structure StoreSessionCall where
  addrA : BitVec 64
  addr : AddrGhost
  recA : BitVec 64
  g : RecordGhost
  record : SessionRecord (List (BitVec 8))

/-- **`libsignal_session_store_session(address, record) -> u32`** (reads the record, does not
consume it). Some answer: status 0 = `Ok(())`, else error; the trace grew by
`storeSessionEvent encRecord address record ans`; the arguments are given back unchanged. -/
def storeSessionSpec (A : RustAlloc) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec StoreSessionCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.addrA ∧ s.readReg64 .x1 = x.recA⌝ ∗ protocolAddressAt A x.addr x.addrA ∗
      sessionRecordAt A x.recA x.g x.record ∗ A.pool ∗ stackAt s.sp storeHookStack
  post := fun x s0 sf =>
    ∃∗ ans : Except Unit Unit,
      ⌜StoreStatusIs ((sf.readReg64 .x0).setWidth 32) ans ∧
        sf.trace = s0.trace ++ [storeSessionEvent encRecord x.addr.val x.record ans]⌝ ∗
      protocolAddressAt A x.addr x.addrA ∗ sessionRecordAt A x.recA x.g x.record ∗ A.pool ∗
      stackAt s0.sp storeHookStack

/-- An identity-store call: the address (`x0`), the `&IdentityKey` (`x1`; 32 key bytes, the
`IdentityKey` layout, 32 bytes, align 1), and for the trust check the direction (`w2`: 0 =
sending, 1 = receiving). -/
structure IdentityCall where
  addrA : BitVec 64
  addr : AddrGhost
  keyA : BitVec 64
  key : IdentityKey

/-- **`libsignal_session_is_trusted_identity(address, identity, direction) -> u32`**: status 0 /
1 = `Ok(false)` / `Ok(true)`, else error; one `trustEvent`; arguments given back. Ghost: the call
and the direction. -/
def isTrustedSpec (A : RustAlloc) : Spec (IdentityCall × Direction) where
  pre := fun (x, d) s =>
    ⌜s.readReg64 .x0 = x.addrA ∧ s.readReg64 .x1 = x.keyA ∧
      (s.readReg64 .x2).setWidth 32 = (directionByte d).setWidth 32⌝ ∗
      protocolAddressAt A x.addr x.addrA ∗ (x.keyA ↦ₛ x.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp storeHookStack
  post := fun (x, d) s0 sf =>
    ∃∗ ans : Except Unit Bool,
      ⌜StatusIs ((sf.readReg64 .x0).setWidth 32) (exceptClass id ans) ∧
        sf.trace = s0.trace ++ [trustEvent x.addr.val x.key d ans]⌝ ∗
      protocolAddressAt A x.addr x.addrA ∗ (x.keyA ↦ₛ x.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s0.sp storeHookStack

/-- **`libsignal_session_save_identity(address, identity) -> u32`**: status 0 / 1 =
`Ok(NewOrUnchanged)` / `Ok(ReplacedExisting)`, else error; one `saveEvent`; arguments given back. -/
def saveIdentitySpec (A : RustAlloc) : Spec IdentityCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.addrA ∧ s.readReg64 .x1 = x.keyA⌝ ∗ protocolAddressAt A x.addr x.addrA ∗
      (x.keyA ↦ₛ x.key.publicKey.bytes.toList) ∗ A.pool ∗ stackAt s.sp storeHookStack
  post := fun x s0 sf =>
    ∃∗ ans : Except Unit IdentityChange,
      ⌜StatusIs ((sf.readReg64 .x0).setWidth 32) (exceptClass (· == .replacedExisting) ans) ∧
        sf.trace = s0.trace ++ [saveEvent x.addr.val x.key ans]⌝ ∗
      protocolAddressAt A x.addr x.addrA ∗ (x.keyA ↦ₛ x.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s0.sp storeHookStack

/-! ## `std::time` stubs (PreKey wrapping)

Encrypt's PreKey branch (`session_management.rs:75–86`) and `unacknowledged_pre_key_message_items`
(`state/session.rs:549–564`) call two `std` functions that are extern stubs of the image (`std` is
not compiled in). Every call site passes a whole number of seconds (`w3 = 0`):
`UNIX_EPOCH + Duration::from_secs(timestamp)` (`0x12518`) and `items.timestamp() +
MAX_UNACKNOWLEDGED_SESSION_AGE` (`_with_stores+0x6f8`, `x2 = 2592000`); `duration_since(UNIX_EPOCH)`
(`_with_stores+0x6c4`) feeds only the log line (logging off). -/

abbrev timeAddHookName : String :=
  "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add"
abbrev durationSinceHookName : String := "<std::time::SystemTime>::duration_since"

/-- The two time stubs. -/
def timeHookNames : List String := [timeAddHookName, durationSinceHookName]

/-- **`<SystemTime as Add<Duration>>::add(self, dur) -> SystemTime`** for a whole number of
seconds (`std/time.rs:738–748`): `self` in `x0` (`tv_sec`) / `w1` (`tv_nsec`), the duration in `x2`
(seconds) / `w3` (nanoseconds, 0 at every call site), `x4` the panic `Location`. Returns W0's
`checkedAddSecs` in `x0` / `w1`; panics exactly when it is `none` (`expect("overflow when adding
duration to `SystemTime`")`, `std/time.rs:747`). Ghost: `(self, secs)`. -/
def timeAddSpec : Spec (SystemTime × Nat) where
  pre := fun (t, secs) s =>
    ⌜s.readReg64 .x0 = t.tvSec ∧ (s.readReg64 .x1).setWidth 32 = t.tvNsec ∧
      t.tvNsec.toNat < 10 ^ 9 ∧ (s.readReg64 .x2).toNat = secs ∧
      (s.readReg64 .x3).setWidth 32 = 0#32⌝ ∗ stackAt s.sp extHookStack
  post := fun (t, secs) s0 sf =>
    ⌜t.checkedAddSecs secs = some ⟨sf.readReg64 .x0, (sf.readReg64 .x1).setWidth 32⟩ ∧
      sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack
  onPanic := fun (t, secs) s0 sf => ⌜t.checkedAddSecs secs = none ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- **`SystemTime::duration_since(&self, earlier) -> Result<Duration, SystemTimeError>`**
(`std/time.rs`; `x0` = `&self`, a 16-byte `SystemTime` temporary; `earlier` in `x1` / `w2`; sret
`x8`, 24 bytes: tag word, then the `Duration` either way). A contract, not a model: only the log
line reads the result, so it is any 24 bytes; it never panics (`checked_sub` on `Timespec`). The
footprint is the memory the stub reads or writes in the image. The real stub also reads a 16-byte
constant from std's own immutable `.rodata` (`sub_timespec`, `Err` path). That read is allowed and
is deliberately not in the footprint: it is not program memory, nothing writes it, and the result is
unconstrained anyway. Ghost: `(self address, sret)`. -/
def durationSinceSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, ret) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗ memRegion p 16 ∗ memRegion ret 24 ∗
      stackAt s.sp extHookStack
  post := fun (p, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion p 16 ∗ memRegion ret 24 ∗ stackAt s0.sp extHookStack

/-! ## `<String as Clone>::clone` (the address clone of two errors)

`ProtocolAddress::clone` (derived) is inlined: a call of the `alloc` stub `<String as Clone>::clone`
on the name, then an inline copy of the device byte. W0 error outcomes reach it: `SessionNotFound`
(decrypt `_with_stores+0x4b0`; encrypt `+0x1d0`, `+0x424`, `+0x798`) and `UntrustedIdentity`
(decrypt `+0x225c`, encrypt `+0xd18`); every site is `add x8, sp, #..; mov x0, <&address>; bl`. -/

abbrev stringCloneHookName : String := "<alloc::string::String as core::clone::Clone>::clone"

/-- **`<String as Clone>::clone(&self) -> String`** (`alloc/string.rs`; `x0` = `&self`, sret
`x8`, 24 bytes): a fresh `String` with exactly the same bytes (`to_vec` of the contents: one
`__rust_alloc(len, 1)` and a copy; capacity unspecified), `self` unchanged. Panics only on a failed
allocation. Ghost: `(self address, sret, self's exact Vec)`. -/
def stringCloneSpec (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × VecGhost) where
  pre := fun (p, ret, g) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗ vecGhostAt A g p ∗ memRegion ret 24 ∗
      A.pool ∗ stackAt s.sp extHookStack
  post := fun (p, ret, g) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecGhostAt A g p ∗ vecU8 A ret g.bytes ∗ A.pool ∗
      stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- **The contracts the abstract hooks meet**: the triple ratchet's (`TripleRatchetHooks`), the
four store hooks, the two time stubs and `String::clone` (each a `HookSat` on `abs`;
`tripleRatchetExterns` hands these names to `abs`, `tripleRatchetExterns_stores_abs`). -/
structure PublicApiHooks (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S abs where
  loadSession : HookSat abs loadSessionHookName (loadSessionSpec A encRecord)
  storeSession : HookSat abs storeSessionHookName (storeSessionSpec A encRecord)
  isTrusted : HookSat abs isTrustedHookName (isTrustedSpec A)
  saveIdentity : HookSat abs saveIdentityHookName (saveIdentitySpec A)
  timeAdd : HookSat abs timeAddHookName timeAddSpec
  durationSince : HookSat abs durationSinceHookName durationSinceSpec
  stringClone : HookSat abs stringCloneHookName (stringCloneSpec A)

/-- The extern stubs `PublicApiHooks` adds to those of `TripleRatchetHooks`: the store hooks, the
time stubs, `String::clone`. -/
def publicApiStubNames : List String := storeHookNames ++ timeHookNames ++ [stringCloneHookName]

/-! ## Stack budget -/

/-- Stack of the two public entries: `_with_stores`' frame (decrypt `0xe80 + 0x60` bytes) plus the
deepest callee (the triple ratchet's `rootStack` for the inlined `try_decrypt_from_record` /
`OTR::encrypt`), with margin. -/
abbrev entryStack : Nat := 2 ^ 19

/-! ## `session_message_decrypt_signal` -/

/-- Ghost of a decrypt call (`ciphertext: &SignalMessage` `x0`, `remote_address` `x1` (the
sender), `local_address` `x2`, sret `x8`, 48 bytes). -/
structure DecryptGhost where
  ret : BitVec 64
  msgA : BitVec 64
  msgG : SignalMessageGhost
  msg : SignalMessage
  remA : BitVec 64
  rem : AddrGhost
  locA : BitVec 64
  loc : AddrGhost
  /-- The tape position. -/
  cur : BitVec 64
  rest : List (BitVec 8)

/-- W0's result and call trace on the store answers `answers` (coins = the first 32 tape bytes,
addresses parsed by the triple ratchet's model of the compiled parser). -/
def DecryptGhost.model (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) (x : DecryptGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit) :
    Except (ApiError AddrVal Unit) (List (BitVec 8)) × List (StoreCall AddrVal (List (BitVec 8))) :=
  messageDecryptSignal C S.spqr (serializeAddrVals (serviceIdParse uuidParse)) answers x.msg
    x.rem.val x.loc.val (coinsOf x.rest)

/-- The loaded current session, if `load_session` answered `Ok(Some r)` with one. -/
def loadedSession (answers : StoreAnswers (List (BitVec 8)) Unit) :
    Option (Session (List (BitVec 8))) :=
  match answers.loadSession with
  | .ok (some r) => r.currentSession
  | _ => none

/-- Tape bytes drawn: those of record decryption (`decryptDraws`, as in
`RecordDecryptGhost.draws`) on the loaded session when the version matches, else 0. -/
def DecryptGhost.draws (C : Crypto) (x : DecryptGhost) (answers : StoreAnswers (List (BitVec 8)) Unit) :
    Nat :=
  match loadedSession answers with
  | some s =>
    if s.state.version.toNat = x.msg.messageVersion.toNat then
      decryptDraws C s.state x.msg.senderRatchetKey x.rest
    else 0
  | none => 0

/-- `spqr::recv` panics on the loaded session's inputs (by the abstract panic set
`SpqrModel.recvPanics`), when the version check passes. -/
def DecryptGhost.recvPanics (S : SpqrModel) (x : DecryptGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit) : Prop :=
  match loadedSession answers with
  | some s =>
    s.state.version.toNat = x.msg.messageVersion.toNat ∧
      S.recvPanics s.state.pqRatchetState x.msg.pqRatchet
  | none => False

/-- **The binding spec of `session_message_decrypt_signal`** (`message_decrypt_signal`,
`session_management.rs:297–354`, on the hook stores). Normal return: for some store answers (those
in the trace), W0 does not panic, the trace grew by W0's calls with their answers, the sret holds
W0's result (`apiDecResultAt`), the borrowed message and addresses are unchanged, the tape advanced
by `draws`. Panic only on a failed allocation, or (with the loaded record in the trace) when W0
panics or `spqr::recv` panics on the loaded session's inputs.

On a panic, the guarantee is only that the trace extends `s0 ++ [load]`. "Nothing stored on panic"
is **not** guaranteed, because the triple-ratchet panic contracts (`recordDecryptSpec`, the spqr
hooks, `format_inner`, the allocation-panic hooks) allow arbitrary trace growth. The message and the
two addresses are separate blocks (`∗`): aliased borrowed inputs are out of scope. -/
def decryptSignalSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) : Spec DecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x8 = x.ret ∧ entryStack ≤ s.sp.toNat⌝ ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗
        logOff img ∗ stackAt s.sp entryStack ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            sf.trace = s0.trace ++ (x.model C S uuidParse answers).2.map (storeEvent encRecord answers)⌝ ∗
          apiDecResultAt A x.ret (x.model C S uuidParse answers).1 ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws C answers) ∗
          logOff img ∗ stackAt s0.sp entryStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              s0.trace ++ [loadEvent encRecord x.rem.val answers.loadSession] <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.recvPanics S answers))⌝ ∗
          anyHeap }
    img

/-! ## `session_message_encrypt` -/

/-- Ghost of an encrypt call (`ptext: &[u8]` `x0` / `x1`, `remote_address` `x2`, `local_address`
`x3`, `now: SystemTime` in `x4` (`tv_sec`) and `w5` (`tv_nsec`; the entry stores both,
`0x430e0..0x430fc`), sret `x8`, 248 bytes). -/
structure EncryptGhost where
  ret : BitVec 64
  ptA : BitVec 64
  ptext : List (BitVec 8)
  remA : BitVec 64
  rem : AddrGhost
  locA : BitVec 64
  loc : AddrGhost
  now : SystemTime
  /-- The tape position. -/
  cur : BitVec 64
  rest : List (BitVec 8)

/-- W0's result and call trace on the store answers `answers` (the SPQR coins = the whole remaining
tape, as `OtrEncryptGhost.model`). -/
def EncryptGhost.model (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) (x : EncryptGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit) :
    Except (ApiError AddrVal Unit) CiphertextMessage × List (StoreCall AddrVal (List (BitVec 8))) :=
  messageEncrypt C protoSignalCodec S.spqr (serializeAddrVals (serviceIdParse uuidParse)) answers
    x.ptext x.rem.val x.loc.val x.now x.rest

/-- The post-quantum state `spqr::send` is called with, if W0 reaches `OTR::encrypt` (steps 1–5 of
`messageEncrypt`: a loaded current session, `from_session_state` succeeds, the remote identity is
present, and an unacknowledged session is not stale); `none` otherwise. -/
def EncryptGhost.sendState (x : EncryptGhost) (answers : StoreAnswers (List (BitVec 8)) Unit) :
    Option (List (BitVec 8)) :=
  match loadedSession answers with
  | none => none
  | some s =>
    match execOk OutgoingTripleRatchet.fromSessionState s.state with
    | .error _ => none
    | .ok (otr, taken) =>
      if taken.remoteIdentity.isNone then none else
      match s.pendingPreKey with
      | none => some otr.pqrState
      | some items =>
        match (SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat).bind
            (·.checkedAddSecs maxUnacknowledgedSessionAge) with
        | none => none
        | some expiry => if expiry.lt x.now then none else some otr.pqrState

/-- Tape bytes drawn: `spqr::send`'s (`S.draws`) if it is reached, else 0. -/
def EncryptGhost.draws (S : SpqrModel) (x : EncryptGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit) : Nat :=
  match x.sendState answers with
  | some st => S.draws st x.rest
  | none => 0

/-- `spqr::send` panics on its inputs (by the abstract panic set `SpqrModel.sendPanics`), when
it is reached. -/
def EncryptGhost.sendPanics (S : SpqrModel) (x : EncryptGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit) : Prop :=
  ∃ st, x.sendState answers = some st ∧ S.sendPanics st x.rest

/-- **The binding spec of `session_message_encrypt`** (`message_encrypt`,
`session_management.rs:43–151`, on the hook stores). Precondition: a plaintext shorter than `2^32`
bytes (as `otrEncryptSpec`), a valid `SystemTime` (`tv_nsec < 10^9`, Rust's validity
invariant of `Nanoseconds`) and a non-null local address pointer (Rust's validity invariant of
`&ProtocolAddress`; `OTR::encrypt` gets it as `Option<&_>`, null niche, `otrEncryptSpec`).
Normal return: for some store answers (those in the trace), W0 does
not panic, the trace grew by W0's calls with their answers, the sret holds W0's result
(`apiEncResultAt`), the borrowed plaintext and addresses are unchanged, the tape advanced by
`draws`. Panic only on a failed allocation, or (with the load in the trace) when W0 panics or
`spqr::send` panics on its inputs.

On a panic, the guarantee is only that the trace extends `s0 ++ [load]`. "Nothing stored on panic"
is **not** guaranteed, because the triple-ratchet panic contracts (the reused `OTR::encrypt` /
`spqrSendSpec`, the spqr hooks, `format_inner`, the allocation-panic hooks) allow arbitrary trace
growth. The plaintext and the two addresses are separate blocks (`∗`): aliased borrowed inputs (e.g.
a plaintext inside an address name) are out of scope. -/
def encryptSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) : Spec EncryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s.readReg64 .x4 = x.now.tvSec ∧ (s.readReg64 .x5).setWidth 32 = x.now.tvNsec ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s.readReg64 .x8 = x.ret ∧ entryStack ≤ s.sp.toNat⌝ ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        memRegion x.ret 248 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s.sp entryStack ∗
        A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            sf.trace = s0.trace ++ (x.model C S uuidParse answers).2.map (storeEvent encRecord answers)⌝ ∗
          apiEncResultAt A x.ret (x.model C S uuidParse answers).1 ∗
          (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗ stackAt s0.sp entryStack ∗
          A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              s0.trace ++ [loadEvent encRecord x.rem.val answers.loadSession] <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers))⌝ ∗
          anyHeap }
    img

/-! ## Encrypt with SPQR off (D2; for the end-to-end SM theorem) -/

/-- **The loaded record's current session, if any, has an empty post-quantum state** (SPQR off:
`OutgoingTripleRatchet.fromSessionState` then hands `spqr::send` the empty state). -/
def RecordPqEmpty (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s → s.state.pqRatchetState = []

/-! ## Guards (kernel-checked) -/

set_option maxRecDepth 200000 in
open ProofLib.ProgramReflection in
/-- Guard: `tripleRatchetExterns` (under `Rust.withPanics`) hands each store hook, time stub and
`String::clone` name to `abs`. -/
theorem tripleRatchetExterns_stores_abs (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    publicApiStubNames.map (Rust.withPanics (tripleRatchetExterns C ctl abs)) =
      publicApiStubNames.map abs := by
  rfl_kernel

end CryptoVerification.LibsignalPublicApi
