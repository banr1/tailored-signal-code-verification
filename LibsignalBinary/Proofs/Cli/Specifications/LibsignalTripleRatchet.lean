/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import GeneratedLean.LibsignalSessionObj

/-!
# CLI Triple Ratchet Specifications and Verification Statements

Defines entry symbols, machine-level specifications (`spqrSendSpec`, `tryDecryptSpec`,
`otrEncryptSpec`, `recordDecryptSpec`), and verification statement predicates for the `<Coins>`
instantiations in `libsignalSessionImage`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol names -/

/-- `try_decrypt_with_state::<HookRng>` (image offset `(ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<signal_session_ratchet::Coins>")`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName : String :=
  "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"

/-- `OutgoingTripleRatchet::encrypt::<HookRng>` (`(ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<signal_session_ratchet::Coins>")`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName : String :=
  "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>"

/-- The in-image `spqr::send::<HookRng>` (`(ls_off% "spqr::send::<signal_session_ratchet::Coins>")`, 3436 instructions). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName : String := "spqr::send::<libsignal_cli_ratchet::Coins>"

set_option linter.unusedVariables false in
/-- The contract of `spqr::send::<HookRng>`: `send state tape`, the tape advanced by
`draws state tape ≤ tape.length`. Panics only on `S.sendPanics state tape` or a failed
allocation; a normal return happens only when `¬ S.sendPanics state tape`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    Spec SendCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.st.v⌝ ∗ x.st.at A ∗ memRegion x.ret 72 ∗
          CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ A.pool ∗ stackAt s.sp spqrSendStack
      post := fun x s0 sf =>
        ⌜S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ S.sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A ∗
          spqrSendResultAt A x.ret (S.send x.st.bytes x.rest) ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (S.draws x.st.bytes x.rest) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp spqrSendStack
      onPanic := fun x s0 sf =>
        ⌜(allocFailedIn s0 sf ∨ S.sendPanics x.st.bytes x.rest) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- **Named hypothesis `CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk`**: the in-image `spqr::send::<HookRng>` (3436 instructions;
its closure is 133 in-image functions, all of `spqr`, `prost` and `bytes`) meets `CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec`,
not verified on non-empty states. It is stated **for the given `abs`**: `TripleRatchetHooks` contracts the
allocator hooks its closure calls (`AllocHooks`, `allocZeroed`; `libsignal_session_rng_fill`,
`memcpy` / `memmove` / `memset`, SHA-256 compression and the panic entry points are concrete). On a
non-empty state its closure also reaches these extern stubs, which go to `abs` with no contract
here:
* libcrux ML-KEM-768 `incremental::KeyPairCompressedBytes::from_seed` / `pk1` / `pk2` and
  `incremental::encapsulate1`; `libcrux_hmac::hmac`;
* `std::sync::Once::call` (the `cpufeatures` init), `RawVec<Vec<u8>>::grow_one`,
  `RawVec<u8>::grow_one`;
* the no-hook stubs `__aarch64_ldadd8_rel` and `log::Log::log` (behind `MAX_LOG_LEVEL_FILTER`,
  `logOff`).
So discharging it needs facts about `abs` on these names beyond `TripleRatchetHooks`. The empty-state
instance needs none: `SpqrSendEmptyRunStmt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName) (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img)

/-- `CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec` restricted to an empty state (`x.st.bytes = []`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    Spec SendCall :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img with
    pre := fun x s => ⌜x.st.bytes = []⌝ ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img).pre x s }

/-- **`CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk` on an empty state, without assuming `CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk`.** For a model meeting
`SpqrModel.SendEmptyOk`, the in-image `spqr::send::<HookRng>` meets `CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec` whenever the state
is empty. On that path it calls the in-image `spqr::decode_state` (`decodeStateEmptySpec`), then
`memcpy`, and `__rust_dealloc` only behind a test that `decodeStateEmptyAt` makes false (`+0xc0`);
no libcrux stub. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.SendEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img)

set_option linter.unusedVariables false in
/-- **The binding spec of `try_decrypt_with_state::<HookRng>`** (`session_management.rs:566–606`).
Registers: sret `x0`, `x1` = SS, `x2` / `x3` = remote / local address, `x4` = message, `w5` =
message type; `w6` (`CurrentOrPrevious`, logging only) and `x7` (`&mut HookRng`, a ZST) are not
read. Precondition: the remote IK is not the local IK (`DEV-LS28`; then `self_session = false`, as in
the model), every stored skipped-key seed is 32 bytes (`SeedsLen32`, `DEV-LS9`), fewer than `2^32`
receiver chains (else `grow_one` in `dh_ratchet_step` can overflow the capacity and panic, which the
model does not; libsignal keeps at most 5), and the stack budget does not wrap through address 0
(`rootStack ≤ sp`: `dh_ratchet_step` passes stack copies of the root key at
`sp_entry − 0x230` / `− 0x140` to `RootKey::create_chain`, whose `Hkdf::extract` reads a null salt
pointer as `None`, `0x1ad64: cmp x1, #0; csel`, and would run HKDF unsalted). Normal return only if
the model does not panic, in **both** arms (`Ok` and `Err`): SS holds the model's final state with a
ghost `G'` related by `AfterTryDecrypt` (on `Err` the receiver chains and the pq state were taken, as in the
model), the sret the model's result, the borrowed addresses and message unchanged, the tape advanced
by `decryptDraws`. Panic only if the model panics, `spqr::recv` panics on the model's inputs
(`S.recvPanics` of SS's pq state and the message's `pq_ratchet`), or the allocator failed. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
          s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
          (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
          x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
          x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
        sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
        memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗
        A.pool
      post := fun x s0 sf =>
        ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidParse).1.toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.model C S uuidParse).2) ∗
        vecResultAt A x.ret (x.model C S uuidParse).1 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
        logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.recvPanics x.st.pqRatchetState x.msg.pqRatchet ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

set_option linter.unusedVariables false in
/-- **The binding spec of `OTR::encrypt::<HookRng>`** (`triple_ratchet.rs:86–135`): sret `x0`,
`x1` = OTR, `x2` / `x3` = plaintext (`< 2^32` bytes), `x4` = local address or 0, `x5` = remote
address; `x6` (`&mut HookRng`) not read. Normal return only if the model does not panic: the OTR
holds the model's final value (new pq `Vec` on success), the sret the model's result (using the
concrete codec `protoSignalCodec`), the tape advanced by `S.draws` (only `spqr::send` draws). Panic
only if the model panics, `spqr::send` panics on the model's inputs (`S.sendPanics` of the OTR's pq
state and the tape), or the allocator failed. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec OtrEncryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.o ∧ s.readReg64 .x2 = x.ptA ∧
          (s.readReg64 .x3).toNat = x.ptext.length ∧ x.ptext.length < 2 ^ 32 ∧
          s.readReg64 .x4 = (if x.loc.isSome then x.locA else 0#64) ∧
          (x.loc.isSome → x.locA ≠ 0#64) ∧ s.readReg64 .x5 = x.remA⌝ ∗
        otrAt A x.o x.pqCap x.pqPtr x.ot ∗ (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗
        protocolAddressAt A x.rem x.remA ∗ memRegion x.ret 120 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
        logOff img ∗ stackAt s.sp rootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A x.o pqCap' pqPtr' (x.model C S uuidParse).2) ∗
        signalMessageResultAt A (utf8 "encrypt") x.ret (x.model C S uuidParse).1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (S.draws x.ot.pqrState x.rest) ∗
        logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- **Decrypt.** For an image of `libsignalSessionImage` and abstract hooks meeting `TripleRatchetHooks`,
the compiled `try_decrypt_with_state::<HookRng>` meets `CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec`. Named hypotheses:
`SpqrRecvOk` and `TripleRatchetHooks.aesDec`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → SpqrRecvOk C A ctl S abs img → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)

/-- **Decrypt, empty post-quantum state (without `SpqrRecvOk`).** For a model meeting
`SpqrModel.RecvEmptyOk` and a session whose pq state is empty, `try_decrypt_with_state::<HookRng>`
meets `CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec` without `SpqrRecvOk`: the `spqr::recv` call is crossed with
`SpqrRecvEmptyRunStmt`. Named hypothesis: `TripleRatchetHooks.aesDec`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜x.st.pqRatchetState = []⌝ ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).pre x s }

/-- **Encrypt (`OTR::encrypt`).** `OTR::encrypt::<HookRng>` meets `CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec`. Named hypotheses:
`CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk` and `TripleRatchetHooks.aesEnc`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.OtrEncryptRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk C A ctl S abs img → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img)

/-- **Encrypt (`OTR::encrypt`), empty post-quantum state (without `CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk`).** For a model meeting
`SpqrModel.SendEmptyOk` and an OTR whose pq state is empty, `OTR::encrypt::<HookRng>` meets
`CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec` without `CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk`: the `spqr::send` call is crossed with
`CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmptyRunStmt`. Named hypothesis: `TripleRatchetHooks.aesEnc`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.OtrEncryptEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.SendEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      { CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s => ⌜x.ot.pqrState = []⌝ ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img).pre x s }

/-- `session_message_decrypt_signal` (`(ls_off% "signal_session_ratchet::decrypt_signal")`, 2451 instructions): the session crate's
`message_decrypt_signal::<HookRng>` with `try_decrypt_from_record` inlined. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName : String := "libsignal_cli_ratchet::decrypt_signal"

/-- Region entry `+0x1a8` (`(ls_off% "signal_session_ratchet::decrypt_signal" + 424)`): just after `load_session` returned `Some(record)` and the
record was assembled at `sp + 0x120` (`+0x198..+0x1a4`, `memcpy` 312 B to `sp + 0x158`); the next
instructions start `record.session_state()` (`+0x1c4: ldr x9, [sp, #0x138]; cmn x9, #1`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1a8#64

/-- Region exit `+0x1f50` (`(ls_off% "signal_session_ratchet::decrypt_signal" + 8016)`): after the `errs: Vec<SignalProtocolError>` was dropped
(`+0x1e8c..+0x1f4c`), where the code branches on the result tag `x28` (`+0x1f60: cmn x28, #2`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1f50#64

set_option linter.unusedVariables false in
/-- **The binding region contract of `try_decrypt_from_record`** (`CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry` →
`CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit`; Whisper, current session only, logging off).

Entry state (established by `message_decrypt_signal`'s prefix, `+0x0..+0x1a8`): the frame of
`sub sp, #0xe80` under `x29`; the record at `sp + 0x120` with `previous_sessions.len = 0` and
`current_session = Some(st)` (`sessionStateAt` at `sp + 0x138`, whose word 0 is never the `None`
niche `-1`); the argument spills `sp + 0xe0` (message) and `sp + 0xf0` (local address), `x19` =
remote address; `x23 = sp + 0x5f0`, `x24 = sp + 0xca0` (scratch pointers live into the region);
the region's scratch `sp .. sp + 0xa0` and `sp + 0x4b0 .. sp + 0xe00`; the stack below `sp`.
Preconditions as `CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec` for `st` (`DEV-LS28` remote IK ≠ local IK, `DEV-LS9` `SeedsLen32`,
fewer than `2^32` receiver chains, and `rootStack ≤ sp`: the region calls `try_decrypt_with_state`
at the same `sp`).

Postcondition (normal arrival at the exit only if the model does not panic): `sp`, `x29`, `x27`
unchanged, `x26 = sp + 0xa0`, `x28` is the result's word 0 (`recordResultTag`); the result in the
slot `sp + 0x4b0` (`recordResultAt`); **all or nothing**: on `Ok` the record holds the model's
updated session (the clone, moved in by `set_session_state`; the old current session freed), on
`Err` it holds the **same** session with the **same** ghost (`tryDecryptFromRecord_error`); the
borrowed addresses and message unchanged; the tape advanced by `draws`; every scratch byte, `errs`,
the clone and the losing session freed back to `memRegion` / the pool.

Panic only if the model panics (`try_decrypt_with_state` panics on the clone), `spqr::recv` panics
on the model's inputs (only when the version check passes), or the allocator failed (the clone
allocates). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec RecordDecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.spAligned = true ∧ s.readReg64 .x27 = x.sret ∧ s.readReg64 .x19 = x.remA ∧
          s.readReg64 .x23 = s.sp + 0x5f0#64 ∧ s.readReg64 .x24 = s.sp + 0xca0#64 ∧
          x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
          x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
        memRegion s.sp 0xa0 ∗
        ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (s.sp + 0x138#64) x.G x.st ∗
        memRegion (s.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace ∧ sf.sp = s0.sp ∧
          sf.readReg64 .x29 = s0.readReg64 .x29 ∧ sf.readReg64 .x27 = x.sret ∧
          sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧
          sf.readReg64 .x28 = recordResultTag (x.model C S uuidParse).1⌝ ∗
        memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (match (x.model C S uuidParse).1 with
         | .ok _ => ∃∗ G' : SessionGhost, ⌜x.G.AfterRecordDecrypt G'⌝ ∗
             sessionStateAt A (s0.sp + 0x138#64) G' (x.model C S uuidParse).2
         | .error _ => sessionStateAt A (s0.sp + 0x138#64) x.G x.st) ∗
        recordResultAt A (s0.sp + 0x4b0#64) (x.model C S uuidParse).1 ∗
        memRegion (s0.sp + 0x4e0#64) 0x920 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C) ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model C S uuidParse).1 = .error .panic ∨
            (x.st.version.toNat = x.msg.messageVersion.toNat ∧
              S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- **Decrypt from a record (`try_decrypt_from_record`).** The `try_decrypt_from_record` region of
the compiled `message_decrypt_signal::<HookRng>` meets `CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec`. Named hypotheses:
`SpqrRecvOk` and `TripleRatchetHooks.aesDec`, as for `CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.RecordDecryptRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → SpqrRecvOk C A ctl S abs img → Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg img C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)

/-- **Decrypt from a record, empty post-quantum state (without `SpqrRecvOk`).** As
`CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt`: for a model meeting `SpqrModel.RecvEmptyOk` and a current session whose
pq state is empty, the region meets `CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec` without `SpqrRecvOk`. Named hypothesis:
`TripleRatchetHooks.aesDec`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.RecordDecryptEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg img C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      { CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜x.st.pqRatchetState = []⌝ ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).pre x s }

end CryptoVerification.LibsignalTripleRatchet
