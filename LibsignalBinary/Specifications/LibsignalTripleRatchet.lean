/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSpqr
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop

/-!
# Triple-ratchet encrypt / decrypt and `SignalMessage` parse on the compiled session image

**Trusted in part.** The theorems of `Computational/Theorems/` use only the following definitions
from this file (see `Computational/docs/TRUSTED_BASE.md`):
- The SPQR interface: the structure `SpqrModel` and its fields `send`, `recv`, `sendPanics`,
  `recvPanics` (the PQXDH-mode and SPQR V1 theorems).
- Concrete hooks and a helper: `pubFromSecretHook`, `diffieHellmanHook`, `zeroizeSecretHook`,
  `readVec32` (rows of the CLI's hook table `cliHookTablePlaced`, `SignalSession/CliRun.lean`,
  which the statements about the CLI's ELF use).
Everything else here, the layered program `tripleRatchetProg` / `tripleRatchetExterns`,
`entryOf` and `rngFillHook` included, is checked by Lean.

This file states what the compiled AArch64 code of libsignal's triple ratchet (the Double Ratchet
combined with the post-quantum SPQR ratchet) does, in terms of the pure session model
(`LibsignalBinary/Specifications/CryptoGames/Ratchet/LibsignalSession.lean`). It defines the
session program `tripleRatchetProg` (a loaded session image `img` with the base hooks
`sessionExterns` plus the triple-ratchet hooks), the contracts of the callees it does not verify,
the Hoare specs of the two entry points below and of the inlined `try_decrypt_from_record` region.
The run statements (`...RunStmt`) the proofs establish are proof-side, in
`LibsignalBinary/Proofs/SpecLemmas/LibsignalTripleRatchetProofDefs.lean`. Memory layouts and
constants are in
`LibsignalBinary/Specifications/LibsignalTripleRatchetRepr.lean`; the image guards are in
`LibsignalBinary/Specifications/LibsignalTripleRatchetGuards.lean`.

Glossary: ABI = application binary interface; SS = `SessionStructure`;
OTR = `OutgoingTripleRatchet`; SPE = `SignalProtocolError`; sret = the caller-provided
structure-return buffer (here `x0` for the two `HookRng`-generic entry points, `x8` otherwise);
SPQR / `spqr` = the Sparse Post-Quantum Ratchet; ML-KEM-768 = Module-Lattice-Based
Key-Encapsulation Mechanism (`ML-KEM-768`); RNG = random number generator; UUID = universally
unique identifier; ZST = zero-sized type; tape = the deterministic byte stream `HookRng` draws from
(`libsignal_session_rng_fill`, `DEV-E8`); `abs` = the abstract hooks (any functions meeting the
contracts of `TripleRatchetHooks`); IK = identity key; `C` = the session model's cryptographic primitives
(`Crypto`: SHA-256 (Secure Hash Algorithm 256-bit) compression `F`, AES-256-CBC (Advanced
Encryption Standard with 256-bit keys in Cipher Block Chaining mode) block cipher `E` / `D`,
X25519 (Curve25519 elliptic-curve Diffie-Hellman) `X`, and public-key derivation `pubKey`);
`A` = the Rust allocator model (`RustAlloc`); ghost = the logical (proof-only) parameters a spec
is stated over; HMAC = Hash-based Message Authentication Code; HKDF = HMAC-based Key Derivation
Function.

## The entry points (register conventions differ; see each spec)

| Entry point (image offset) | Spec | Session model |
| --- | --- | --- |
| `session_management::try_decrypt_with_state::<HookRng>` (`0x3439c`) | `tryDecryptSpec` | `SessionState.tryDecryptWithState` |
| `OutgoingTripleRatchet::encrypt::<HookRng>` (`0x33e0c`) | `otrEncryptSpec` | `OutgoingTripleRatchet.encrypt` |

The specs of `OutgoingTripleRatchet::from_session_state`, `::apply_to_session_state` and
`<SignalMessage as TryFrom<&[u8]>>::try_from` (`otrFromSpec`, `otrApplySpec`, `tryFromSpec`) are
proof-side, in `LibsignalBinary/Proofs/SpecLemmas/LibsignalTripleRatchetProofDefs.lean`.

In addition, `recordDecryptSpec` is a region contract for `try_decrypt_from_record`, which is
inlined into `session_message_decrypt_signal` (model `SessionState.tryDecryptFromRecord`).

## Trusted boundary (`tripleRatchetExterns`)

* everything in `LibsignalSession.sessionExterns`: SHA-256 compression, `memcpy` /
  `memmove` / `memset`, the no-alloc shim, `black_box`, `Vec::remove::assert_failed`, the allocator;
* concrete hooks: X25519 `diffie_hellman` = `C.X` and `PublicKey::from(&StaticSecret)` = `C.pubKey`,
  the two secret drops = zeroize, `libsignal_session_rng_fill` = the deterministic tape (`DEV-E8`);
* abstract hooks (`abs`, contracts in `TripleRatchetHooks`): the allocator (`AllocHooks A`, and
  `__rust_alloc_zeroed` from the same `A`, `rustAllocZeroedSpec`), AES-256-CBC encrypt / decrypt
  (named hypotheses matching the byte-level `aesCbcEncrypt` / `aesCbcDecrypt` functions),
  `alloc::fmt::format_inner` and `core::fmt::write` into a `String` (contracted to produce some
  owned `String`, since only error texts depend on them);
* no hook (reaching them halts, which every spec forbids, so the proofs must show they are not
  reached): `__aarch64_ldadd8_rel` / `_relax`, `__aarch64_cas8_acq_rel`, `log::Log::log` (logging
  off: `logOff`);
* the in-image `spqr::send::<HookRng>` and `spqr::recv` are not verified on non-empty post-quantum
  states: the general encrypt / decrypt statements take the named hypotheses `SpqrSendOk` /
  `SpqrRecvOk`, `subroutine_ok` statements in terms of `SpqrModel.send` / `SpqrModel.recv`
  (panics: `SpqrModel.sendPanics` / `recvPanics`), stated for the given `abs`. On a non-empty state
  their closures reach libcrux ML-KEM-768 / HMAC stubs with no contract here (lists at
  `SpqrSendOk` / `SpqrRecvOk`). On an empty state they reach none of them, so the proofs
  establish the empty-state instances without the hypotheses (proof-side statements in
  `LibsignalBinary/Proofs/SpecLemmas/LibsignalTripleRatchetProofDefs.lean`);
* the Rust panic entry points = `Rust.withPanics`; every other stub = `abs` (no contract: a proof
  can only cross it through `SpqrSendOk` / `SpqrRecvOk`).

`libsignal-core`, `bytes`, `uuid`, `prost` and `spqr` are whole crates in the image, so their
functions are in-image code that the proofs execute, not hooks: in particular
`<PublicKey as TryFrom<&[u8]>>::try_from`, `PrivateKey::serialize`, `<ProtocolAddress as
Display>::fmt` (which calls `core::fmt::write`), `ServiceId::parse_from_service_id_string` (which
calls `Uuid::try_parse`), `bytes::panic_advance`, `Uuid::try_parse`, prost's `decode_varint_slow`
and `DecodeError::from` / `push`, `spqr::decode_state` and `spqr::recv` (guard
`inImageCallees_code`).

## Preconditions

Local IK ≠ remote IK (`DEV-LS28`: else upstream's `self_session` is true and `max_forward_jumps`
differs from the model's); logging off; addresses parsed by `serviceIdParse uuidParse` (the specs
are generic in the UUID parser; the statements instantiate them at the uuid 1.26.1 model
`uuidTryParse`, which the in-image `Uuid::try_parse` computes). Sizes: plaintexts `< 2^32`, the
parsed buffer `< 2^32`, message byte strings `< 2^40` (`signalMessageAt`), decrypt: fewer than
`2^32` receiver chains. Decrypt only (`DEV-LS9`):
every stored skipped-key seed is 32 bytes (`SeedsLen32`), as libsignal itself always stores them.

## Main definitions

* `tripleRatchetExterns` / `tripleRatchetProg`: the hook table and the program (image + hooks +
  panics) every statement runs.
* `diffieHellmanHook`, `pubFromSecretHook`, `zeroizeSecretHook`, `rngFillHook`: the concrete hooks
  (X25519, public-key derivation, secret zeroization, the RNG tape).
* `aesEncSpec` / `aesDecSpec`, `formatInnerSpec`, `fmtWriteSpec`, `rustAllocZeroedSpec`, collected
  in `TripleRatchetHooks`: the contracts assumed of the abstract hooks.
* `SpqrModel`: the abstract SPQR functions on serialized bytes; `spqrSendSpec` / `spqrRecvSpec`:
  the contracts of the in-image `spqr::send` / `spqr::recv`; `SpqrSendOk` / `SpqrRecvOk`: the named
  hypotheses that they meet them.
* `SeedsLen32`: the decrypt precondition that stored skipped-key seeds are 32 bytes (`DEV-LS9`).
* `tryDecryptSpec`, `otrEncryptSpec`: the binding specs of the two entry points (each with its
  ghost structure and `.model`).
* `region_ok` and `recordDecryptSpec`: the region-triple judgment and the region contract of the
  inlined `try_decrypt_from_record`.

## Main statements

* `tripleRatchetExterns_abs` (kernel-checked guard): the abstract hook names reach `abs` unchanged.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-! ## Symbol names -/

/-- `try_decrypt_with_state::<HookRng>` (image offset `0x3439c`). -/
abbrev tryDecryptName : String :=
  "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"
/-- `OutgoingTripleRatchet::from_session_state` (`0xb794`). -/
abbrev otrFromName : String :=
  "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"
/-- `OutgoingTripleRatchet::encrypt::<HookRng>` (`0x33e0c`). -/
abbrev otrEncryptName : String :=
  "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>"
/-- `OutgoingTripleRatchet::apply_to_session_state` (`0xbcb0`). -/
abbrev otrApplyName : String :=
  "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state"
/-- `<SignalMessage as TryFrom<&[u8]>>::try_from` (`0x25868`). -/
abbrev tryFromName : String :=
  "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"
/-- The in-image `spqr::send::<HookRng>` (`0x3085c`, 3436 instructions). -/
abbrev spqrSendName : String := "spqr::send::<libsignal_session::HookRng>"

/-- `<x25519_dalek::StaticSecret>::diffie_hellman` (stub `0x6f024`). -/
abbrev dhName : String := "<x25519_dalek::x25519::StaticSecret>::diffie_hellman"
/-- `<x25519_dalek::PublicKey as From<&StaticSecret>>::from` (stub `0x6f010`). -/
abbrev pubFromSecretName : String :=
  "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"
/-- `<StaticSecret as Drop>::drop` (stub `0x6ef24`). -/
abbrev staticDropName : String := "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop"
/-- `<SharedSecret as Drop>::drop` (stub `0x6f028`). -/
abbrev sharedDropName : String := "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop"
/-- `libsignal_session_rng_fill` (stub `0x6efec`; `third_party/libsignal/libsignal-session/src/lib.rs:50–72`). -/
abbrev rngFillName : String := "libsignal_session_rng_fill"
/-- `signal_crypto::aes_cbc::aes_256_cbc_encrypt` (stub `0x6f004`). -/
abbrev aesEncName : String := "signal_crypto::aes_cbc::aes_256_cbc_encrypt"
/-- `signal_crypto::aes_cbc::aes_256_cbc_decrypt` (stub `0x6f008`). -/
abbrev aesDecName : String := "signal_crypto::aes_cbc::aes_256_cbc_decrypt"
/-- `alloc::fmt::format::format_inner` (stub `0x6ef30`). -/
abbrev formatInnerName : String := "alloc::fmt::format::format_inner"
/-- `core::fmt::write` (stub `0x6eee8`; the only call in the triple-ratchet closure is from the
in-image `<ProtocolAddress as Display>::fmt`, `+0x38`). -/
abbrev fmtWriteName : String := "core::fmt::write"
/-- `__rust_alloc_zeroed` (stub `0x6effc`; called by the in-image `spqr::send::<HookRng>`,
`BytesMut::zeroed`, `Authenticator::new` / `update`, `EkSentCt1Received::recv_ct2_chunk` and
`kdf::hkdf_to_vec`, i.e. only on non-empty post-quantum paths and in `spqr::send`'s own code). -/
abbrev allocZeroedName : String := "__rustc::__rust_alloc_zeroed"

/-- Stubs with no hook (logging is off, and atomic reference-count stubs are unused on borrowed/owned
paths): the proofs must show they are not reached. -/
def noHookNames : List String :=
  ["__aarch64_ldadd8_rel", "__aarch64_ldadd8_relax", "__aarch64_cas8_acq_rel",
   "<log::__private_api::GlobalLogger as log::Log>::log"]

/-! ## In-image callees (executed code, not hooks)

`libsignal-core`, `bytes`, `uuid`, `prost` and `spqr` are whole crates in the image, so these are
code the proofs execute (no hook; guard `inImageCallees_code`). -/

/-- `<libsignal_core::curve::PublicKey as TryFrom<&[u8]>>::try_from` (`0x3eadc`, 68 instructions;
`core/curve.rs:193`, `PublicKey::deserialize` (`:84–105`) inlined). -/
abbrev pkTryFromName : String :=
  "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from"
/-- `ServiceId::parse_from_service_id_string` (`0x3e4c0`, 53 instructions; `core/address.rs:263–280`;
model `serviceIdParse uuidTryParse`). -/
abbrev parseSidName : String := "<libsignal_core::address::ServiceId>::parse_from_service_id_string"
/-- `bytes::panic_advance` (`0x3f5a8`, 14 instructions; ends in `core::panicking::panic_fmt`). -/
abbrev panicAdvanceName : String := "bytes::panic_advance"
/-- `<ProtocolAddress as Display>::fmt` (`0x3f404`, 18 instructions; `core/address.rs:815–819`,
`write!(f, "{}.{}", self.name, self.device_id)`, i.e. one `core::fmt::write` call). -/
abbrev addrDisplayName : String :=
  "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt"
/-- `<libsignal_core::curve::PrivateKey>::serialize` (`0x3e6dc`, 21 instructions; `core/curve.rs:253–256`,
the 32 key bytes `to_vec()`). -/
abbrev privSerializeName : String := "<libsignal_core::curve::PrivateKey>::serialize"
/-- `<uuid::Uuid>::try_parse` (`0x48a80`, 24 instructions, calling `uuid::parser::try_parse`,
`0x4930c`, 134 instructions; uuid 1.26.1 `src/parser.rs:110–112`; model
`LibsignalTripleRatchetRepr.uuidTryParse`). Called only by the in-image
`ServiceId::parse_from_service_id_string` (`+0x3c` and `+0x84`, both on a 36-byte input). -/
abbrev uuidTryParseName : String := "<uuid::Uuid>::try_parse"
/-- `prost`'s `decode_varint_slow::<&mut &[u8]>` (`0x4db38`, 112 instructions). -/
abbrev varintSlowName : String := "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>"
/-- `<DecodeError as From<DecodeErrorKind>>::from` (`0x4ada0`, 23 instructions). -/
abbrev decodeErrorFromName : String :=
  "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"
/-- `<DecodeError>::push` (`0x4aaa8`, 32 instructions). -/
abbrev decodeErrorPushName : String := "<prost::error::DecodeError>::push"
/-- `spqr::recv` (`0x5462c`, 759 instructions; `spqr/src/lib.rs:355`; called only by
`try_decrypt_with_state::<HookRng>`). -/
abbrev spqrRecvName : String := "spqr::recv"
/-- `spqr::decode_state` (`0x5349c`, 745 instructions; `spqr/src/lib.rs:495–505`; called by
`spqr::send::<HookRng>` (first, `+0x4c`), `spqr::current_version` and `spqr::recv`). -/
abbrev decodeStateName : String := "spqr::decode_state"

/-- The eleven in-image callees above (guard `inImageCallees_code` checks they are code in the
image, not stubs). -/
def inImageCalleeNames : List String :=
  [pkTryFromName, parseSidName, panicAdvanceName, addrDisplayName, privSerializeName,
   uuidTryParseName, varintSlowName, decodeErrorFromName, decodeErrorPushName, spqrRecvName,
   decodeStateName]

/-! ## Concrete hooks -/

/-- The 32 bytes at `a` as a vector. -/
def readVec32 (m : Memory) (a : BitVec 64) : List.Vector (BitVec 8) 32 :=
  ⟨m.readBytes a 32, Memory.readBytes_length m a 32⟩

/-- `<StaticSecret>::diffie_hellman(self = x0, their_public = x1) -> SharedSecret` (sret `x8`):
`mem[x8 .. +32] := X mem[x0 .. +32] mem[x1 .. +32]` (the secret is already clamped by
`calculate_agreement`); `pc := lr`. -/
def diffieHellmanHook (X : Ratchet.X25519Fn) (s : State) : State :=
  let r := X (readVec32 s.mem (s.readReg64 .x0)) (readVec32 s.mem (s.readReg64 .x1))
  retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8) r.toList)) s

/-- `<x25519_dalek::PublicKey as From<&StaticSecret>>::from(x0 = &secret)` (sret `x8`, 32 bytes;
tail-called by the in-image `derive_public_key_bytes`, `0x3db4c`): `mem[x8 .. +32] := pubKey
mem[x0 .. +32]` (`Crypto.pubKey`; the secret is clamped inline before the tail call);
`pc := lr`. -/
def pubFromSecretHook (pubKey : PubKeyFn) (s : State) : State :=
  let r := pubKey (readVec32 s.mem (s.readReg64 .x0))
  retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x8) r.toList)) s

/-- `<StaticSecret as Drop>::drop` / `<SharedSecret as Drop>::drop` (`x0 = self`, zeroize):
`mem[x0 .. +32] := 0`; `pc := lr`. -/
def zeroizeSecretHook (s : State) : State :=
  retHook (fun s => s.setMem (s.mem.writeBytes (s.readReg64 .x0) (List.replicate 32 0#8))) s

/-- `libsignal_session_rng_fill(dst = x0, len = x1)` (`src/lib.rs:50–72`, no return value) on the
tape whose control block is at `ctl` (cursor `cur`, remaining count `rem`, `tapeAt`): writes the
next `k = min len rem` tape bytes then `len - k` zeros at `dst`, and advances the cursor by `k`;
`pc := lr` (`DEV-E8`). -/
def rngFillHook (ctl : BitVec 64) (s : State) : State :=
  let dst := s.readReg64 .x0
  let len := (s.readReg64 .x1).toNat
  let cur := s.mem.read64 ctl
  let rem := (s.mem.read64 (ctl + 8#64)).toNat
  let k := min len rem
  let bytes := s.mem.readBytes cur k ++ List.replicate (len - k) 0#8
  let m := ((s.mem.write64 ctl (cur + BitVec.ofNat 64 k)).write64 (ctl + 8#64)
    (BitVec.ofNat 64 (rem - k))).writeBytes dst bytes
  retHook (fun s => s.setMem m) s

/-! ## The program -/

/-- **The extern hooks of the triple-ratchet session program**: the base hooks (`sessionExterns`, run
here with no allocator so that its answer does not depend on `abs`; the allocator names fall through
to `abs` at the end, just as in `LibsignalSession`), then the concrete ones above, the no-hook names
= `none`, and `abs` for everything else (the allocator and the abstract hooks of `TripleRatchetHooks`). -/
def tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : String → Option (State → State) := fun sym =>
  match CryptoVerification.LibsignalSession.sessionExterns C.F (fun _ => none) sym with
  | some h => some h
  | none =>
    if sym = dhName then some (diffieHellmanHook C.X)
    else if sym = pubFromSecretName then some (pubFromSecretHook C.pubKey)
    else if sym = staticDropName ∨ sym = sharedDropName then some zeroizeSecretHook
    else if sym = rngFillName then some (rngFillHook ctl)
    else if noHookNames.contains sym then none
    else abs sym

/-- The triple-ratchet session program: the loaded session image, `tripleRatchetExterns`, panics via
`Rust.withPanics`. -/
abbrev tripleRatchetProg (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Program :=
  Program.ofImage img (Rust.withPanics (tripleRatchetExterns C ctl abs))

/-- The entry of a function, by symbol name. -/
abbrev entryOf (img : Obj.Image) (name : String) : BitVec 64 := (Program.ofImage img).fnAddr name

/-- Logging off: `log::MAX_LOG_LEVEL_FILTER` holds 0 (`LibsignalSession.logFilterAddr`). -/
abbrev logOff (img : Obj.Image) : SepProp :=
  CryptoVerification.LibsignalSession.logFilterAddr img ↦₆₄ 0#64

/-! ## Stack budgets (bytes below `sp`; `spqr::recv` measured statically) -/

/-- Stack for the abstract hooks without a stated bound of their own (AES, `format_inner`,
`core::fmt::write`). -/
abbrev extHookStack : Nat := 2 ^ 14
/-- Stack for `spqr::recv` (`SpqrRecvOk`; ML-KEM-768 decapsulation on
non-empty states). `spqr::recv` is in the image (own frame 4992 bytes: `stp x29, x30, [sp, #-0x60]!;
sub sp, #0x1000; sub sp, #0x320`; on an empty state it calls `spqr::decode_state`, own frame 1392
bytes), but much of its non-empty closure is not (libcrux stubs), so the bound comes from a static
measurement.

Measured worst case: **18160 bytes**, using `third_party/libsignal/libsignal-session/tools/stackdepth.py`
(checked by Lean). Method: sum of the `sp` decrements of each function, maximized over the `bl` / `b` call
graph. Inputs:
* the `aarch64-unknown-linux-gnu` release rlibs built with the image's profile (`codegen-units=1`,
  `panic=abort`, soft AES / SHA-2 backends);
* the Rust 1.98.1 `core` / `alloc` / `std` / `compiler_builtins` rlibs.
The call graph from `spqr::recv` has 199 functions, no recursion and no dynamic `sp` adjustment.
Panic / formatting / logging entry points are terminal; following formatting changes nothing.
Worst path: `spqr::recv` (frame 4992), then `States::recv` (4192), then
`EkSentCt1Received::recv_ct2_chunk` (2496), then libcrux
`ind_cca::incremental::neon::decapsulate_compressed_key` (5344), then `keccak2::<136, 31>` (1040),
then `KeccakState::squeeze2::<136>` (96); the frames sum to 18160.
The boundary items stay below the worst case:
* the two indirect calls: `Once::call` → the cpufeatures `getauxval` init (about 12.8 KB) and
  `bytes::merge` → the `Bytes` vtable drop (about 8 KB);
* the out-of-crate allocator / `mem*` calls: each is reached at a depth of at most
  18160 bytes, and their own (libc) frames are not counted.
The same method gives `spqr::send::<HookRng>` an own frame of 8064 bytes, which is what
`TripleRatchetRunTest` measures on the image. `2 ^ 17` is 7.2× the measurement (`2 ^ 16` would be 3.6×);
it is chosen equal to `spqrSendStack`. -/
abbrev spqrRecvStack : Nat := 2 ^ 17
/-- Stack for `spqr::send::<HookRng>` (`SpqrSendOk`). -/
abbrev spqrSendStack : Nat := 2 ^ 17
/-- Stack of `try_decrypt_with_state` and `OTR::encrypt` (frames ≤ 1504 bytes plus the deepest hook). -/
abbrev rootStack : Nat := 2 ^ 18
/-- Stack of `OTR::from_session_state` / `apply_to_session_state` / `SignalMessage::try_from`. -/
abbrev smallRootStack : Nat := 2 ^ 16

/-! ## Contracts of the abstract hooks -/

/-- A call of an AES-256-CBC hook: the input bytes (`x0`, `x1`), the 32 key bytes (`x2`, `x3 = 32`),
the 16 IV bytes (`x4`, `x5 = 16`), the sret `x8` (24 bytes). -/
structure AesCall where
  inA : BitVec 64
  input : List (BitVec 8)
  keyA : BitVec 64
  key : List (BitVec 8)
  ivA : BitVec 64
  iv : List (BitVec 8)
  ret : BitVec 64

/-- The common precondition of the two AES hooks (input `< 2^40` bytes). -/
def AesCall.pre (A : RustAlloc) (x : AesCall) (s : State) : SepProp :=
  ⌜s.readReg64 .x0 = x.inA ∧ (s.readReg64 .x1).toNat = x.input.length ∧ s.readReg64 .x2 = x.keyA ∧
    s.readReg64 .x3 = 32#64 ∧ s.readReg64 .x4 = x.ivA ∧ s.readReg64 .x5 = 16#64 ∧
    s.readReg64 .x8 = x.ret ∧ x.key.length = 32 ∧ x.iv.length = 16 ∧ x.input.length < 2 ^ 40⌝ ∗
    (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗ A.pool ∗
    stackAt s.sp extHookStack

/-- The input, key and IV buffers of an AES call, given back unchanged in the postcondition. -/
def AesCall.frame (x : AesCall) : SepProp := (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv)

/-- **Named hypothesis: `aes_256_cbc_encrypt(ptext, key, iv)`** (`crypto/aes_cbc.rs:26–35`)
= the session model's `aesCbcEncrypt E`: `Ok` = a fresh owned `Vec<u8>` at the sret; the
`BadKeyOrIv` error cannot occur (fixed lengths). Trusted as a whole function, with no
machine-checked link to the compiled `signal_crypto::aes_cbc` code (DEV-E8). -/
def aesEncSpec (E : CBC.AesKey → CBC.Block → CBC.Block) (A : RustAlloc) : Spec AesCall where
  pre := fun x s => x.pre A s
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ x.frame ∗
      vecU8 A x.ret (aesCbcEncrypt E (bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- **Named hypothesis: `aes_256_cbc_decrypt(ctext, key, iv)`** (`crypto/aes_cbc.rs:37–53`)
= the session model's `aesCbcDecrypt D` (`CBC.cbcDecRaw`, `CryptoGames/AEAD/CBCDecDefs.lean`; trusted as
a whole function, DEV-E8): `some pt` = `Ok`, a fresh
`Vec<u8>`; `none` = `Err(BadCiphertext(&'static str))`: word 0 `-1`, a non-null `&str` at +8
(`BadKeyOrIv` cannot occur). -/
def aesDecSpec (D : CBC.AesKey → CBC.Block → CBC.Block) (A : RustAlloc) : Spec AesCall where
  pre := fun x s => x.pre A s
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ x.frame ∗
      (match aesCbcDecrypt D (bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input with
       | some pt => vecU8 A x.ret pt
       | none => (x.ret ↦₆₄ errTag) ∗
           (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((x.ret + 8#64) ↦₆₄ p)) ∗ memRegion (x.ret + 16#64) 8) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- The abstract SPQR (`spqr` 1.6.0) on serialized bytes: `send` / `recv` as in the session model's
`Spqr` interface (states and messages are byte strings, `PQC` = the tape), and `draws st tape` = the
number of tape bytes `spqr::send` consumes (a function of its inputs: the code is deterministic
given the tape).

**`spqr` panic predicates.** `recvPanics st msg` / `sendPanics st tape` = the inputs on
which `spqr::recv` / `spqr::send` panic (`Bool`, so that the session model's `Spqr` interface can
branch on them: `SpqrModel.spqr` passes them to `Spqr.recvPanics` / `Spqr.sendPanics`, and the
triple-ratchet model aborts with `.panic` exactly there). Upstream sites (`spqr` git checkout
`06959b4`):
* `recv`: `KeyHistory::get` `assert_eq!(data.len() % 36, 0)` and the `at + max_ooo` overflow
  (`chain.rs:191–192`), `KeyHistory::gc` `assert!(current_key >= max_ooo)` (`chain.rs:149`), the
  version-negotiation `assert!` / `expect`s (`lib.rs:425, 429, 433`), `msg.epoch - 1`
  (`lib.rs:462`, if `Message::deserialize` lets epoch 0 through), and the panics of its V1 helpers;
* `send`: `assert!(key.is_none())` (`lib.rs:292`), `msg.epoch - 1` (`lib.rs:299`), and the panics
  of its V1 helpers (all stubs, `SpqrSendOk`). On an empty state `send` cannot panic
  (`SpqrModel.SendEmptyOk`). -/
structure SpqrModel where
  send : List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8) × Salt × List (BitVec 8))
  draws : List (BitVec 8) → List (BitVec 8) → Nat
  recv : List (BitVec 8) → List (BitVec 8) → Except Bool (List (BitVec 8) × Salt)
  recvPanics : List (BitVec 8) → List (BitVec 8) → Bool
  sendPanics : List (BitVec 8) → List (BitVec 8) → Bool

/-- The session model's `Spqr` instance for `S` (`init` is not used by the triple-ratchet entry points). -/
def SpqrModel.spqr (S : SpqrModel) : Spqr (List (BitVec 8)) (List (BitVec 8)) :=
  ⟨fun _ _ => [], S.send, S.recv, S.sendPanics, S.recvPanics⟩

/-- `spqr::MessageKey = Option<Vec<u8>>` at `a` (24 bytes): `None` = `noneCap` (`generate_keys`
`cmn x20, #1`); `Some k` = an owned `Vec` of the 32 key bytes. -/
def spqrSendKeyAt (A : RustAlloc) (a : BitVec 64) : Salt → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16
  | some k => vecU8 A a k.toList

/-- `spqr::MessageKey = Option<Vec<u8>>` at `a` (24 bytes) as returned by `spqr::recv` (DEV-SPQR2):
`None` (`Salt.none`) is laid out either as the `None` niche (`noneCap` at `a`) or as an empty
`Vec<u8>` (`Some(vec![])`, which `spqr::recv` produces on the version-negotiation
`Ordering::Greater` path with `msg.index == 0`, `src/lib.rs:406`, and which HKDF-Extract treats
identically to `None`); `Some k` is an owned `Vec` of the 32 key bytes. -/
def spqrRecvKeyAt (A : RustAlloc) (a : BitVec 64) : Salt → SepProp
  | none =>
    ∃∗ isNiche : Bool,
      if isNiche then (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16
      else vecU8 A a []
  | some k => vecU8 A a k.toList

/-- A borrowed `Vec<u8>` argument: header address, `(cap, ptr)` and bytes. -/
structure VecArg where
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bytes : List (BitVec 8)

/-- The `Vec<u8>` of a `VecArg`. -/
def VecArg.at (A : RustAlloc) (a : VecArg) : SepProp := vecU8At A a.v a.cap a.ptr a.bytes

/-- `Result<spqr::Recv, spqr::Error>` at `r` (48 bytes): `Ok` = the new state
`Vec` @0 and the message key @24 (`spqrRecvKeyAt`, DEV-SPQR2); `Err` = word 0 `-1`, the error
discriminant byte @8, `0` exactly for `StateDecode` (try_decrypt `0x34bc8: ldrb w9, [sp, #0x400];
cbz w9`). -/
def spqrRecvResultAt (A : RustAlloc) (r : BitVec 64) :
    Except Bool (List (BitVec 8) × Salt) → SepProp
  | .ok (st', key) => vecU8 A r st' ∗ spqrRecvKeyAt A (r + 24#64) key
  | .error sd =>
    (r ↦₆₄ errTag) ∗ (∃∗ d : BitVec 8, ⌜(d = 0#8 ↔ sd = true)⌝ ∗ ((r + 8#64) ↦₈ d)) ∗
      memRegion (r + 9#64) 39

/-- `spqr::recv(state = x0, msg = x1)` (both `&Vec<u8>`; sret `x8`, 48 bytes) = `S.recv state msg`
(`spqr/src/lib.rs:355`), in the image (`0x5462c`): the subject of the named hypothesis `SpqrRecvOk`
(general state). Allocates its outputs; `spqr::Error`
owns no heap memory. Logging off (`logOff`: `recv` logs through `log_impl`). Panics only on
`S.recvPanics state msg` or a failed allocation; a normal return happens only when
`¬ S.recvPanics state msg` (the model and the code agree on which calls panic). -/
def spqrRecvSpec (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) :
    Spec (VecArg × VecArg × BitVec 64) :=
  Spec.inImage
    { pre := fun (st, msg, ret) s =>
        ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
          st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ logOff img ∗ A.pool ∗ stackAt s.sp spqrRecvStack
      post := fun (st, msg, ret) s0 sf =>
        ⌜sf.trace = s0.trace ∧ ¬ S.recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
          spqrRecvResultAt A ret (S.recv st.bytes msg.bytes) ∗
          logOff img ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
      onPanic := fun (st, msg, _) s0 sf =>
        ⌜(allocFailedIn s0 sf ∨ S.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- `alloc::fmt::format::format_inner(x0 = pieces, x1 = args)` (sret `x8`, a `String`):
produces some fresh owned `String`. It reads its arguments (any frame), writes only the sret. Only
error texts depend on it (`invalidState`, `invalidMessage pqRatchet / badCiphertext`). -/
def formatInnerSpec (A : RustAlloc) : Spec (BitVec 64) where
  pre := fun ret s => ⌜s.readReg64 .x8 = ret⌝ ∗ memRegion ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack
  post := fun ret s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (∃∗ bs : List (BitVec 8), vecU8 A ret bs) ∗ A.pool ∗
      stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `core::fmt::write(output: &mut dyn Write, args: Arguments)` into a `String` (`x0` = the
`String`, `x1` = the writer's vtable; `x2`, `x3` = the two words of Rust 1.98.1's `Arguments`:
template pointer and argument array): returns `w0 = 0` (`Ok`) and the `String` holds some owned
bytes. The only call in the triple-ratchet closure is from the in-image
`<ProtocolAddress as Display>::fmt` (`+0x38`; other image sites call this stub too, but none is
reached by a triple-ratchet proof; `ldp x0, x1, [x1]` loads the `Formatter`'s writer; template
`"{}.{}"`, arguments the address's name and device id), which `try_decrypt_with_state` calls
(`0x347dc`) with a `Formatter` whose writer is a stack `String` and the `<String as fmt::Write>`
vtable. Because only error texts and logging depend on the formatted bytes, this contract does not
constrain the vtable or the arguments (just like `formatInnerSpec`). Ghost `(v, bs)`: the
`String` and its bytes. -/
def fmtWriteSpec (A : RustAlloc) : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (v, bs) s =>
    ⌜s.readReg64 .x0 = v⌝ ∗ vecU8 A v bs ∗ A.pool ∗ stackAt s.sp extHookStack
  post := fun (v, _) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ bs' : List (BitVec 8), vecU8 A v bs') ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `__rust_alloc_zeroed(size = x0, align = x1)` (`library/alloc/src/alloc.rs`), from the same
allocator `A` as `AllocHooks A`:
as `rustAllocSpec A`, but the fresh block holds `size` zero bytes. Failure: `x0 = 0`, one
`allocFailedEvent` appended. Ghost: `(size, align)`. -/
def rustAllocZeroedSpec (A : RustAlloc) : Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧ LayoutOk size align⌝ ∗
      A.pool ∗ stackAt s.sp allocHookStack
  post := fun (size, align) s0 sf =>
    A.pool ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
         A.live (sf.readReg64 .x0) size align ∗ (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8))

/-- **The contracts the abstract hooks meet** (every field a `HookSat` on `abs`; `tripleRatchetExterns`
passes these names to `abs` unchanged, `tripleRatchetExterns_abs`). `aesEnc` / `aesDec` are named
hypotheses. The `S` parameter is unused (`spqr::recv`, `spqr::decode_state` and prost's
`DecodeError::from` / `push` are in-image code, since the image holds the `uuid`, `prost` and
`spqr` crates, so they need no hook contract); it keeps the statements uniform. -/
structure TripleRatchetHooks (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop where
  alloc : AllocHooks A abs
  allocZeroed : HookSat abs allocZeroedName (rustAllocZeroedSpec A)
  aesEnc : HookSat abs aesEncName (aesEncSpec C.E A)
  aesDec : HookSat abs aesDecName (aesDecSpec C.D A)
  formatInner : HookSat abs formatInnerName (formatInnerSpec A)
  fmtWrite : HookSat abs fmtWriteName (fmtWriteSpec A)

/-! ## The `spqr::send` hypothesis -/

/-- A call of `spqr::send::<HookRng>(sret = x0, state = x1: &Vec<u8>)`: the sret (72 bytes), the
state, the tape position. -/
structure SendCall where
  ret : BitVec 64
  st : VecArg
  cur : BitVec 64
  rest : List (BitVec 8)

/-- `Result<spqr::Send, spqr::Error>` at `r` (72 bytes): `Ok` = the new state
`Vec` @0, the `pq_ratchet` message `Vec` @24 (shorter than `2^32`), the message key @48; `Err` =
word 0 `-1` (`OTR::encrypt` `0x33e58: cmn x8, #1`), the rest unspecified. -/
def spqrSendResultAt (A : RustAlloc) (r : BitVec 64) :
    Option (List (BitVec 8) × Salt × List (BitVec 8)) → SepProp
  | some (st', key, msg) =>
    ⌜msg.length < 2 ^ 32⌝ ∗ vecU8 A r st' ∗ vecU8 A (r + 24#64) msg ∗ spqrSendKeyAt A (r + 48#64) key
  | none => (r ↦₆₄ errTag) ∗ memRegion (r + 8#64) 64

/-- The contract of `spqr::send::<HookRng>`: `send state tape`, the tape advanced by
`draws state tape ≤ tape.length`. Panics only on `S.sendPanics state tape` or a failed
allocation; a normal return happens only when `¬ S.sendPanics state tape`. -/
def spqrSendSpec (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    Spec SendCall :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.st.v⌝ ∗ x.st.at A ∗ memRegion x.ret 72 ∗
          tapeAt ctl x.cur x.rest ∗ logOff img ∗ A.pool ∗ stackAt s.sp spqrSendStack
      post := fun x s0 sf =>
        ⌜S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
            ¬ S.sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A ∗
          spqrSendResultAt A x.ret (S.send x.st.bytes x.rest) ∗
          tapeAfter ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗ logOff img ∗ A.pool ∗
          stackAt s0.sp spqrSendStack
      onPanic := fun x s0 sf =>
        ⌜(allocFailedIn s0 sf ∨ S.sendPanics x.st.bytes x.rest) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- **Named hypothesis `SpqrSendOk`**: the in-image `spqr::send::<HookRng>` (3436 instructions;
its closure is 133 in-image functions, all of `spqr`, `prost` and `bytes`) meets `spqrSendSpec`,
not verified on non-empty states. It is stated **for the given `abs`**: `TripleRatchetHooks` contracts the
allocator hooks its closure calls (`AllocHooks`, `allocZeroed`; `libsignal_session_rng_fill`,
`memcpy` / `memmove` / `memset`, SHA-256 compression and the panic entry points are concrete). On a
non-empty state its closure also reaches these extern stubs, which go to `abs` with no contract
here:
* libcrux ML-KEM-768 `incremental::KeyPairCompressedBytes::from_seed` / `pk1` / `pk2` and
  `incremental::encapsulate1`; `libcrux_hmac::hmac`;
* `std::sync::Once::call` (the `cpufeatures` init);
* the no-hook stubs `__aarch64_ldadd8_rel` and `log::Log::log` (behind `MAX_LOG_LEVEL_FILTER`,
  `logOff`).
So discharging it needs facts about `abs` on these names beyond `TripleRatchetHooks`. The empty-state
instance needs none. -/
def SpqrSendOk (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrSendName) (spqrSendSpec A ctl S img)

/-- What upstream `spqr::send` does on an empty state (`spqr/src/lib.rs:264–271, 495–501`): `Ok`
with an empty state and message and no key, drawing no tape bytes and not panicking, whatever the
tape. A property of the model `S`, not of the code. -/
structure SpqrModel.SendEmptyOk (S : SpqrModel) : Prop where
  send : ∀ rest, S.send [] rest = some ([], none, [])
  draws : ∀ rest, S.draws [] rest = 0
  noPanic : ∀ rest, ¬ S.sendPanics [] rest

/-! ## The `spqr::recv` hypothesis -/

/-- **Named hypothesis `SpqrRecvOk`** (mirrors `SpqrSendOk`): the in-image `spqr::recv` (759
instructions; its closure is 140 in-image functions) meets `spqrRecvSpec`, not verified on
non-empty states. Stated **for the given `abs`**: `TripleRatchetHooks` contracts the allocator hooks
(`AllocHooks`, `allocZeroed`) and `alloc::fmt::format_inner`; `memcpy` / `memmove` / `memset`,
SHA-256 compression and the panic entry points (including `assert_failed::<u64, u64>` /
`<usize, usize>`) are concrete. On a non-empty state (or a message that starts a V1 exchange) its
closure also reaches these extern stubs, which go to `abs` with no contract here:
* libcrux ML-KEM-768 `incremental::validate_pk_bytes` / `encapsulate2` /
  `decapsulate_compressed_key`; `libcrux_hmac::hmac`;
* `std::sync::Once::call` (the `cpufeatures` init);
* the no-hook stubs `__aarch64_ldadd8_rel` and `log::Log::log` (behind `MAX_LOG_LEVEL_FILTER`,
  `logOff`).
So, as for `SpqrSendOk`, discharging it needs facts about `abs` on these names beyond
`TripleRatchetHooks`; and `subroutine_ok` also requires termination, which no hypothesis on `abs` alone
gives for an unconstrained stub. The empty-state instance needs none. -/
def SpqrRecvOk (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrRecvName) (spqrRecvSpec A S img)

/-- What upstream `spqr::recv` does on an empty state (`spqr/src/lib.rs:355–380, 495–505`): it
parses the message's preamble (`msg_preamble`, `Err(MsgDecode)` on failure), decodes the state
(`None` everywhere) and returns `Ok` with an empty state and no key; it never panics
(`LibsignalSpqr.spqrRecvEmpty`, module docstring of `Specifications/LibsignalSpqr.lean`). A property
of the model `S`, not of the code. -/
structure SpqrModel.RecvEmptyOk (S : SpqrModel) : Prop where
  recv : ∀ msg, S.recv [] msg = LibsignalSpqr.spqrRecvEmpty msg
  noPanic : ∀ msg, ¬ S.recvPanics [] msg

/-! ## `try_decrypt_with_state` -/

/-- Ghost of a `try_decrypt_with_state` call: the argument addresses, their layouts and their
session-model values. -/
structure TryDecryptGhost where
  /-- The sret (`x0`, 48 bytes). -/
  ret : BitVec 64
  /-- `state: &mut SessionState` (`x1`), its ghost layout and session-model value. -/
  ss : BitVec 64
  G : SessionGhost
  st : SessionState (List (BitVec 8))
  /-- `remote_address` (`x2`, the sender) and `local_address` (`x3`, the recipient). -/
  remA : BitVec 64
  rem : AddrGhost
  locA : BitVec 64
  loc : AddrGhost
  /-- `ciphertext: &SignalMessage` (`x4`). -/
  msgA : BitVec 64
  msgG : SignalMessageGhost
  msg : SignalMessage
  /-- `original_message_type` (`w5`). -/
  msgType : MessageType
  /-- The tape position. -/
  cur : BitVec 64
  rest : List (BitVec 8)

/-- The session-model result and final state: `try_decrypt_with_state` with `expected =
serialize_addresses(remote, local)` and the coins = the first 32 tape bytes. -/
def TryDecryptGhost.model (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : TryDecryptGhost) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState (List (BitVec 8)) :=
  Mut.exec (SessionState.tryDecryptWithState C S.spqr (serializeAddresses (serviceIdParse uuidParse) x.rem x.loc) x.msg
    x.msgType (coinsOf x.rest)) x.st

/-- **Stored skipped-key seeds are 32 bytes (`DEV-LS9`, a trusted precondition of `tryDecryptSpec`).**
libsignal creates every seed as `HMAC-SHA256(chain key, 0x01)`, 32 bytes (`ChainKey::message_keys`
/ `calculate_base_material`, `ratchet/keys.rs:172–181`), and stores only those
(`store_skipped_key`). Reading a record, `MessageKey::from_pb` (`:63–88`) accepts **any non-empty**
seed (the `Seed` form, `:86`), and `LibsignalSessionRepr.messageKeyAt` likewise requires only
`seed ≠ []`. The proved `generate_keys` / HKDF-extract contracts (`LibsignalSession.generateKeysSpec` /
`hkdfExtractSpec`) take a 32-byte input key material, so a record holding a stored seed of another
length (never produced by libsignal: a corrupted or foreign record) is outside this spec. The
session model preserves the predicate (proof lemmas, not part of the trust base). -/
def SeedsLen32 {PQ : Type} (st : SessionState PQ) : Prop :=
  ∀ c ∈ st.receiverChains, ∀ k ∈ c.messageKeys, k.seed.length = 32

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
def tryDecryptSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
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
        memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗
        A.pool
      post := fun x s0 sf =>
        ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidParse).1.toBool G'⌝ ∗
          sessionStateAt A x.ss G' (x.model C S uuidParse).2) ∗
        vecResultAt A x.ret (x.model C S uuidParse).1 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
        logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.recvPanics x.st.pqRatchetState x.msg.pqRatchet ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-! ## `OutgoingTripleRatchet::from_session_state` -/

/-! ## `OutgoingTripleRatchet::encrypt::<HookRng>` -/

/-- An optional borrowed `ProtocolAddress` (`Option<&ProtocolAddress>`, null = `None`). -/
def optAddrAt (A : RustAlloc) (a : BitVec 64) : Option AddrGhost → SepProp
  | none => emp
  | some g => protocolAddressAt A g a

/-- Ghost of an `OTR::encrypt` call. -/
structure OtrEncryptGhost where
  /-- The sret (`x0`, 120 bytes). -/
  ret : BitVec 64
  /-- `self: &mut OutgoingTripleRatchet` (`x1`), its pq `Vec` and session-model value. -/
  o : BitVec 64
  pqCap : BitVec 64
  pqPtr : BitVec 64
  ot : OutgoingTripleRatchet (List (BitVec 8))
  /-- `plaintext: &[u8]` (`x2`, `x3`). -/
  ptA : BitVec 64
  ptext : List (BitVec 8)
  /-- `local_address: Option<&ProtocolAddress>` (`x4`, 0 = `None`), `remote_address` (`x5`). -/
  locA : BitVec 64
  loc : Option AddrGhost
  remA : BitVec 64
  rem : AddrGhost
  /-- The tape position. -/
  cur : BitVec 64
  rest : List (BitVec 8)

/-- `serialize_addresses(local, remote)` if a local address is passed (`triple_ratchet.rs:86–135`). -/
def OtrEncryptGhost.addresses (uuidParse : UuidParser) (x : OtrEncryptGhost) :
    Option (List (BitVec 8)) :=
  x.loc.bind fun l => serializeAddresses (serviceIdParse uuidParse) l x.rem

/-- The session-model result and final OTR (the coins of `spqr::send` = the whole remaining tape). -/
def OtrEncryptGhost.model (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : OtrEncryptGhost) :
    Except SignalProtocolError SignalMessage × OutgoingTripleRatchet (List (BitVec 8)) :=
  Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext (x.addresses uuidParse)
    x.rest) x.ot

/-- **The binding spec of `OTR::encrypt::<HookRng>`** (`triple_ratchet.rs:86–135`): sret `x0`,
`x1` = OTR, `x2` / `x3` = plaintext (`< 2^32` bytes), `x4` = local address or 0, `x5` = remote
address; `x6` (`&mut HookRng`) not read. Normal return only if the model does not panic: the OTR
holds the model's final value (new pq `Vec` on success), the sret the model's result (using the
concrete codec `protoSignalCodec`), the tape advanced by `S.draws` (only `spqr::send` draws). Panic
only if the model panics, `spqr::send` panics on the model's inputs (`S.sendPanics` of the OTR's pq
state and the tape), or the allocator failed. -/
def otrEncryptSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec OtrEncryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.o ∧ s.readReg64 .x2 = x.ptA ∧
          (s.readReg64 .x3).toNat = x.ptext.length ∧ x.ptext.length < 2 ^ 32 ∧
          s.readReg64 .x4 = (if x.loc.isSome then x.locA else 0#64) ∧
          (x.loc.isSome → x.locA ≠ 0#64) ∧ s.readReg64 .x5 = x.remA⌝ ∗
        otrAt A x.o x.pqCap x.pqPtr x.ot ∗ (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗
        protocolAddressAt A x.rem x.remA ∗ memRegion x.ret 120 ∗ tapeAt ctl x.cur x.rest ∗
        logOff img ∗ stackAt s.sp rootStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A x.o pqCap' pqPtr' (x.model C S uuidParse).2) ∗
        signalMessageResultAt A (utf8 "encrypt") x.ret (x.model C S uuidParse).1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗
        tapeAfter ctl x.cur x.rest (S.draws x.ot.pqrState x.rest) ∗
        logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-! ## `OutgoingTripleRatchet::apply_to_session_state` -/

/-! ## `<SignalMessage as TryFrom<&[u8]>>::try_from` -/

/-! ## The statements the proofs establish

The specs above are generic in the UUID parser; the program is not (the image holds uuid 1.26.1's
`Uuid::try_parse`), so every statement instantiates them at its model `uuidTryParse`. -/

/-! ## `try_decrypt_from_record`, a region of `message_decrypt_signal`

`try_decrypt_from_record::<HookRng>` (`session_management.rs:368–556`) is `pub(crate)` and fully
inlined into `session_message_decrypt_signal` (= `message_decrypt_signal::<HookRng>`), so its
contract is a **region contract**: from a pc inside the function to a later pc of the same
function, with the function's frame (`sp`, `x29`) fixed. Scope: a `Whisper` message, a record with
a current session and **no** previous sessions, logging off. -/

/-- **Framed region triple (total correctness).** From every state at `entry` satisfying `pre` (with
any frame `R`), `prog` runs to a `.Running` state at `exit` satisfying `post`, or panics with
`onPanic`; it never exits the process. Unlike `subroutine_ok`, nothing returns: `entry` and `exit`
are pcs inside one function, and the calling-convention facts the continuation needs are stated in
`post`. -/
def region_ok {α : Type} (prog : Program) (entry exit : BitVec 64) (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 : State),
    s0.pc = entry → s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) →
    prog.CodeLoaded s0.mem →
    ∃ sf, Steps prog s0 sf ∧
      ((sf.pc = exit ∧ sf.status = .Running ∧ (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∨
       (sf.status = .Panicked ∧ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R)))

/-- `session_message_decrypt_signal` (`0x3a58c`, 2451 instructions): the session crate's
`message_decrypt_signal::<HookRng>` with `try_decrypt_from_record` inlined. -/
abbrev msgDecryptName : String := "session_message_decrypt_signal"

/-- Region entry `+0x1a8` (`0x3a734`): just after `load_session` returned `Some(record)` and the
record was assembled at `sp + 0x120` (`+0x198..+0x1a4`, `memcpy` 312 B to `sp + 0x158`); the next
instructions start `record.session_state()` (`+0x1c4: ldr x9, [sp, #0x138]; cmn x9, #1`). -/
abbrev recordRegionEntry (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x1a8#64

/-- Region exit `+0x1f50` (`0x3c4dc`): after the `errs: Vec<SignalProtocolError>` was dropped
(`+0x1e8c..+0x1f4c`), where the code branches on the result tag `x28` (`+0x1f60: cmn x28, #2`). -/
abbrev recordRegionExit (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x1f50#64

/-- Ghost of the region. -/
structure RecordDecryptGhost where
  /-- The caller's sret (`x27`, also spilled at `sp + 0x80`), opaque to the region. -/
  sret : BitVec 64
  /-- `record.previous_sessions` buffer pointer (`sp + 0x128`; its length at `sp + 0x130` is 0). -/
  prevPtr : BitVec 64
  /-- The current session (`record.current_session` at `sp + 0x138`): ghost layout and session-model value. -/
  G : SessionGhost
  st : SessionState (List (BitVec 8))
  /-- `remote_address` (sender; `x19`, spilled at `sp + 0xe8`) and `local_address` (recipient;
  `sp + 0xf0`). -/
  remA : BitVec 64
  rem : AddrGhost
  locA : BitVec 64
  loc : AddrGhost
  /-- `ciphertext: &SignalMessage` (`sp + 0xe0`). -/
  msgA : BitVec 64
  msgG : SignalMessageGhost
  msg : SignalMessage
  /-- The tape position. -/
  cur : BitVec 64
  rest : List (BitVec 8)

/-- The session-model result and final record: `try_decrypt_from_record` with `msg_type = Whisper`,
`expected = serialize_addresses(remote, local)`, coins = the first 32 tape bytes. -/
def RecordDecryptGhost.model (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : RecordDecryptGhost) :
    Except SignalProtocolError (List (BitVec 8)) × SessionState (List (BitVec 8)) :=
  SessionState.tryDecryptFromRecord C S.spqr (serializeAddresses (serviceIdParse uuidParse) x.rem x.loc) x.msg .whisper
    (coinsOf x.rest) x.st

/-- Tape bytes drawn: `try_decrypt_with_state`'s (`decryptDraws`) iff the version check passes
(`+0x63c..+0x698`: `(session_version = 0 ? 2 : session_version) = message_version`), else 0. -/
def RecordDecryptGhost.draws (C : Crypto) (x : RecordDecryptGhost) : Nat :=
  if x.st.version.toNat = x.msg.messageVersion.toNat then
    decryptDraws C x.st x.msg.senderRatchetKey x.rest
  else 0

/-- `"decryption failed"` (`session_management.rs:451, 549`), 17 bytes: built at `+0x1de8..+0x1e14`
from 16 `.rodata` bytes and `strb #0x64` (`'d'`) at +16. -/
def decryptionFailedStr : List (BitVec 8) := utf8 "decryption failed"

/-- The region's result slot (48 bytes): `vecResultAt`, except that the `"decryption failed"`
`InvalidMessage` (which the five entry points above never produce, so `invalidMessageStrAt` leaves
it `False`) is the `String` with exactly those bytes and the type byte (`+0x1e08..+0x1e24`). -/
def recordResultAt (A : RustAlloc) (r : BitVec 64) :
    Except SignalProtocolError (List (BitVec 8)) → SepProp
  | .error (.invalidMessage t .decryptionFailed) =>
    (r ↦₆₄ speWord 24) ∗ vecU8 A (r + 8#64) decryptionFailedStr ∗ ((r + 32#64) ↦₈ msgTypeByte t) ∗
      memRegion (r + 33#64) 15
  | res => vecResultAt A r res

/-- Word 0 of `recordResultAt` / `vecResultAt` / `speAt` for each result: `okTagVec` for `Ok`, the
variant's `speWord` for `Err` (the table of `speAt`). The region leaves it in `x28`; the
continuation stores `x28` as word 0 of the caller's result (`+0x24e0: str x28, [x27]`) and copies
bytes 8..48 from the slot, so `x28` must be exactly this word. -/
def recordResultTag : Except SignalProtocolError (List (BitVec 8)) → BitVec 64
  | .ok _ => okTagVec
  | .error .invalidState => speWord 1
  | .error (.ciphertextMessageTooShort _) => speWord 3
  | .error (.legacyCiphertextVersion _) => speWord 4
  | .error (.unrecognizedCiphertextVersion _) => speWord 5
  | .error .invalidProtobufEncoding => speWord 2
  | .error .noKeyTypeIdentifier => speWord 7
  | .error (.badKeyType _) => speWord 8
  | .error (.badKeyLength _) => speWord 9
  | .error .invalidKeyAgreement => speWord 10
  | .error (.invalidSessionStructure _) => speWord 20
  | .error (.duplicatedMessage _ _) => speWord 23
  | .error (.invalidMessage _ _) => speWord 24
  | .error .panic => 0#64

/-- The ghost of the stored session after a successful region: the record now holds the decrypted
**clone** (every `Vec` freshly allocated), so only the bytes the model does not determine are
related: both identity keys' bytes, `alice_base_key`'s bytes, the registration ids; the pending
pre-keys are cleared (`clear_unacknowledged_pre_key_message`). -/
def _root_.CryptoVerification.LibsignalTripleRatchetRepr.SessionGhost.AfterRecordDecrypt
    (G G' : SessionGhost) : Prop :=
  G'.localIk.bytes = G.localIk.bytes ∧ G'.remoteIk.bytes = G.remoteIk.bytes ∧
    G'.alice.bytes = G.alice.bytes ∧ G'.regIds = G.regIds ∧ G'.pending = none ∧ G'.kyber = none

/-- **The binding region contract of `try_decrypt_from_record`** (`recordRegionEntry` →
`recordRegionExit`; Whisper, current session only, logging off).

Entry state (established by `message_decrypt_signal`'s prefix, `+0x0..+0x1a8`): the frame of
`sub sp, #0xe80` under `x29`; the record at `sp + 0x120` with `previous_sessions.len = 0` and
`current_session = Some(st)` (`sessionStateAt` at `sp + 0x138`, whose word 0 is never the `None`
niche `-1`); the argument spills `sp + 0xe0` (message) and `sp + 0xf0` (local address), `x19` =
remote address; `x23 = sp + 0x5f0`, `x24 = sp + 0xca0` (scratch pointers live into the region);
the region's scratch `sp .. sp + 0xa0` and `sp + 0x4b0 .. sp + 0xe00`; the stack below `sp`.
Preconditions as `tryDecryptSpec` for `st` (`DEV-LS28` remote IK ≠ local IK, `DEV-LS9` `SeedsLen32`,
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
def recordDecryptSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
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
        tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool
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
        tapeAfter ctl x.cur x.rest (x.draws C) ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model C S uuidParse).1 = .error .panic ∨
            (x.st.version.toNat = x.msg.messageVersion.toNat ∧
              S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-! ## Guards (kernel-checked)

The four image guards (`tripleRatchetEntries_unique`, `recordRegion_unique`, `tripleRatchetStubs_present`,
`inImageCallees_code`) live in the leaf module `LibsignalBinary/Specifications/LibsignalTripleRatchetGuards.lean`, which
no proof imports and `LibsignalBinary.lean` builds; `tripleRatchetExterns_abs` stays here because the
proofs use it. -/

set_option maxRecDepth 200000 in
open ProofLib.ProgramReflection in
/-- Guard: `tripleRatchetExterns` (under `Rust.withPanics`) hands each abstract hook name to `abs`. -/
theorem tripleRatchetExterns_abs (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    [aesEncName, aesDecName, formatInnerName, fmtWriteName, "__rustc::__rust_alloc",
      "__rustc::__rust_dealloc", "__rustc::__rust_realloc", allocZeroedName].map
        (Rust.withPanics (tripleRatchetExterns C ctl abs)) =
    [abs aesEncName, abs aesDecName, abs formatInnerName, abs fmtWriteName,
      abs "__rustc::__rust_alloc", abs "__rustc::__rust_dealloc", abs "__rustc::__rust_realloc",
      abs allocZeroedName] := by
  rfl_kernel

end CryptoVerification.LibsignalTripleRatchet
