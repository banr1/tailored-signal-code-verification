/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr

/-!
# Fixed Two-Party Configuration and SPQR-Off Session Outcomes

**Trusted in part.** `Computational/Theorems/` uses `serializedPartyAddresses`, `partyDeviceId`,
`partyIdentityKeyBytes`, `partyIdentityKey`, and `partyAddressName`; `spqrOffSessionParams`,
`initKeysE`, `Reach`, `sendModelSpqrOff`, and `recvModelSpqrOff` are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md` and `Computational/docs/DEVIATIONS.md` (DEV-M3, DEV-M4,
DEV-M5, DEV-M10, DEV-E8).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

/-! ## The parties (constants of the image) -/

/-- The protocol address name of each party: a fixed hyphenated UUID.

**DEV-M3 (libsignal): the parties' addresses are constants.** ACD19 Def. 6 has two parties A
and B and no addresses. libsignal MACs both parties' addresses, and the wrapper fixes them: these
two UUID names and device 1 (`partyDeviceId`). Why: the image is one fixed configuration. Effect:
w.l.o.g., argued: the session model's bound holds for every address blob. -/
def partyAddressName : Party → String
  | .A => "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b"
  | .B => "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6"

/-- The 32 X25519 public-key bytes of each party's fixed identity key (its 33-byte serialization
is the type byte `0x05` followed by these bytes).

**DEV-M10 (libsignal): the identity private keys are public test keys.** ACD19 has no identity
keys. The wrapper's `ALICE` / `BOB` statics hold fixed identity key pairs, derived from public seed
strings and stored in the image's data, private halves included. Why: a test configuration with no
handshake. Effect: none on this bound: only the handshake (out of scope, DEV-M5) uses the
private halves, and the session model's bound holds for any two distinct identity keys. -/
def partyIdentityKeyBytes : Party → List.Vector (BitVec 8) 32
  | .A => ⟨[0x48, 0x3e, 0xf1, 0x07, 0x2a, 0xa0, 0x66, 0x42, 0x4f, 0x02, 0x3f, 0x4b, 0x14, 0x50,
      0x7c, 0x5f, 0x66, 0xa4, 0xcd, 0xff, 0xe8, 0xfc, 0x3c, 0x97, 0x0a, 0x95, 0x8b, 0xd5, 0xdb,
      0xdf, 0x9d, 0x3e], rfl⟩
  | .B => ⟨[0xce, 0x04, 0x50, 0xdd, 0x2f, 0x12, 0x34, 0x24, 0x84, 0x52, 0xb2, 0x37, 0x17, 0x1b,
      0x66, 0x02, 0x11, 0x0f, 0x10, 0x7c, 0x14, 0x1f, 0xfc, 0x0d, 0x19, 0x41, 0x07, 0x08, 0x42,
      0xd7, 0xc9, 0x3c], rfl⟩

/-- **Each party's identity key**, with public-key bytes `partyIdentityKeyBytes P`.

**DEV-M4 (libsignal): the identity public keys are constants.** ACD19 has no identity keys.
libsignal puts both identity public keys into the MAC input (DEV-LS15); the wrapper fixes them.
Why: the image is one fixed configuration. Effect: w.l.o.g., argued: the session model's bound
holds for any two distinct identity keys, and `Guards.lean` checks that these two differ. -/
def partyIdentityKey (P : Party) : IdentityKey := ⟨⟨partyIdentityKeyBytes P⟩⟩

/-- Every party uses device 1. -/
def partyDeviceId : BitVec 8 := 1#8

/-- **`serialize_addresses(sender, recipient)`** of the two parties' addresses (names `partyAddressName`,
device 1) under the UUID parser `uuidParse`: `none` if a name does not parse (then libsignal MACs
without addresses, in the binary and in the session model alike). The scheme uses it at the
trusted model `uuidTryParse` of `Uuid::try_parse` (`spqrOffSessionParams`), under which both names
parse. -/
def serializedPartyAddresses (uuidParse : UuidParser) (sender recipient : Party) : Option (List (BitVec 8)) := do
  let s ← serviceIdParse uuidParse (utf8 (partyAddressName sender))
  let r ← serviceIdParse uuidParse (utf8 (partyAddressName recipient))
  return addrBytes s partyDeviceId ++ addrBytes r partyDeviceId

/-! ## Parameters -/

/-- **The session model's parameters at `C`**: prost's codec, SPQR off (its receive checks only
the message's preamble, DEV-LS24), the parties' identity keys, and the address blobs as the binary
computes them (UUIDs parsed by `uuidTryParse`).

**The free parameters** are the primitives `C` (the session model's `Crypto`: the semantics of the
AES block cipher, X25519 and the SHA-256 compression function). Both conjuncts hold for every
value.

**DEV-E8 (machine model): the primitives' machine code is not verified.** ACD19 assumes ideal
primitives. In the binary, AES-256-CBC (with CBC mode and padding), SHA-256 compression, X25519
and the RNG are hooks: CBC is the session model's `aesCbcEncrypt` over `C.E`, the others are the
free `C`, and the RNG is a tape the game fills. Why: primitives are verified or assumed
separately. Effect: out of scope: their compiled code is trusted to match. For AES-CBC that code
is the whole `signal_crypto::aes_cbc::aes_256_cbc_encrypt` / `aes_256_cbc_decrypt`: CBC chaining
and PKCS#7 padding / unpadding (with its padding check) are trusted, not only the block cipher.
The build pins the portable software AES backend (`--cfg aes_backend="soft"`,
`third_party/libsignal/libsignal-session/translation.toml`), so there is no run-time CPU dispatch: the
code that would run is the `aes` crate's software fixslice implementation, which is outside the
image. `Uuid::try_parse` is not a hook: its compiled code is in the image and verified against
the trusted model `uuidTryParse` (`LibsignalTripleRatchetRepr.lean`). -/
def spqrOffSessionParams (C : Crypto) : Params Bytes Unit :=
  ⟨C, protoSignalCodec, spqrOffB, partyIdentityKey .A, partyIdentityKey .B, serializedPartyAddresses uuidTryParse .A .B,
    serializedPartyAddresses uuidTryParse .B .A⟩

/-! ## Inputs -/

/-- **The session model's initial keys for the scheme key `k`**, exactly as `libsignalSessionScheme` makes
them: the root KDF (key derivation function) of `k`'s root key and `encPt lam` gives the root and
chain keys (ACD19 §5.1: `P-Up(P-Init(k_root), λ)`); the three coins follow.

**DEV-M5 (libsignal): the session starts from the handshake's output.** ACD19 §5.2 "Initial key
agreement" leaves the handshake out; libsignal runs PQXDH (the post-quantum X3DH handshake). Lean
computes the root KDF step and hands its output to `session_seed`, as the session model does.
Why: PQXDH is a separate project. Effect: out of scope. -/
def initKeysE (C : Crypto) {Pt : Type} (encPt : Pt → Bytes) (lam : Pt)
    (k : LibsignalSession.RootKey × BitVec 256 × BitVec 256 × BitVec 256) : InitKeys :=
  let rc := rootKdf C.F k.1 (encPt lam)
  ⟨rc.1, rc.2, k.2.1, k.2.2.1, k.2.2.2⟩

/-! ## Reachable session-model states -/

/-- **The session-model states reachable from an initial state** by sends of any plaintext and
receives of any ciphertext, with any coins. -/
inductive Reach (P : Params Bytes Unit) : GhostState Bytes → Prop
  | initA (k : InitKeys) : Reach P (P.initA k)
  | initB (k : InitKeys) : Reach P (P.initB k)
  | send {g : GhostState Bytes} (m : Bytes) (r : Unit) : Reach P g → Reach P (P.send g m r).1
  | recv {g g' : GhostState Bytes} {c : Bytes} {rc : BitVec 256} {x : ℕ × ℕ × Bytes} :
      Reach P g → P.receive g c rc = some (g', x) → Reach P g'

/-! ## Each entry's outcome in the session model -/

/-- **`send`'s outcome in the model**: the session model's `messageEncrypt` on `g`'s
session. On success the record of the new state and the `SignalMessage` bytes; on the model's panic
(`.error .panic`: the sending chain's index is `u32::MAX`, `ChainKey.nextChainKey`) an abort
(`none`); on any other error a null return (`some none`). -/
def sendModelSpqrOff (C : Crypto) (g : GhostState Bytes) (m : Bytes) : Option (Option (Bytes × Bytes)) :=
  match SessionState.messageEncrypt (spqrOffSessionParams C).C (spqrOffSessionParams C).codec (spqrOffSessionParams C).spqr
      ((spqrOffSessionParams C).sendAddrs g.party) m () g.session with
  | (.ok msg, s) => some (some (encodeRecord { g with session := s }, msg.serialized))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-- **`recv`'s outcome in the model**: the session model's receive, written with its parts
(`SignalMessage.tryFrom`, then `SessionState.tryDecryptFromRecord` with the party's expected
address blob and the coins `rc`, as in `Params.receive`, which collapses every error to `none`).
On success the record of the new state and the raw plaintext (not fitted to `ℓ`); on the model's panic
(`.error .panic`: a header counter `u32::MAX` within `maxForwardJumps` of the chain's index,
`ChainKey.nextChainKey`) an abort (`none`); on a parse failure or any other error a null return
(`some none`). -/
def recvModelSpqrOff (C : Crypto) (g : GhostState Bytes) (c : Bytes) (rc : BitVec 256) :
    Option (Option (Bytes × Bytes)) :=
  match SignalMessage.tryFrom (spqrOffSessionParams C).codec c with
  | .error _ => some none
  | .ok msg =>
    match SessionState.tryDecryptFromRecord (spqrOffSessionParams C).C (spqrOffSessionParams C).spqr
        ((spqrOffSessionParams C).expectedAddrs g.party) msg .whisper rc g.session with
    | (.ok pt, s) => some (some (encodeRecord { g with session := s }, pt))
    | (.error .panic, _) => none
    | (.error _, _) => some none

end CryptoVerification.E2E
