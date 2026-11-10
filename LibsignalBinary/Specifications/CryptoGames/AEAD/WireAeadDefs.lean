/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead

/-!
# Wire OT-CCA game and libsignal's per-message AEAD on raw wire bytes

**Trusted in part.** The theorems of `Computational/Theorems/` use only 13 definitions of this file,
listed in `Computational/docs/TRUSTED_BASE.md` §3: read them. Everything else here is checked by
Lean.

Because libsignal authenticates the raw received bytes `ids ‖ ser` while parsing `ser` with a
non-canonical protobuf parser, ciphertexts in `WireAEAD` are raw `(wire bytes, tag)` pairs rather
than structured `(header, body, tag)` tuples. This file defines the wire OT-CCA game
(`wireSpec`, `WireState`, `idealEnc`, `wireEncrypt`, `wireDecrypt`, `wireOtccaGame`,
`wireOtccaAdvantage`) and libsignal's concrete instance `libsignalWireAead` (`WireCodec`,
`wireEncode`, `libsignalReceiveWire`; DEV-AEAD2, DEV-AEAD4, DEV-AEAD7, DEV-LS30).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

/-- Deterministic AEAD on raw wire bytes `(w, τ)`, with key `K`, associated data `AD`, public
header `H` serialized into `w` and recovered by `dec`, sender plaintext `M`, receiver plaintext
`M'`, ideal-world body `C`, and tag `T`. -/
structure WireAEAD (K AD H M M' C T : Type) where
  /-- Serialize header `h` and body `c` into wire bytes; used to form the ideal ciphertext
  `(encode h c, τ)` for uniform `c` and `τ`. -/
  encode : H → C → List (BitVec 8)
  /-- `Enc(k, a, h, m) = (w, τ)`. -/
  enc : K → AD → H → M → List (BitVec 8) × T
  /-- `Dec(k, a, (w, τ))` on arbitrary bytes `w`, returning the parsed header and plaintext or
  `none`.

  **DEV-AEAD9 (libsignal): the header is an output of decryption.** ACD19 Def. 1's `Dec(K, a, e)`
  takes the AD `a` as an input that the receiver knows. libsignal's receiver reads the header
  (ratchet key, counters) from the received bytes, so the header is an output of `dec`, not an AD
  the receiver checks. Effect: none. -/
  dec : K → AD → List (BitVec 8) × T → Option (H × M')

namespace WireAEAD

variable {K AD H M M' C T : Type}

/-- The wire OT-CCA oracles: a one-time `encrypt(a, h, m)` and an unbounded `decrypt(a, (w, τ))`
on arbitrary wire bytes. -/
abbrev wireSpec (AD H M M' T : Type) :=
  ((AD × H × M) →ₒ Option (List (BitVec 8) × T)) +
    ((AD × (List (BitVec 8) × T)) →ₒ Option (H × M'))

/-- A wire OT-CCA adversary, with its own coins (`unifSpec`) and the wire oracles. -/
abbrev WireAdversary (AD H M M' T : Type) :=
  OracleComp (unifSpec + wireSpec AD H M M' T) Bool

/-- Game state: key, hidden bit, and the challenge `(a*, (w*, τ*))` (`none` before `encrypt`).
This is `OTCCAState` of `CryptoGames/Primitives.lean` with ciphertext `List (BitVec 8) × T`. -/
abbrev WireState (K AD T : Type) := AEADScheme.OTCCAState K AD (List (BitVec 8) × T)

/-- The ideal ciphertext for header `h`: `(encode h c, τ)` with uniform body `c` and tag `τ`. -/
def idealEnc [SampleableType C] [SampleableType T] (ae : WireAEAD K AD H M M' C T) (h : H) :
    ProbComp (List (BitVec 8) × T) := do
  let c ← $ᵗ C
  let τ ← $ᵗ T
  return (ae.encode h c, τ)

/-- `encrypt(a, h, m)`: one-time; `b = false` real, `b = true` the ideal ciphertext for `h`. -/
def wireEncrypt [SampleableType C] [SampleableType T] (ae : WireAEAD K AD H M M' C T) :
    QueryImpl ((AD × H × M) →ₒ Option (List (BitVec 8) × T))
      (StateT (WireState K AD T) ProbComp) := fun ⟨a, h, m⟩ => do
  let st ← get
  if st.chal.isSome then return none
  let e ← if st.b then liftM (ae.idealEnc h) else pure (ae.enc st.key a h m)
  set { st with chal := some (a, e) }
  return some e

/-- `decrypt(a, (w, τ))` on any bytes: rejects the exact challenge `(a*, (w*, τ*))`; always
rejects when `b = true`. A different `w` that parses to the challenge's header and body is **not**
the challenge (this is what a raw-bytes MAC must reject). -/
def wireDecrypt [DecidableEq AD] [DecidableEq T] (ae : WireAEAD K AD H M M' C T) :
    QueryImpl ((AD × (List (BitVec 8) × T)) →ₒ Option (H × M'))
      (StateT (WireState K AD T) ProbComp) := fun ⟨a, e⟩ => do
  let st ← get
  if st.b || st.chal == some (a, e) then return none
  return ae.dec st.key a e

/-- Wire OT-CCA hidden-bit game.

**DEV-AEAD10 (libsignal): OT-CCA on raw wire bytes.** ACD19 Fig. 1 decrypts structured
ciphertexts and its ideal ciphertext is uniform. libsignal MACs the raw received bytes and parses
them non-canonically, so here decryption takes arbitrary bytes, and the ideal ciphertext is
`encode h` of a uniform body with a uniform tag (the header stays public). Effect: none; security
is proved for every codec. -/
def wireOtccaGame [SampleableType K] [SampleableType C] [SampleableType T] [DecidableEq AD]
    [DecidableEq T] (ae : WireAEAD K AD H M M' C T) (A : WireAdversary AD H M M' T) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let key ← $ᵗ K
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (WireState K AD T) ProbComp)
    + (ae.wireEncrypt + ae.wireDecrypt)
  let b' ← (simulateQ impl A).run' { key, b }
  return b == b'

/-- `Adv^{wire-ot-cca}(A)`, the bias `2·|Pr[b = b'] − 1/2|`. -/
noncomputable def wireOtccaAdvantage [SampleableType K] [SampleableType C] [SampleableType T]
    [DecidableEq AD] [DecidableEq T] (ae : WireAEAD K AD H M M' C T)
    (A : WireAdversary AD H M M' T) : ℝ≥0∞ :=
  𝒟[ae.wireOtccaGame A].boolBias

variable {KE : Type}

end WireAEAD

/-! ### libsignal's per-message AEAD on the wire -/

namespace LibsignalAead

open CBC HMAC WireAEAD

/-- Abstract wire codec for a `SignalMessage` header `H` and arbitrary-length byte body. -/
structure WireCodec (H : Type) where
  /-- Serialize header and body bytes into `ver ‖ protobuf(h, body)`. -/
  encode : H → List (BitVec 8) → List (BitVec 8)
  /-- Parse serialized bytes into header and body bytes, or `none` on failure. -/
  parse : List (BitVec 8) → Option (H × List (BitVec 8))

/-- Restrict a byte-body `WireCodec` to the fixed-block `WireEnc H n` on `16·n`-byte bodies. -/
def WireCodec.toWireEnc {H : Type} (codec : WireCodec H) (n : ℕ) : WireEnc H n where
  encode h c := codec.encode h (c.toList.flatMap blockToBytesLE)
  parse w :=
    match codec.parse w with
    | none => none
    | some (h, body) =>
      if hb : body.length = 16 * n then
        some (h, ⟨chunks16 body, by simp [chunks16, hb]⟩)
      else none

/-- Sender wire bytes for header `h` and CBC ciphertext blocks `c`. -/
def wireEncode {H : Type} {n : ℕ} (codec : WireCodec H) (h : H) (c : List.Vector Block n) :
    List (BitVec 8) :=
  codec.encode h (c.toList.flatMap blockToBytesLE)

/-- Receiver decryption on arbitrary wire bytes `(ser, tag)` under key
`k = ((cipher_key, iv), mac_key)`: verify HMAC-SHA256/8 over `ids ‖ ser`, parse `ser`, CBC-decrypt
and unpad the body via `cbcDecRaw`, and check `addressCheckPasses (addrs h) expected`.

**DEV-AEAD11 (libsignal): only the address-checking path.** Only the `local_address = Some` path
is modeled (`verify_mac_with_addresses`, `triple_ratchet.rs:257–263`). The legacy path that calls
plain `verify_mac` when `local_address = None` (`session_cipher_legacy.rs:693–705`) is not.
Effect: out of scope (the legacy path).

**DEV-AEAD12 (libsignal): key selection is not part of the AEAD.** libsignal selects the message
keys from the unauthenticated header before `verify_mac` (`triple_ratchet.rs:225–254`). Here the
key `k` is given: key selection belongs to the FS-AEAD (forward-secure AEAD) layer. Effect: none. -/
def libsignalReceiveWire {H : Type} (D : AesKey → Block → Block) (F : ShaState → List (BitVec 8) → ShaState)
    (codec : WireCodec H) (addrs : H → Option (List (BitVec 8)))
    (k : (AesKey × Block) × BitVec 256) (ids : SerializedIdentityKeys) (expected : Option (List (BitVec 8)))
    (wire : List (BitVec 8) × BitVec 64) : Option (H × List (BitVec 8)) :=
  if (hmacScheme F).tag k.2 (ids.toList ++ wire.1) == wire.2 then
    match codec.parse wire.1 with
    | none => none
    | some (h, body) =>
      match cbcDecRaw D k.1.1 k.1.2 body with
      | none => none
      | some m => if addressCheckPasses (addrs h) expected then some (h, m) else none
  else none

/-- libsignal's per-message `WireAEAD`: AES-256-CBC-PKCS#7 encryption (`cbcPkcs7EncryptOnly E ℓ`),
wire serialization via `codec`, and 8-byte truncated HMAC-SHA256 over `ids ‖ ser`, paired with
`libsignalReceiveWire`.

**DEV-AEAD3 (libsignal): libsignal's concrete AEAD.** ACD19 assumes an abstract OT-CCA secure
AEAD. libsignal's is Encrypt-then-MAC with AES-256-CBC (PKCS#7 padding) and HMAC-SHA256 truncated
to 8 bytes. Effect: constants: with an 8-byte tag, every OT-CCA bound for it has a forgery term of
at least (decryption queries)·2^-64.

**DEV-AEAD13 (libsignal): fixed expected addresses.** The receiver's expected addresses `expected`
and the header's `addrs` map are parameters of the scheme (the receiver's local session data), not
adversarial input. Effect: none. -/
def libsignalWireAead {H : Type} (E D : AesKey → Block → Block)
    (F : ShaState → List (BitVec 8) → ShaState) (ℓ : ℕ) (codec : WireCodec H)
    (addrs : H → Option (List (BitVec 8))) (expected : Option (List (BitVec 8))) :
    WireAEAD ((AesKey × Block) × BitVec 256) SerializedIdentityKeys H (Plain ℓ) (List (BitVec 8))
      (List.Vector Block (nBlocks ℓ)) (BitVec 64) where
  encode := wireEncode codec
  enc k ids h m :=
    let ser := wireEncode codec h ((cbcPkcs7EncryptOnly E ℓ).enc k.1 m)
    (ser, (hmacScheme F).tag k.2 (ids.toList ++ ser))
  dec k ids wire := libsignalReceiveWire D F codec addrs k ids expected wire

end LibsignalAead
end CryptoGames
