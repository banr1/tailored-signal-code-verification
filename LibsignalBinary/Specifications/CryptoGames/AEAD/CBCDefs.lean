/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs

/-!
# AES-256-CBC with PKCS#7 padding as a one-time cipher

**Trusted in part.** The theorems of `Computational/Theorems/` use only `AesKey`, `Block`, `Plain`,
`bytesToBlock`, `cbcEncrypt`, `cbcScheme`, `nBlocks`, `padLen`, `pkcs7Blocks`, `pkcs7Bytes`,
`cbcPkcs7EncryptOnly` from this file: read them. Everything else here is checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Models libsignal's `signal_crypto::aes_256_cbc_encrypt` over an abstract AES-256 block function
`E : AesKey → Block → Block` (DEV-AEAD14), together with monadic CBC `cbcM`, the PRF wrapper
`blockPRF`, and the one-time IND-CPA-to-PRF reduction `cbcRed` (`CBC.lean`). Decryption is
specified separately in `CBCDecDefs.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace CBC

/-- A 128-bit AES block. -/
abbrev Block := BitVec 128

/-- A 256-bit AES key. -/
abbrev AesKey := BitVec 256

/-- CBC encryption of the blocks `P` with block function `f`, starting from the chaining value
`prev` (the IV): `C₁ = f (P₁ ⊕ prev)`, `Cᵢ₊₁ = f (Pᵢ₊₁ ⊕ Cᵢ)`.

**DEV-AEAD8 (libsignal): the IV is part of the key.** libsignal derives the IV with HKDF (the
HMAC-based key derivation) together with the keys, and never transmits it. So the IV is part of the
one-time key `(k, iv)` and not of the ciphertext. Effect: none. -/
def cbcEncrypt (f : Block → Block) (prev : Block) :
    {n : ℕ} → List.Vector Block n → List.Vector Block n
  | 0, _ => List.Vector.nil
  | _ + 1, P =>
    let c := f (P.head ^^^ prev)
    c ::ᵥ cbcEncrypt f c P.tail

/-- Monadic CBC: the same chaining, with each block-function call `f x` an effect (used by the
reduction `cbcRed`, where `f` is a PRF-oracle query). -/
def cbcM {m : Type → Type} [Monad m] (f : Block → m Block) (prev : Block) :
    {n : ℕ} → List.Vector Block n → m (List.Vector Block n)
  | 0, _ => pure List.Vector.nil
  | _ + 1, P => do
    let c ← f (P.head ^^^ prev)
    let cs ← cbcM f c P.tail
    pure (c ::ᵥ cs)

/-! ### PKCS#7 padding -/

/-- A plaintext of exactly `ℓ` bytes. CBC with PKCS#7 reveals the length, so the game fixes it.

**DEV-AEAD2 (libsignal): one plaintext length per session.** ACD19 Def. 2 compares the real
ciphertext with a uniformly random one. AES-CBC with PKCS#7 padding reveals the number of blocks,
so every plaintext of a session has the same length `ℓ`; the end-to-end adversary's messages have
type `CBC.Plain ℓ`. Effect: restricts the adversary (no claim for sessions that mix message
lengths). -/
abbrev Plain (ℓ : ℕ) := List.Vector (BitVec 8) ℓ

/-- Number of ciphertext blocks for an `ℓ`-byte plaintext. -/
def nBlocks (ℓ : ℕ) : ℕ := ℓ / 16 + 1

/-- PKCS#7 pad length: `16 − (ℓ mod 16)`, always in `1..16`. -/
def padLen (ℓ : ℕ) : ℕ := 16 - ℓ % 16

/-- The padded byte string: `m` followed by `padLen ℓ` copies of the byte `padLen ℓ`. -/
def pkcs7Bytes {ℓ : ℕ} (m : Plain ℓ) : List (BitVec 8) :=
  m.toList ++ List.replicate (padLen ℓ) (BitVec.ofNat 8 (padLen ℓ))

/-- Little-endian block of (up to) 16 bytes: byte `j` occupies bits `8j .. 8j+7`, as in an AArch64
16-byte load. -/
def bytesToBlock (bs : List (BitVec 8)) : Block :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend 128) 0

/-- PKCS#7 padding split into `nBlocks ℓ` blocks: block `i` is bytes `16i .. 16i+15`. -/
def pkcs7Blocks {ℓ : ℕ} (m : Plain ℓ) : List.Vector Block (nBlocks ℓ) :=
  List.Vector.ofFn fun i => bytesToBlock (((pkcs7Bytes m).drop (16 * i.val)).take 16)

/-! ### The cipher and the PRF -/

/-- CBC with key `(k, iv)` applied to a deterministic block encoding `encode` of the message.
Decryption is out of scope and always rejects. -/
def cbcScheme {M : Type} {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n) :
    CipherScheme (AesKey × Block) M (List.Vector Block n) where
  enc k m := cbcEncrypt (E k.1) k.2 (encode m)
  dec _ _ := none

/-- libsignal's AES-256-CBC with PKCS#7 padding on `ℓ`-byte plaintexts, AES abstracted as `E`.

**DEV-AEAD14 (machine model): AES and SHA-256 are arbitrary functions.** The AES-256 block
function `E` here and the SHA-256 compression function `F` of `AEAD/HMACDefs.lean` are parameters,
because in the binary they are hooks whose machine code is not verified (DEV-E8). The assumptions
(`blockPRF E` and HMAC are PRFs) are about whatever the hooks compute. Effect: none. -/
abbrev cbcPkcs7EncryptOnly (E : AesKey → Block → Block) (ℓ : ℕ) :
    CipherScheme (AesKey × Block) (Plain ℓ) (List.Vector Block (nBlocks ℓ)) :=
  cbcScheme E pkcs7Blocks

/-- The block function `E` as a PRF with key `AesKey`, for `MACScheme.prfAdvantage`.

**DEV-AEAD4 (formalization): AES is assumed a PRF.** AES is a permutation; the IND-CPA proof of
CBC assumes it is a pseudorandom *function*. Assuming a PRP (pseudorandom permutation) instead would
add a birthday term by PRP/PRF switching. Effect: none (a named assumption). -/
def blockPRF (E : AesKey → Block → Block) : MACScheme AesKey Block Block := ⟨E⟩

/-! ### The PRF reduction -/

/-- Query implementation of `cbcRed`: forwards the adversary's coins, and answers the single
`encrypt(m)` query by sampling a uniform IV and computing CBC of `encode m` with PRF-oracle queries
as the block function. Later `encrypt` queries return `none`. The state records whether `encrypt`
was already queried. -/
def cbcRedImpl {M : Type} {n : ℕ} (encode : M → List.Vector Block n) :
    QueryImpl (unifSpec + CipherScheme.indcpaSpec M (List.Vector Block n))
      (StateT Bool (OracleComp (unifSpec + MACScheme.prfSpec Block Block))) :=
  fun q => match q with
  | .inl k => StateT.lift (query (spec := unifSpec + MACScheme.prfSpec Block Block) (.inl k))
  | .inr m => do
    let queried ← get
    if queried then return none
    set true
    let iv ← StateT.lift (liftM ($ᵗ Block : ProbComp Block) :
      OracleComp (unifSpec + MACScheme.prfSpec Block Block) Block)
    let c ← StateT.lift (cbcM (MACScheme.evalQuery (Input := Block) (Tag := Block)) iv (encode m))
    return some c

/-- PRF reduction `cbcRed encode A`: runs the one-time IND-CPA adversary `A`, answering its
`encrypt(m)` query with CBC of `encode m` under a fresh uniform IV and the PRF oracle as block
function, and outputs `A`'s bit. -/
def cbcRed {M : Type} {n : ℕ} (encode : M → List.Vector Block n)
    (A : CipherScheme.INDCPAAdversary M (List.Vector Block n)) :
    MACScheme.PRFAdversary Block Block :=
  (simulateQ (cbcRedImpl encode) A).run' false

end CBC
end CryptoGames
