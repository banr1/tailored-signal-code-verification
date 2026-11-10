/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.CKA.DDHDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs

/-!
# Diffie–Hellman CKA over an abstract DH function and X25519 hook model

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Generalizes ACD19 §4.1.2's Diffie–Hellman CKA from an `F`-module (`CKA/DDHDefs.lean`) to an
abstract Diffie–Hellman function `DHFun` (`dhScheme`), and specifies the relation `X25519Model`
connecting `D` to the binary's X25519 agreement and public-key hooks (`clamp256`, `x25519Base`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.CKA

/-- Abstract Diffie–Hellman function: base point `base` and scalar action `dh : Sc → Pt → Pt`.

**DEV-CKA10 (libsignal): X25519 is not a prime-order group.** ACD19 §4.1.2 builds the CKA from a
cyclic group. X25519 clamps its 32-byte scalars (exponents are not uniform modulo the group order)
and uses x-only points. So the scheme is defined over an abstract DH function, and Thm 3's
assumption becomes DDH for `D` (clamped exponents and x-only points), a non-standard assumption.
Effect: none on `libsignal_binary_e2e`, which does not use Thm 3. -/
structure DHFun (Sc Pt : Type) where
  base : Pt
  dh : Sc → Pt → Pt

namespace DHFun

variable {Sc Pt : Type}

/-- Commutativity on generated public keys: `dh a (dh b base) = dh b (dh a base)`. -/
def Commutes (D : DHFun Sc Pt) : Prop :=
  ∀ a b : Sc, D.dh a (D.dh b D.base) = D.dh b (D.dh a D.base)

section DDH

variable [SampleableType Sc]

end DDH

end DHFun

open DHFun DDH

variable {Sc Pt : Type}

/-- Diffie–Hellman ratchet CKA (ACD19 §4.1.2) over `D : DHFun Sc Pt`: `CKA-S(h; x) =
(x, dh x base, dh x h)` and `CKA-R(x, T) = (T, dh x T)`, returning `0` on out-of-order states
(DEV-CKA9).

**DEV-CKA11 (libsignal): key generation when receiving.** ACD19 Fig. 8 draws a party's next CKA
coins when it next *sends*. libsignal draws the next sending key pair, and runs both root-KDF
steps, when it *receives* a new ratchet key (`dh_ratchet_step`, `double_ratchet.rs:289–291`).
The CKA syntax here stays ACD19's; the session model handles the difference (DEV-LS1).
Effect: none here (see DEV-LS1 for the effect on the session game).

**DEV-CKA17 (libsignal): the initial CKA key is Bob's signed pre-key.** ACD19 Fig. 8 starts from a
fresh secret CKA key `k_CKA`. In libsignal, `x₀` is the secret of Bob's signed pre-key (SPK):
medium-term, shared by Bob's sessions until rotation, and also used by the handshake PQXDH. The
model samples a fresh `x₀` per session. Effect: out of scope (PQXDH; see DEV-LS22). -/
def dhScheme [Zero Pt] (D : DHFun Sc Pt) : CKAScheme Sc (State Sc Pt) Sc Pt Pt where
  initA x₀ := .pub (D.dh x₀ D.base)
  initB x₀ := .exp x₀
  send γ x := match γ with
    | .pub h => (.exp x, D.dh x D.base, D.dh x h)
    | .exp _ => (.exp x, D.dh x D.base, 0)
  receive γ T := match γ with
    | .exp x => (.pub T, D.dh x T)
    | .pub _ => (.pub T, 0)

section Reduction

variable [Zero Sc] [Zero Pt] [SampleableType Sc] (D : DHFun Sc Pt) (tStar : ℕ)

local notation "GameM" => StateT (GameState (State Sc Pt) Pt) ProbComp

end Reduction

/-! ### The X25519 model -/

/-- X25519 base point `u = 9` as 32 little-endian bytes (RFC 7748 §4.1). -/
def x25519Base : List (BitVec 8) := 9 :: List.replicate 31 0

/-- RFC 7748 §5 X25519 scalar clamping on a 256-bit word: clear bits 0–2 and 255, set bit 254. -/
def clamp256 (x : BitVec 256) : BitVec 256 :=
  (x &&& ~~~((7 : BitVec 256) ||| ((1 : BitVec 256) <<< 255))) ||| ((1 : BitVec 256) <<< 254)

/-- Hypothesis relating an abstract `DHFun` `D` (via an injective 32-byte point encoding `enc`) to
the binary's X25519 agreement hook `x25519` and public-key derivation hook `pubKey`.

**DEV-CKA12 (libsignal): only prime-order points.** ACD19's group has no invalid elements.
libsignal accepts any 32 bytes as a public key (twist, low-order and non-canonical `u`). `Pt`
holds only prime-order-subgroup points, so the session game refuses injected ratchet keys outside
`Pt`. Effect: restricts the adversary (DEV-LS5).

**DEV-CKA13 (libsignal): corruption leaks the raw coins.** The CKA state holds the raw 256-bit
coins `x`; libsignal stores, and a compromise reveals, the clamped bytes `clamp256 x`
(`curve25519.rs:34`, `private_key_bytes`). The raw coins determine the clamped ones, so the model's
adversary learns at least as much. Effect: none (conservative).

**DEV-CKA16 (machine model): ideal randomness.** The coins `x` are uniform 256-bit strings: the
caller's random number generator (libsignal's `CryptoRng`) is assumed perfect. ACD19 also assumes
uniform coins. Effect: none; the generator's machine code is hooked, not verified (DEV-E8). -/
structure X25519Model [Zero Pt] (D : DHFun (BitVec 256) Pt) (enc : Pt → List (BitVec 8))
    (x25519 : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (pubKey : List (BitVec 8) → List (BitVec 8)) : Prop where
  enc_injective : Function.Injective enc
  enc_length : ∀ P, (enc P).length = 32
  enc_zero : enc 0 = List.replicate 32 0
  enc_base : enc D.base = x25519Base
  base_ne_zero : D.base ≠ 0
  hook : ∀ (x : BitVec 256) (P : Pt), x25519 (HMAC.keyToBytes32 x) (enc P) = enc (D.dh x P)
  /-- **DEV-CKA14 (machine model): public-key derivation is a separate hook.** The binary derives
  public keys with `mul_base_clamped`, not with the ladder on `u = 9`, so `pubKey` is its own hook
  and this field ties it to `D`. Effect: none (a hypothesis on the hooks). -/
  pubKey_hook : ∀ x : BitVec 256, pubKey (HMAC.keyToBytes32 x) = enc (D.dh x D.base)
  dh_clamp : ∀ (x : BitVec 256) (P : Pt), D.dh (clamp256 x) P = D.dh x P
  /-- **DEV-CKA15 (libsignal): honest agreements are never all-zero.** libsignal rejects an
  all-zero agreement (`curve.rs:303–306`); this hypothesis (true on prime-order points) says the
  check never fires on honest keys. Effect: none (a hypothesis on `D`). -/
  dh_ne_zero : ∀ (x : BitVec 256) (P : Pt), P ≠ 0 → D.dh x P ≠ 0

end CryptoGames.CKA
