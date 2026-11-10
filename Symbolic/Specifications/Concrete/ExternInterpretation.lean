/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Concrete.ByteSpecs
public import Symbolic.Specifications.Concrete.ImageSymbols
public import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Cryptographic Extern Interpretations and Laws

**Trusted: definitions used by the statement.**

Byte-level interpretation of external cryptographic primitives called by the `signal-session`
binary, together with the algebraic and torsion-check laws assumed by the refinement and security
statements.
-/

@[expose] public section

namespace CryptoProofLib.Refinement

abbrev ByteString := List (BitVec 8)

/-- Partial byte-level semantics `symbol → args → Option ByteString` for external functions. -/
abbrev ExternInterpretation := String → List ByteString → Option ByteString

end CryptoProofLib.Refinement

namespace DY.Libsignal.Refinement

open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open ByteSpecs (ShaState)

/-- Spec-only symbol adding the `t`-th Curve25519 8-torsion point to a 32-byte u-coordinate. -/
def x25519TorsionSymbol : String := "spec::x25519_add_eight_torsion"

/-- Adds the `t`-th 8-torsion point to `point` via `x25519TorsionSymbol`, returning `point` when
`t = 0`, `point` is not 32 bytes, or the result is not 32 bytes. -/
def torsionShift (interpretation : ExternInterpretation) (point : ByteString) (t : Fin 8) :
    ByteString :=
  if t = 0 ∨ point.length ≠ 32 then point
  else match interpretation x25519TorsionSymbol [point, [BitVec.ofNat 8 t.val]] with
    | some q => if q.length = 32 then q else point
    | none => point

/-- Encodes a SHA-256 chaining state as eight little-endian 32-bit words. -/
def shaStateBytes (state : ShaState) : ByteString :=
  state.toList.flatMap fun word =>
    [word.extractLsb' 0 8, word.extractLsb' 8 8, word.extractLsb' 16 8, word.extractLsb' 24 8]

/-- Decodes eight little-endian 32-bit words from `bytes` (zero-filling missing bytes). -/
def shaStateOfBytes (bytes : ByteString) : ShaState :=
  List.Vector.ofFn fun i : Fin 8 =>
    let byte := fun j => (bytes.getD (4 * i.val + j) 0).toNat
    BitVec.ofNat 32 (byte 0 + 256 * byte 1 + 65536 * byte 2 + 16777216 * byte 3)

/-- Lifts `sha256CompressSymbol` to a compression function on `ShaState`. -/
def sha256CompressFunction (interpretation : ExternInterpretation) (state : ShaState)
    (block : ByteString) : ShaState :=
  shaStateOfBytes ((interpretation sha256CompressSymbol [shaStateBytes state, block]).getD [])

/-- Algebraic and output-length laws assumed of X25519, AES-256-CBC with strict PKCS#7 padding,
and HMAC-SHA256. -/
structure ExternCryptoLawsHold (interpretation : ExternInterpretation) : Prop where
  x25519_agreement_commutes : ∀ a b : ByteString,
    interpretation x25519AgreementSymbol [a, (interpretation x25519PublicKeySymbol [b]).getD []] =
      interpretation x25519AgreementSymbol [b, (interpretation x25519PublicKeySymbol [a]).getD []]
  x25519_agreement_length : ∀ secret point : ByteString,
    ((interpretation x25519AgreementSymbol [secret, point]).getD []).length = 32
  x25519_public_key_length : ∀ secret : ByteString,
    ((interpretation x25519PublicKeySymbol [secret]).getD []).length = 32
  x25519_agreement_reads_u_coordinate : ∀ secret point point' : ByteString,
    point.length = 32 → point'.length = 32 →
    DY.X25519.uCoord (point.map BitVec.toNat) = DY.X25519.uCoord (point'.map BitVec.toNat) →
    interpretation x25519AgreementSymbol [secret, point] =
      interpretation x25519AgreementSymbol [secret, point']
  x25519_agreement_torsion_invariant : ∀ (secret point : ByteString) (t : Fin 8),
    interpretation x25519AgreementSymbol [secret, torsionShift interpretation point t] =
      interpretation x25519AgreementSymbol [secret, point]
  x25519_agreement_zero_iff_low_order : ∀ secret point : ByteString,
    secret.length = 32 → point.length = 32 →
    ((interpretation x25519AgreementSymbol [secret, point]).getD [] = List.replicate 32 0 ↔
      DY.X25519.isLowOrderKey (point.map BitVec.toNat) = true)
  x25519_public_key_not_low_order : ∀ secret : ByteString, secret.length = 32 →
    DY.X25519.isLowOrderKey
      (((interpretation x25519PublicKeySymbol [secret]).getD []).map BitVec.toNat) = false
  aes_cbc_decrypt_inverts_encrypt : ∀ plaintext key iv : ByteString,
    interpretation aesCbcDecryptSymbol
        [(interpretation aesCbcEncryptSymbol [plaintext, key, iv]).getD [], key, iv] =
      some plaintext
  aes_cbc_encrypt_of_decrypt : ∀ c k iv p : ByteString,
    k.length = 32 → iv.length = 16 →
    interpretation aesCbcDecryptSymbol [c, k, iv] = some p →
    interpretation aesCbcEncryptSymbol [p, k, iv] = some c
  hmac_tag_length : ∀ key data tag : ByteString,
    interpretation DY.Libsignal.PQXDH.Refinement.libcruxHmacSymbol [key, data] = some tag →
      tag.length = 32

end DY.Libsignal.Refinement

namespace DY.Libsignal.PQXDH.Refinement

open CryptoProofLib.Refinement (ByteString ExternInterpretation)

/-- Whether `PublicKey::is_torsion_free` accepts the 32-byte Montgomery key `b` after decompressing
it to an Edwards point. -/
def X25519TorsionFree (interpretation : ExternInterpretation) (b : ByteString) : Prop :=
  ∃ pt : ByteString, pt.length = 160 ∧
    interpretation toEdwardsSymbol [b, [0#8]] = some pt ∧
    interpretation torsionFreeSymbol [pt] = some [1#8]

/-- Requires `X25519TorsionFree` to reject any 32-byte key whose u-coordinate equals a non-trivial
8-torsion shift of an X25519 public key. -/
def X25519TorsionShiftsRejected (interpretation : ExternInterpretation) : Prop :=
  ∀ (s : ByteString) (t : Fin 8) (k : ByteString), k.length = 32 →
    DY.X25519.uCoord (k.map BitVec.toNat) =
      DY.X25519.uCoord ((DY.Libsignal.Refinement.torsionShift interpretation
        ((interpretation DY.Libsignal.Refinement.x25519PublicKeySymbol [s]).getD [])
        t).map BitVec.toNat) →
    DY.X25519.uCoord (k.map BitVec.toNat) ≠
      DY.X25519.uCoord
        (((interpretation DY.Libsignal.Refinement.x25519PublicKeySymbol [s]).getD
          []).map BitVec.toNat) →
    ¬ X25519TorsionFree interpretation k

end DY.Libsignal.PQXDH.Refinement
