/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Bytes.AttackerKnowledge
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.DiffieHellman
public import Symbolic.Specifications.Model.EquationalTheory.Representable
import DY.Meta.CombineMacro

/-!
# X25519 Key Decoding, Encoding Variants, and 8-Torsion

Byte-level RFC 7748 u-coordinate decoding, low-order point detection, and the DyLean term algebra
for non-canonical 32-byte public-key encodings (`Fin 4`) and 8-torsion shifts (`Fin 8`).
-/

namespace DY.X25519

@[expose] public def p25519 : Nat := 2 ^ 255 - 19

/-- Little-endian `Nat` value of a byte list. -/
@[expose] public def leValue : List Nat → Nat
  | [] => 0
  | x :: xs => x + 256 * leValue xs

/-- RFC 7748 `decodeUCoordinate`: clear bit 255 and reduce modulo `p25519`. -/
@[expose] public def uCoord (bytes : List Nat) : Nat := leValue bytes % 2 ^ 255 % p25519

/-- Curve25519 and twist u-coordinates in `[0, p25519)` on which clamped X25519 scalar
multiplication outputs all zeros. -/
@[expose] public def lowOrderUs : List Nat :=
  [0, 1, 325606250916557431795983626356110631294008115727848805560023387167927233504,
    39382357235489614581723060781553021112529911719440698176882885853963445705823,
    p25519 - 1]

/-- Whether `bytes` is a 32-byte key whose `uCoord` lies in `lowOrderUs`. -/
@[expose] public def isLowOrderKey (bytes : List Nat) : Bool :=
  bytes.length == 32 && lowOrderUs.contains (uCoord bytes)

namespace Variant

/-- Public key paired with a non-canonical encoding selector `variation` and 8-torsion shift
`torsion`. -/
public
structure SubF (Bytes: Type) where
  key: Bytes
  variation: Fin 4
  torsion: Fin 8 := 0

public instance: ALaCarte.FunctorSizeOf SubF := .unary SubF.key
public instance: SubBytesFunctor SubF :=
  .unaryData (Fin 32)
    (fun {variation, torsion, ..} => ⟨variation.val + 4 * torsion.val, by omega⟩)
    SubF.key
    (fun d key => { key, variation := ⟨d.val % 4, by omega⟩, torsion := ⟨d.val / 4, by omega⟩ })
    (fun {key, variation, torsion} => by simp [Fin.ext_iff] <;> omega)
    (fun d _ => by simp [Fin.ext_iff]; omega)

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ => 32

end Variant

#combine into BytesFunctor, BytesLength from
  Variant,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev Variant.SubF.pack (x: Variant.SubF Bytes) := BytesView.pack x

/-- Strip an outer `Variant.SubF` wrapper if present. -/
@[expose] public
def normalizeX25519Key (pk: Bytes): Bytes :=
  match pk.view? Variant.SubF with
  | some x => x.key
  | none => pk

/-- Apply encoding selector `v` and 8-torsion shift `t` to `normalizeX25519Key key`, returning the
normalized key unchanged when `v = 0 ∧ t = 0`. -/
@[expose] public
def x25519TorsionVariant (key: Bytes) (v: Fin 4) (t: Fin 8): Bytes :=
  if v = 0 ∧ t = 0 then normalizeX25519Key key
  else ({key := normalizeX25519Key key, variation := v, torsion := t}: Variant.SubF Bytes).pack

@[expose] public
def x25519Variant.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ key v t, out = x25519TorsionVariant key v t ∧ p key

@[expose] public
def normalizeX25519Key.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ x: Variant.SubF Bytes, p x.pack ∧ out = x.key

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  x25519Variant,
  normalizeX25519Key,

/-- Whether `normalizeX25519Key pk` is a literal 32-byte low-order key. -/
@[expose] public
def x25519LowOrder [BytesFunctor.Has Literal.SubF] (pk: Bytes): Bool :=
  match Literal.bytesToLiteral (normalizeX25519Key pk) with
  | some b => isLowOrderKey (b.data.toList.map (·.toNat))
  | none => false

/-- Symbolic `PublicKey::is_canonical` check: rejects `Variant.SubF` wrappers and literal low-order
keys. -/
@[expose] public
def isCanonicalKey [BytesFunctor.Has Literal.SubF] (pk: Bytes): Bool :=
  (pk.view? Variant.SubF).isNone && !x25519LowOrder pk

/-- Symbolic X25519 Diffie-Hellman agreement on `normalizeX25519Key pk` and secret key `sk`. -/
@[expose] public
def agree [BytesFunctor.Has DiffieHellman.SubF] (pk sk: Bytes): Bytes :=
  DiffieHellman.dh (normalizeX25519Key pk) sk

end DY.X25519
