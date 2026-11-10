/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Bytes.AttackerKnowledge
public import DY.Trace.Monad
public import Symbolic.Specifications.Model.EquationalTheory.Representable
import DY.Meta.CombineMacro

/-!
# Post-Quantum KEM Equational Theory

DyLean term algebra and attacker deduction rules for Kyber-1024 / ML-KEM-1024. `SharedSecret`
binds the target public key `pk` alongside `entropy`, `kemDecap` returns `none` on mismatch, and
`kemRejKey` models Kyber-1024 round-3 secret-keyed implicit rejection.
-/

namespace DY.PQKem

public
class CanPQKem.{u} (Bytes: Type u) where
  kemPk: (sk: Bytes) → Bytes
  kemEncap: (pk: Bytes) → (entropy: Bytes) → Bytes × Bytes
  kemDecap: (sk: Bytes) → (cipher: Bytes) → Err Bytes
  /-- Kyber-1024 implicit-rejection key derived from `sk` and `cipher`. -/
  kemRejKey: (sk: Bytes) → (cipher: Bytes) → Bytes

export CanPQKem (kemPk kemEncap kemDecap kemRejKey)

namespace Pk

/-- 1568-byte KEM public key `kemPk sk`. -/
public structure SubF (Bytes: Type) where
  sk: Bytes

public instance: ALaCarte.FunctorSizeOf SubF := .unary SubF.sk
public instance: SubBytesFunctor SubF := .unary SubF.sk SubF.mk
@[expose] public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun _ _ => 1568

end Pk

namespace Encap

/-- 1568-byte KEM ciphertext encapsulated to `pk` with randomness `entropy`. -/
public structure SubF (Bytes: Type) where
  pk: Bytes
  entropy: Bytes

public instance: ALaCarte.FunctorSizeOf SubF := .binary SubF.pk SubF.entropy
public instance: SubBytesFunctor SubF := .binary SubF.pk SubF.entropy SubF.mk
@[expose] public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun _ _ => 1568

end Encap

namespace SharedSecret

/-- 32-byte KEM shared secret bound to `pk` and `entropy`. -/
public structure SubF (Bytes: Type) where
  pk: Bytes
  entropy: Bytes

public instance: ALaCarte.FunctorSizeOf SubF := .binary SubF.pk SubF.entropy
public instance: SubBytesFunctor SubF := .binary SubF.pk SubF.entropy SubF.mk
@[expose] public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun _ _ => 32

end SharedSecret

namespace RejKey

/-- 32-byte Kyber-1024 implicit-rejection key derived from `sk` and `cipher`. -/
public
structure SubF (Bytes: Type) where
  sk: Bytes
  cipher: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {sk, cipher} => sizeOf sk + sizeOf cipher

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }
  toRepr | {sk, cipher} => { id := (), data := (), as := #v[sk, cipher] }
  fromRepr
  | {id, data, as} => { sk := as[0], cipher := as[1] }
  from_to | {sk, cipher} => by rfl
  to_from
  | {id, data, as} => by simp_all <;> grind
  sizeOf_eq | {sk, cipher} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

@[expose] public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ => 32

end RejKey

#combine into BytesFunctor, BytesLength from
  Pk,
  Encap,
  SharedSecret,
  RejKey,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Pk.SubF.pack (x: Pk.SubF Bytes) := BytesView.pack x
public abbrev Encap.SubF.pack (x: Encap.SubF Bytes) := BytesView.pack x
public abbrev SharedSecret.SubF.pack (x: SharedSecret.SubF Bytes) := BytesView.pack x
public abbrev RejKey.SubF.pack (x: RejKey.SubF Bytes) := BytesView.pack x

public
instance: CanPQKem Bytes where
  kemPk sk := ({sk}: Pk.SubF Bytes).pack

  kemEncap pk entropy :=
    (({pk, entropy}: Encap.SubF Bytes).pack, ({pk, entropy}: SharedSecret.SubF Bytes).pack)

  kemDecap sk cipher :=
    match cipher.view? Encap.SubF with
    | some { pk, entropy } =>
      match pk.view? Pk.SubF with
      | some { sk := sk' } =>
        if sk = sk' then some ({pk, entropy}: SharedSecret.SubF Bytes).pack else none
      | none => none
    | none => none

  kemRejKey sk cipher := ({sk, cipher}: RejKey.SubF Bytes).pack

/-- Extracts `sk` from a `kemPk sk` term. Used only by the PQXDH state machine after `BrokenKEM`. -/
@[expose] public
def invertKemPublicKey (pk: Bytes): Err Bytes :=
  match pk.view? Pk.SubF with
  | some { sk } => some sk
  | none => none

@[expose] public
def kemPk.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ sk, out = kemPk sk ∧ p sk

@[expose] public
def kemEncapCipher.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ pk entropy rhs, (out, rhs) = kemEncap pk entropy ∧ p pk ∧ p entropy

@[expose] public
def kemEncapSS.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ pk entropy lhs, (lhs, out) = kemEncap pk entropy ∧ p pk ∧ p entropy

@[expose] public
def kemDecap.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ sk cipher, some out = kemDecap sk cipher ∧ p sk ∧ p cipher

@[expose] public
def kemRejKey.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ sk cipher, out = kemRejKey sk cipher ∧ p sk ∧ p cipher

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  kemPk,
  kemEncapCipher,
  kemEncapSS,
  kemDecap,
  kemRejKey,

end DY.PQKem
