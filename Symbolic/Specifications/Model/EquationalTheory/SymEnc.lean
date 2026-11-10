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
# Symmetric Encryption Equational Theory

DyLean term algebra and attacker deduction rules for AES-256-CBC with PKCS#7 padding (`symEnc` and
`symDec`).
-/

namespace DY.SymEnc

public
class CanSymEnc (Bytes: Type u) where
  symEnc: (key: Bytes) → (iv: Bytes) → (msg: Bytes) → Bytes
  symDec: (key: Bytes) → (iv: Bytes) → (ct: Bytes) → Err Bytes

export CanSymEnc (symEnc symDec)

namespace Enc

public
structure SubF (Bytes: Type) where
  key: Bytes
  iv: Bytes
  msg: Bytes

public instance: ALaCarte.FunctorSizeOf SubF := .ternary SubF.key SubF.iv SubF.msg
public instance: SubBytesFunctor SubF := .ternary SubF.key SubF.iv SubF.msg SubF.mk

/-- PKCS#7 padded ciphertext length `16 * (|msg| / 16 + 1)`. -/
@[expose] public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { msg, .. } rec =>
    16 * (rec msg / 16 + 1)

end Enc

#combine into BytesFunctor, BytesLength from
  Enc,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public
abbrev Enc.SubF.pack (x: Enc.SubF Bytes) := BytesView.pack x

public
instance: CanSymEnc Bytes where
  symEnc key iv msg := ({key, iv, msg}: Enc.SubF Bytes).pack

  symDec key iv ct :=
    match ct.view? Enc.SubF with
    | some {key := key', iv := iv', msg} =>
      if key = key' ∧ iv = iv' then some msg else none
    | none => none

@[expose] public
def symEnc.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ key iv msg, out = symEnc key iv msg ∧ p key ∧ p iv ∧ p msg

@[expose] public
def symDec.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ key iv ct, some out = symDec key iv ct ∧ p key ∧ p iv ∧ p ct

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  symEnc,
  symDec,

end DY.SymEnc
