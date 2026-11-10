/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.EquationalTheory.X25519

/-!
# X25519 Variant Typeclass

Defines the `CanX25519Variant` typeclass and its `DY.Bytes` instance for encoding non-canonical
X25519 public-key variations.
-/

@[expose] public section

namespace DY.X25519

class CanX25519Variant (Bytes: Type u) where
  x25519Variant: (key: Bytes) → (variation: Fin 4) → Bytes

export CanX25519Variant (x25519Variant)

instance [BytesFunctor] [BytesFunctor.Has SubF] : CanX25519Variant Bytes where
  x25519Variant key v :=
    if v = 0 then normalizeX25519Key key else ({key := normalizeX25519Key key, variation := v}: Variant.SubF Bytes).pack

end DY.X25519
