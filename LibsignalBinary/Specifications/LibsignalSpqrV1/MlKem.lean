/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs

/-!
# SPQR V1: libcrux ML-KEM-768 incremental API (`MlKem`)

**Trusted: definitions used by the statement.**

Models the incremental ML-KEM-768 entry points of `libcrux_ml_kem::mlkem768::incremental` (called
via extern stubs in `Hooks.lean`) as a record `MlKem` of uninterpreted functions (`keyPair`,
`encaps1`, `encaps2`, `decaps`, `validPk`), with slice projections `MlKem.fromSeed` (`pk1Off`,
`pk2Off`) and length-checked public-key validation `MlKem.validPkBytes`. No correctness or security
property is built into `MlKem`; correctness enters only as explicit hypotheses in
`MlKemCorrect.lean` and `KemFailFind.lean`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

abbrev Bytes := List (BitVec 8)

/-- Byte offset of `pk1` (`hdr`, 64 bytes) inside 2400-byte `KeyPairCompressedBytes` (`2304..2368`). -/
abbrev pk1Off : Nat := 2304

/-- Byte offset of `pk2` (`ek`, 1152 bytes) inside 2400-byte `KeyPairCompressedBytes` (`1152..2304`). -/
abbrev pk2Off : Nat := 1152

/-- Uninterpreted incremental ML-KEM-768 interface (`spqr/src/incremental_mlkem768.rs:28–171`):
* `keyPair`: 2400-byte compressed keypair from a 64-byte seed (`from_seed`);
* `encaps1`: first encapsulation step `(hdr, rand) ↦ Option (ct1, es, ss)` (`none` on `Err`);
* `encaps2`: second encapsulation step `(es, ek) ↦ ct2`;
* `decaps`: compressed-key decapsulation `(dk, ct1, ct2) ↦ ss`;
* `validPk`: encapsulation-key check on 64-byte `hdr` and 1152-byte `ek`. -/
structure MlKem where
  keyPair : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 2400
  encaps1 : Bytes → List.Vector (BitVec 8) 32 →
    Option (List.Vector (BitVec 8) 960 × List.Vector (BitVec 8) 2080 × List.Vector (BitVec 8) 32)
  encaps2 : List.Vector (BitVec 8) 2080 → List.Vector (BitVec 8) 1152 → List.Vector (BitVec 8) 128
  decaps : List.Vector (BitVec 8) 2400 → List.Vector (BitVec 8) 960 → List.Vector (BitVec 8) 128 →
    List.Vector (BitVec 8) 32
  validPk : Bytes → Bytes → Bool

/-- Splits `kp = K.keyPair seed` into `(hdr, ek, dk)` at `pk1Off` (`2304..2368`) and `pk2Off`
(`1152..2304`), with `dk = kp`. -/
@[irreducible] def MlKem.fromSeed (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 1152 × List.Vector (BitVec 8) 2400 :=
  (⟨((K.keyPair seed).toList.drop pk1Off).take 64, by simp [pk1Off]⟩,
   ⟨((K.keyPair seed).toList.drop pk2Off).take 1152, by simp [pk2Off]⟩,
   K.keyPair seed)

theorem MlKem.fromSeed_dk (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    (K.fromSeed seed).2.2 = K.keyPair seed := by with_unfolding_all rfl

theorem MlKem.fromSeed_hdr (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    (K.fromSeed seed).1.toList = ((K.keyPair seed).toList.drop pk1Off).take 64 := by
  with_unfolding_all rfl

theorem MlKem.fromSeed_ek (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    (K.fromSeed seed).2.1.toList = ((K.keyPair seed).toList.drop pk2Off).take 1152 := by
  with_unfolding_all rfl

theorem MlKem.fromSeed_pk1 (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList := by
  with_unfolding_all rfl

theorem MlKem.fromSeed_pk2 (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList := by
  with_unfolding_all rfl

/-- Full `validate_pk_bytes(hdr, ek).is_ok()` check: `hdr.length == 64 && ek.length == 1152` followed
by `K.validPk hdr ek`. -/
def MlKem.validPkBytes (K : MlKem) (hdr ek : Bytes) : Bool :=
  hdr.length == 64 && ek.length == 1152 && K.validPk hdr ek

end CryptoVerification.LibsignalSpqrV1
