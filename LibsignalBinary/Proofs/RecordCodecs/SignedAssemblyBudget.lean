/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedAssembly
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD
public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKeyBudget
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Fetches
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.FetchesBudget
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode
public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecodeBudget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Signed and Kyber Pre-Key Record Decoder Assembly

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` assembly for
`decode_kyber_pre_key` and `decode_signed_pre_key` (Block `595`) from `SignedHooksPlaced` and
`SignedPortDepsPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace LibsignalBinary.Proofs.RecordCodecs.SignedAssemblyBudget

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs
open ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open LibsignalBinary.Heap
open CryptoVerification.RecordCodecsBinary.SignedAssembly (signedPreKeyResultAt_deserialize)
open LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKeyBudget (decodeKyberPreKey_placed_ok_of_decode)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (SignedHooksPlaced SignedPortDepsPlaced decodeKyberPreKeyPlacedSpec decodeKyberPreKeyRawSpec decodeSignedPreKeyPlacedSpec decodeSignedPreKeyRawSpec)
open LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecodeBudget (signedDecode_placed_ok_of_deps)
attribute [local irreducible] Program.fetch Program.externAt?

/-- The image-free signed and Kyber binding specs are the same spec. -/
theorem decodeSignedPreKeyRawSpec_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    decodeSignedPreKeyRawSpec A lim = decodeKyberPreKeyRawSpec A lim := by
  simp only [decodeSignedPreKeyRawSpec, decodeKyberPreKeyRawSpec, signedPreKeyResultAt_deserialize]

/-- The relocatable `[CryptoVerification.LibsignalPlacement]` signed and Kyber binding specs are the same spec. -/
theorem decodeSignedPreKeyPlacedSpec_eq [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    decodeSignedPreKeyPlacedSpec A lim = decodeKyberPreKeyPlacedSpec A lim := by
  simp only [decodeSignedPreKeyPlacedSpec, decodeKyberPreKeyPlacedSpec,
    decodeSignedPreKeyRawSpec_eq]

/-- `decode_kyber_pre_key` (block `595`) under `[CryptoVerification.LibsignalPlacement]` meets
`decodeKyberPreKeyPlacedSpec A lim` from `SignedHooksPlaced` and `SignedPortDepsPlaced`. -/
theorem decodeKyberPreKey_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_595 H) (blkPl_595).base (decodeKyberPreKeyPlacedSpec A lim) :=
  decodeKyberPreKey_placed_ok_of_decode
    (signedDecode_placed_ok_of_deps hH d) d.dropDecodeError3

/-- `decode_kyber_pre_key` as `decode_signed_pre_key` (block `595`, LLVM keeps one function
for both) under `[CryptoVerification.LibsignalPlacement]` meets `decodeSignedPreKeyPlacedSpec A lim` from
`SignedHooksPlaced` and `SignedPortDepsPlaced`. -/
theorem decodeSignedPreKey_placed_ok [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : SignedHooksPlaced M A lim H) (d : SignedPortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_595 H) (blkPl_595).base (decodeSignedPreKeyPlacedSpec A lim) := by
  rw [decodeSignedPreKeyPlacedSpec_eq]
  exact decodeKyberPreKey_placed_ok hH d

end LibsignalBinary.Proofs.RecordCodecs.SignedAssemblyBudget
