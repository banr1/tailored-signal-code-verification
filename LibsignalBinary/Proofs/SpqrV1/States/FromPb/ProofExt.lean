/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Proof
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bExt

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for Variant 0

Lifts `states_from_pb_keysUnsampled_ok_ext` from `AllocContracts` to `AllocContracts4K` inside
`CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace Ext4K

/-- Variant 0 (`InnerState.keysUnsampled`) of `<States>::from_pb` under `AllocContracts4K`:
    combines `states_from_pb_prologue`, `states_from_pb_dispatch_tagged .keysUnsampled`, and
    `Ext4K.states_from_pb_keysUnsampled_156` (from `Variant1bExt.lean`). -/
theorem states_from_pb_keysUnsampled_ok_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s : V1State.Chunked.KeysUnsampled) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName)
      (statesFromPbVariantSpec A F b { innerState := some (.keysUnsampled s) }) := by
  refine sfpProof_tagged_ok_of_step TaggedVariantDispatch.keysUnsampled
    (Tail := fun pbA => protoChunkedKeysUnsampledAt A (pbA + 8#64) s ∗ memRegion (pbA + 64#64) 160)
    (fun _ => rfl) ?_
  intro _ s0 s1 out pbA R hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1
  exact Ext4K.states_from_pb_keysUnsampled_156 hA s0 s1 out pbA s R
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
