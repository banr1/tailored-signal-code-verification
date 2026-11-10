/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.Helpers

@[expose] public section

set_option autoImplicit false

/-!
# `kem::Key<Public>::deserialize` Subroutine Proof

Lifts the exact-stack proof `KemDeserializeHelpers.cliKemDeserialize_exact_ok` to arbitrary
caller stack `stk ≥ 48 + extHookStack`.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

/-- `kem::Key<Public>::deserialize` satisfies `cliKemDeserializeSpec`. -/
theorem cliKemDeserialize_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliKemDeserializeName)
      ((cliKemDeserializeSpec A stk).inImage img) := by
  refine KemDeserializeHelpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk)
      (stk - KemDeserializeHelpers.cliKemDeserStack))
    (KemDeserializeHelpers.cliKemDeserialize_exact_ok hA hRO) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
  · intro x s0
    dsimp only [Spec.inImage, cliKemDeserializeSpec]
    rw [KemDeserializeHelpers.stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro x s0 sf
    dsimp only [Spec.inImage, cliKemDeserializeSpec]
    rw [KemDeserializeHelpers.stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro _ s0 sf
    dsimp only [Spec.inImage, cliKemDeserializeSpec]
    rw [sepConj_assoc]
    exact sepConj_mono_right (entails_anyHeap _)

end CryptoVerification.SignalSession.Cli.RunProofs
