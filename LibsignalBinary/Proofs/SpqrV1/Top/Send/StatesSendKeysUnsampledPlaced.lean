/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced

/-!
# Relocatable Callee Contracts for Inlined `.keysUnsampled` Arm (Block 124)

Defines `AuthMacHdrPinnedPlacedOkX` (Block 342) and `DoReserve2PlacedOkX` (Block 157)
along with `withLsCodeRoLoaded` lifting lemmas on `spqrSendPlacedProg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

/-- Lift `subroutine_ok prog entry spec` to `subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)`. -/
theorem subroutine_ok_withLsCodeRoLoaded {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  change s0.mem ⊨ (spec.pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R at hpre
  rw [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hal fun _ hout => hout

/-- Lift `subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)` to
    `subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)`. -/
theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  change s0.mem ⊨ (spec.pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R at hpre
  rw [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s0 ∗ R := by
    change s0.mem ⊨ (spec.pre x s0 ∗ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) ∗ R
    rw [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.1, hpre.2⟩
  exact h.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout

/-- `<spqr::authenticator::Authenticator>::mac_hdr` (Block `342`) meets
`withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F A)` on `spqrSendPlacedProg ext`. -/
def AuthMacHdrPinnedPlacedOkX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
    (withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F A))

/-- `alloc::raw_vec::RawVecInner<A>::do_reserve_and_handle [local#2]` (Block `157`) meets
`withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec A)` on `spqrSendPlacedProg ext`. -/
def DoReserve2PlacedOkX (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 157)
    (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec A))

theorem doReserve2_placed_ok_ext_x {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsPlaced A ext) :
    DoReserve2PlacedOkX A ext := by
  have hraw : subroutine_ok ((blkPC_157).rebase (blkPl_157).base (Rust.withPanics ext))
      (lsmpl.base 157) (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec A)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (do_reserve_2_raw32_placed_ok (A := A) (H := Rust.withPanics ext)
        hA.handle_error hA.shim hA.alloc hA.realloc)
  exact SpqrV1.ls_subroutine_ok_of_blockProgram_cro
    (SpqrV1.ls_subroutine_ok_to_blockProgram hraw)

end CryptoVerification.SpqrV1.Top.Send
