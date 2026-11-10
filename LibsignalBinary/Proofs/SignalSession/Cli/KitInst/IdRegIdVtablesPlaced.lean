/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdRegIdVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `IdentityFiles::get_local_registration_id` Vtable Slots

Relocatable `[LibsignalPlacement]` vtable slot lemmas for
`<IdentityFiles as IdentityKeyStore>::get_local_registration_id` and its boxed `Future`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad
open CryptoVerification
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

set_option maxRecDepth 200000

private abbrev idRegIdVtRoSym : String := "libsignal_cli:.rodata..Lanon.35"

private noncomputable abbrev idRegIdVtChecksBool : Bool :=
  (fastLookupBlockSym idRegIdShimName == some (603, 0)) &&
  lsroReloc64Check idRegIdVtRoSym 32 idRegIdShimName

private theorem idRegIdVtChecksBool_eq : idRegIdVtChecksBool = true := by
  decide +kernel

private theorem idRegIdVt_kernel_checks :
    fastLookupBlockSym idRegIdShimName = some (603, 0) ∧
    lsroReloc64Check idRegIdVtRoSym 32 idRegIdShimName = true := by
  have h := idRegIdVtChecksBool_eq
  simpa only [idRegIdVtChecksBool, Bool.and_eq_true, beq_iff_eq] using h

/-- Trait vtable slot `lsρ "signal_session:.rodata..Lanon.35" + 0x20#64` relocates to
`get_local_registration_id` (`lsmpl.base 603`). -/
theorem cliIdRegIdSlot_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ "libsignal_cli:.rodata..Lanon.35" + 0x20#64) ↦₆₄ᵣ lsmpl.base 603) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text idRegIdVt_kernel_checks.1).symm idRegIdVt_kernel_checks.2 hP

/-- Future vtable slot `lsρ idRegIdFutVtSym + 0x00` relocates to `lsmpl.base 547` (`cliIdFutDropName`). -/
theorem cliIdRegIdFutDrop_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsρ idRegIdFutVtSym ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  rodata_idRegIdFut_drop_placed hro hP

/-- Future vtable slot `lsρ idRegIdFutVtSym + 0x08` holds `16#64`. -/
theorem cliIdRegIdFutSize_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idRegIdFutVtSym + 8#64) ↦₆₄ᵣ 16#64) ∗ P) :=
  rodata_idRegIdFut_size_placed hro hP

/-- Future vtable slot `lsρ idRegIdFutVtSym + 0x10` holds `8#64`. -/
theorem cliIdRegIdFutAlign_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idRegIdFutVtSym + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  rodata_idRegIdFut_align_placed hro hP

/-- Future vtable slot `lsρ idRegIdFutVtSym + 0x18` relocates to `lsmpl.base 568` (`idRegIdPollName`). -/
theorem cliIdRegIdFutPoll_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idRegIdFutVtSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 568) ∗ P) :=
  rodata_idRegIdFut_poll_placed hro hP

end CryptoVerification.SignalSession.Cli.KitInst
