/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdKeyPairVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `IdentityFiles::get_identity_key_pair` Vtable Slots

Relocatable `[LibsignalPlacement]` vtable slot lemmas for
`<IdentityFiles as IdentityKeyStore>::get_identity_key_pair` and its boxed `Future`.
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

private abbrev idKpVtRoSym : String := "libsignal_cli:.rodata..Lanon.35"

private noncomputable abbrev idKpVtChecksBool : Bool :=
  (fastLookupBlockSym idKeyPairShimName == some (602, 0)) &&
  lsroReloc64Check idKpVtRoSym 24 idKeyPairShimName

private theorem idKpVtChecksBool_eq : idKpVtChecksBool = true := by
  decide +kernel

private theorem idKpVt_kernel_checks :
    fastLookupBlockSym idKeyPairShimName = some (602, 0) ∧
    lsroReloc64Check idKpVtRoSym 24 idKeyPairShimName = true := by
  have h := idKpVtChecksBool_eq
  simpa only [idKpVtChecksBool, Bool.and_eq_true, beq_iff_eq] using h

/-- Trait vtable slot `lsρ "signal_session:.rodata..Lanon.35" + 0x18#64` relocates to
`get_identity_key_pair` (`lsmpl.base 602`). -/
theorem cliIdKpSlot_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ "libsignal_cli:.rodata..Lanon.35" + 0x18#64) ↦₆₄ᵣ lsmpl.base 602) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text idKpVt_kernel_checks.1).symm idKpVt_kernel_checks.2 hP

/-- Future vtable slot `lsρ idKeyPairFutVtSym + 0x00` relocates to `lsmpl.base 547` (`cliIdFutDropName`). -/
theorem cliIdKpFutDrop_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsρ idKeyPairFutVtSym ↦₆₄ᵣ lsmpl.base 547) ∗ P) :=
  rodata_idKeyPairFut_drop_placed hro hP

/-- Future vtable slot `lsρ idKeyPairFutVtSym + 0x08` holds `16#64`. -/
theorem cliIdKpFutSize_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idKeyPairFutVtSym + 8#64) ↦₆₄ᵣ 16#64) ∗ P) :=
  rodata_idKeyPairFut_size_placed hro hP

/-- Future vtable slot `lsρ idKeyPairFutVtSym + 0x10` holds `8#64`. -/
theorem cliIdKpFutAlign_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idKeyPairFutVtSym + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  rodata_idKeyPairFut_align_placed hro hP

/-- Future vtable slot `lsρ idKeyPairFutVtSym + 0x18` relocates to `lsmpl.base 567` (`idKeyPairPollName`). -/
theorem cliIdKpFutPoll_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ idKeyPairFutVtSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 567) ∗ P) :=
  rodata_idKeyPairFut_poll_placed hro hP

end CryptoVerification.SignalSession.Cli.KitInst
