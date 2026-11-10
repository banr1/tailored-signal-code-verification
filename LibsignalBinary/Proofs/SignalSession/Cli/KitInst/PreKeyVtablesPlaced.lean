/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Pre-Key Store Vtables

Relocatable `[LibsignalPlacement]` `CliFutVtPlacedOk` and trait-object slot lemmas for
`SignedPreKeyFiles`, `OneTimePreKeyFiles`, and `KyberPreKeyFiles`.
-/

@[expose] public section
set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

set_option maxRecDepth 200000

/-- A `dyn Future` vtable at `vt` under `LibsignalRoLoaded lsmpl`: drop ↦ `dropAddr`, size `boxSize`,
align `8`, poll ↦ `pollAddr`. -/
structure CliFutVtPlacedOk [LibsignalPlacement] (vt dropAddr : BitVec 64) (boxSize : Nat)
    (pollAddr : BitVec 64) : Prop where
  drop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ (vt ↦₆₄ᵣ dropAddr) ∗ P
  size : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((vt + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 boxSize) ∗ P
  align : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((vt + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  poll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((vt + 0x18#64) ↦₆₄ᵣ pollAddr) ∗ P

/-- `.data.rel.ro` symbol for `<OneTimePreKeyFiles as PreKeyStore>`. -/
abbrev cliPkVtRoSym : String := "libsignal_cli:.rodata..Lanon.36"
/-- `.data.rel.ro` symbol for `<SignedPreKeyFiles as SignedPreKeyStore>`. -/
abbrev cliSpkVtRoSym : String := "libsignal_cli:.rodata..Lanon.37"
/-- `.data.rel.ro` symbol for `<KyberPreKeyFiles as KyberPreKeyStore>`. -/
abbrev cliKpkVtRoSym : String := "libsignal_cli:.rodata..Lanon.38"

private noncomputable abbrev pkVtChecksBool : Bool :=
  (fastLookupBlockSym spkGetShimName == some (606, 0)) &&
  (fastLookupBlockSym spkGetPollName == some (571, 0)) &&
  (fastLookupBlockSym pkGetShimName == some (608, 0)) &&
  (fastLookupBlockSym pkGetPollName == some (573, 0)) &&
  (fastLookupBlockSym pkRemoveShimName == some (610, 0)) &&
  (fastLookupBlockSym pkRemovePollName == some (575, 0)) &&
  (fastLookupBlockSym kpkGetShimName == some (611, 0)) &&
  (fastLookupBlockSym kpkGetPollName == some (576, 0)) &&
  (fastLookupBlockSym kpkMarkShimName == some (613, 0)) &&
  (fastLookupBlockSym kpkMarkPollName == some (578, 0)) &&
  lsroReloc64Check spkGetFutVtSym 0 cliIdFutDropName &&
  lsroSliceCheck spkGetFutVtSym 8 (unpack64 16#64) &&
  lsroSliceCheck spkGetFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check spkGetFutVtSym 24 spkGetPollName &&
  lsroReloc64Check pkGetFutVtSym 0 cliIdFutDropName &&
  lsroSliceCheck pkGetFutVtSym 8 (unpack64 16#64) &&
  lsroSliceCheck pkGetFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check pkGetFutVtSym 24 pkGetPollName &&
  lsroReloc64Check pkRemoveFutVtSym 0 cliIdFutDropName &&
  lsroSliceCheck pkRemoveFutVtSym 8 (unpack64 16#64) &&
  lsroSliceCheck pkRemoveFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check pkRemoveFutVtSym 24 pkRemovePollName &&
  lsroReloc64Check kpkGetFutVtSym 0 cliIdFutDropName &&
  lsroSliceCheck kpkGetFutVtSym 8 (unpack64 16#64) &&
  lsroSliceCheck kpkGetFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check kpkGetFutVtSym 24 kpkGetPollName &&
  lsroReloc64Check kpkMarkFutVtSym 0 cliIdFutDropName &&
  lsroSliceCheck kpkMarkFutVtSym 8 (unpack64 32#64) &&
  lsroSliceCheck kpkMarkFutVtSym 16 (unpack64 8#64) &&
  lsroReloc64Check kpkMarkFutVtSym 24 kpkMarkPollName &&
  lsroReloc64Check cliSpkVtRoSym 24 spkGetShimName &&
  lsroReloc64Check cliPkVtRoSym 24 pkGetShimName &&
  lsroReloc64Check cliPkVtRoSym 40 pkRemoveShimName &&
  lsroReloc64Check cliKpkVtRoSym 24 kpkGetShimName &&
  lsroReloc64Check cliKpkVtRoSym 40 kpkMarkShimName &&
  (fastLookupBlockSym cliIdFutDropName == some (547, 0))

private theorem pkVtChecksBool_eq : pkVtChecksBool = true := by
  decide +kernel

private theorem pkVt_kernel_checks :
    fastLookupBlockSym spkGetShimName = some (606, 0) ∧
    fastLookupBlockSym spkGetPollName = some (571, 0) ∧
    fastLookupBlockSym pkGetShimName = some (608, 0) ∧
    fastLookupBlockSym pkGetPollName = some (573, 0) ∧
    fastLookupBlockSym pkRemoveShimName = some (610, 0) ∧
    fastLookupBlockSym pkRemovePollName = some (575, 0) ∧
    fastLookupBlockSym kpkGetShimName = some (611, 0) ∧
    fastLookupBlockSym kpkGetPollName = some (576, 0) ∧
    fastLookupBlockSym kpkMarkShimName = some (613, 0) ∧
    fastLookupBlockSym kpkMarkPollName = some (578, 0) ∧
    lsroReloc64Check spkGetFutVtSym 0 cliIdFutDropName = true ∧
    lsroSliceCheck spkGetFutVtSym 8 (unpack64 16#64) = true ∧
    lsroSliceCheck spkGetFutVtSym 16 (unpack64 8#64) = true ∧
    lsroReloc64Check spkGetFutVtSym 24 spkGetPollName = true ∧
    lsroReloc64Check pkGetFutVtSym 0 cliIdFutDropName = true ∧
    lsroSliceCheck pkGetFutVtSym 8 (unpack64 16#64) = true ∧
    lsroSliceCheck pkGetFutVtSym 16 (unpack64 8#64) = true ∧
    lsroReloc64Check pkGetFutVtSym 24 pkGetPollName = true ∧
    lsroReloc64Check pkRemoveFutVtSym 0 cliIdFutDropName = true ∧
    lsroSliceCheck pkRemoveFutVtSym 8 (unpack64 16#64) = true ∧
    lsroSliceCheck pkRemoveFutVtSym 16 (unpack64 8#64) = true ∧
    lsroReloc64Check pkRemoveFutVtSym 24 pkRemovePollName = true ∧
    lsroReloc64Check kpkGetFutVtSym 0 cliIdFutDropName = true ∧
    lsroSliceCheck kpkGetFutVtSym 8 (unpack64 16#64) = true ∧
    lsroSliceCheck kpkGetFutVtSym 16 (unpack64 8#64) = true ∧
    lsroReloc64Check kpkGetFutVtSym 24 kpkGetPollName = true ∧
    lsroReloc64Check kpkMarkFutVtSym 0 cliIdFutDropName = true ∧
    lsroSliceCheck kpkMarkFutVtSym 8 (unpack64 32#64) = true ∧
    lsroSliceCheck kpkMarkFutVtSym 16 (unpack64 8#64) = true ∧
    lsroReloc64Check kpkMarkFutVtSym 24 kpkMarkPollName = true ∧
    lsroReloc64Check cliSpkVtRoSym 24 spkGetShimName = true ∧
    lsroReloc64Check cliPkVtRoSym 24 pkGetShimName = true ∧
    lsroReloc64Check cliPkVtRoSym 40 pkRemoveShimName = true ∧
    lsroReloc64Check cliKpkVtRoSym 24 kpkGetShimName = true ∧
    lsroReloc64Check cliKpkVtRoSym 40 kpkMarkShimName = true ∧
    fastLookupBlockSym cliIdFutDropName = some (547, 0) := by
  have h := pkVtChecksBool_eq
  simpa only [pkVtChecksBool, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

private theorem futDrop_resolve_547' [LibsignalPlacement] :
    lsmpl.base 547 = libsignalSessionLib.resolve lsmpl cliIdFutDropName :=
  (ls_resolve_text
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).symm

theorem cliSpkGetFutVt_placed_ok [LibsignalPlacement] :
    CliFutVtPlacedOk (lsρ spkGetFutVtSym) (lsmpl.base 547) 16 (lsmpl.base 571) where
  drop hro hP := lsro_reloc64_intro hro (BitVec.add_zero _).symm
    futDrop_resolve_547' pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.1 hP
  size hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.1 hP
  align hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  poll hro hP := lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.1).symm pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

theorem cliPkGetFutVt_placed_ok [LibsignalPlacement] :
    CliFutVtPlacedOk (lsρ pkGetFutVtSym) (lsmpl.base 547) 16 (lsmpl.base 573) where
  drop hro hP := lsro_reloc64_intro hro (BitVec.add_zero _).symm
    futDrop_resolve_547' pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  size hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  align hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  poll hro hP := lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.2.2.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

theorem cliPkRemoveFutVt_placed_ok [LibsignalPlacement] :
    CliFutVtPlacedOk (lsρ pkRemoveFutVtSym) (lsmpl.base 547) 16 (lsmpl.base 575) where
  drop hro hP := lsro_reloc64_intro hro (BitVec.add_zero _).symm
    futDrop_resolve_547' pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  size hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  align hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  poll hro hP := lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.2.2.2.2.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

theorem cliKpkGetFutVt_placed_ok [LibsignalPlacement] :
    CliFutVtPlacedOk (lsρ kpkGetFutVtSym) (lsmpl.base 547) 16 (lsmpl.base 576) where
  drop hro hP := lsro_reloc64_intro hro (BitVec.add_zero _).symm
    futDrop_resolve_547'
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  size hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  align hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  poll hro hP := lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.2.2.2.2.2.2.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

theorem cliKpkMarkFutVt_placed_ok [LibsignalPlacement] :
    CliFutVtPlacedOk (lsρ kpkMarkFutVtSym) (lsmpl.base 547) 32 (lsmpl.base 578) where
  drop hro hP := lsro_reloc64_intro hro (BitVec.add_zero _).symm
    futDrop_resolve_547'
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  size hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  align hro hP := lsro64_intro hro rfl
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP
  poll hro hP := lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

/-- `dyn SignedPreKeyStore` slot `+0x18` relocates to `get_signed_pre_key` (`lsmpl.base 606`). -/
theorem cliSpkGetSlot_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliSpkVtRoSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 606) ∗ P) :=
  lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

/-- `dyn PreKeyStore` slot `+0x18` relocates to `get_pre_key` (`lsmpl.base 608`). -/
theorem cliPkGetSlot_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliPkVtRoSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 608) ∗ P) :=
  lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.2.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

/-- `dyn PreKeyStore` slot `+0x28` relocates to `remove_pre_key` (`lsmpl.base 610`). -/
theorem cliPkRemoveSlot_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliPkVtRoSym + 0x28#64) ↦₆₄ᵣ lsmpl.base 610) ∗ P) :=
  lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.2.2.2.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

/-- `dyn KyberPreKeyStore` slot `+0x18` relocates to `get_kyber_pre_key` (`lsmpl.base 611`). -/
theorem cliKpkGetSlot_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliKpkVtRoSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 611) ∗ P) :=
  lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.2.2.2.2.2.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

/-- `dyn KyberPreKeyStore` slot `+0x28` relocates to `mark_kyber_pre_key_used` (`lsmpl.base 613`). -/
theorem cliKpkMarkSlot_placed_ok [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliKpkVtRoSym + 0x28#64) ↦₆₄ᵣ lsmpl.base 613) ∗ P) :=
  lsro_reloc64_intro hro rfl
    (ls_resolve_text pkVt_kernel_checks.2.2.2.2.2.2.2.2.1).symm
    pkVt_kernel_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP

end CryptoVerification.SignalSession.Cli.KitInst
