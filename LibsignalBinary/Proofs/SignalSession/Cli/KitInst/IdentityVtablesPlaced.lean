/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `IdentityFiles` Vtables

Relocatable `[LibsignalPlacement]` `IdentityVtablesPlacedOk` proof for CLI `IdentityFiles`.
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
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs

set_option maxRecDepth 200000

/-- `.data.rel.ro` symbol for `<IdentityFiles as IdentityKeyStore>`. -/
abbrev cliIdentityVtRoSym : String := "libsignal_cli:.rodata..Lanon.35"

/-- Predicate asserting that a placed `IdentityStoreSpec A 0#64` has the CLI `IdentityFiles`
addresses and box sizes. -/
structure CliIdKitOffsetsPlaced [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) : Prop where
  idVt : ikit.id_vt = lsρ cliIdentityVtRoSym
  saveShim : ikit.saveShimOff = lsmpl.base 600
  trustShim : ikit.trustShimOff = lsmpl.base 601
  saveFutVt : ikit.saveFutVtOff = lsρ idSaveFutVtSym
  trustFutVt : ikit.trustFutVtOff = lsρ idTrustFutVtSym
  savePoll : ikit.savePollOff = lsmpl.base 565
  trustPoll : ikit.trustPollOff = lsmpl.base 566
  saveFutDrop : ikit.saveFutDropOff = lsmpl.base 547
  trustFutDrop : ikit.trustFutDropOff = lsmpl.base 547
  saveBoxSize : ikit.saveBoxSize = 32
  trustBoxSize : ikit.trustBoxSize = 32

private noncomputable abbrev idVtChecksBool : Bool :=
  (fastLookupBlockSym idSaveShimName == some (600, 0)) &&
  (fastLookupBlockSym idTrustShimName == some (601, 0)) &&
  (fastLookupBlockSym idKeyPairShimName == some (602, 0)) &&
  (fastLookupBlockSym idRegIdShimName == some (603, 0)) &&
  lsroReloc64Check cliIdentityVtRoSym 40 idSaveShimName &&
  lsroReloc64Check cliIdentityVtRoSym 48 idTrustShimName &&
  lsroReloc64Check cliIdentityVtRoSym 24 idKeyPairShimName &&
  lsroReloc64Check cliIdentityVtRoSym 32 idRegIdShimName

private theorem idVtChecksBool_eq : idVtChecksBool = true := by
  decide +kernel

private theorem idVt_kernel_checks :
    fastLookupBlockSym idSaveShimName = some (600, 0) ∧
    fastLookupBlockSym idTrustShimName = some (601, 0) ∧
    fastLookupBlockSym idKeyPairShimName = some (602, 0) ∧
    fastLookupBlockSym idRegIdShimName = some (603, 0) ∧
    lsroReloc64Check cliIdentityVtRoSym 40 idSaveShimName = true ∧
    lsroReloc64Check cliIdentityVtRoSym 48 idTrustShimName = true ∧
    lsroReloc64Check cliIdentityVtRoSym 24 idKeyPairShimName = true ∧
    lsroReloc64Check cliIdentityVtRoSym 32 idRegIdShimName = true := by
  have h := idVtChecksBool_eq
  simpa only [idVtChecksBool, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem rodata_cliIdentity_saveSlot_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliIdentityVtRoSym + 0x28#64) ↦₆₄ᵣ lsmpl.base 600) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text idVt_kernel_checks.1).symm idVt_kernel_checks.2.2.2.2.1 hP

theorem rodata_cliIdentity_trustSlot_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliIdentityVtRoSym + 0x30#64) ↦₆₄ᵣ lsmpl.base 601) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text idVt_kernel_checks.2.1).symm idVt_kernel_checks.2.2.2.2.2.1 hP

theorem rodata_cliIdentity_kpSlot_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliIdentityVtRoSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 602) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text idVt_kernel_checks.2.2.1).symm idVt_kernel_checks.2.2.2.2.2.2.1 hP

theorem rodata_cliIdentity_regIdSlot_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliIdentityVtRoSym + 0x20#64) ↦₆₄ᵣ lsmpl.base 603) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text idVt_kernel_checks.2.2.2.1).symm idVt_kernel_checks.2.2.2.2.2.2.2 hP

/-- Every `IdentityStoreSpec A 0#64` satisfying `CliIdKitOffsetsPlaced` satisfies
`IdentityVtablesPlacedOk`. -/
theorem cliIdentityVtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} (h : CliIdKitOffsetsPlaced ikit) :
    IdentityVtablesPlacedOk ikit where
  saveSlot hro hP := by
    rw [h.idVt, h.saveShim, BitVec.zero_add]
    exact rodata_cliIdentity_saveSlot_placed hro hP
  trustSlot hro hP := by
    rw [h.idVt, h.trustShim, BitVec.zero_add]
    exact rodata_cliIdentity_trustSlot_placed hro hP
  saveFutDrop hro hP := by
    rw [h.saveFutVt, h.saveFutDrop, BitVec.zero_add, BitVec.zero_add]
    exact rodata_idSaveFut_drop_placed hro hP
  saveFutSize hro hP := by
    rw [h.saveFutVt, h.saveBoxSize, BitVec.zero_add]
    exact rodata_idSaveFut_size_placed hro hP
  saveFutAlign hro hP := by
    rw [h.saveFutVt, BitVec.zero_add]
    exact rodata_idSaveFut_align_placed hro hP
  saveFutPoll hro hP := by
    rw [h.saveFutVt, h.savePoll, BitVec.zero_add, BitVec.zero_add]
    exact rodata_idSaveFut_poll_placed hro hP
  trustFutDrop hro hP := by
    rw [h.trustFutVt, h.trustFutDrop, BitVec.zero_add, BitVec.zero_add]
    exact rodata_idTrustFut_drop_placed hro hP
  trustFutSize hro hP := by
    rw [h.trustFutVt, h.trustBoxSize, BitVec.zero_add]
    exact rodata_idTrustFut_size_placed hro hP
  trustFutAlign hro hP := by
    rw [h.trustFutVt, BitVec.zero_add]
    exact rodata_idTrustFut_align_placed hro hP
  trustFutPoll hro hP := by
    rw [h.trustFutVt, h.trustPoll, BitVec.zero_add, BitVec.zero_add]
    exact rodata_idTrustFut_poll_placed hro hP

end CryptoVerification.SignalSession.Cli.KitInst
