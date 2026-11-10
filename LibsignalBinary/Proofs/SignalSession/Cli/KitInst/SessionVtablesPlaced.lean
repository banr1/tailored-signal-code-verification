/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `SessionFiles` Vtables

Relocatable `[LibsignalPlacement]` `SessionOnlyVtablesPlacedOk` proof for CLI `SessionFiles`.
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

/-- `.data.rel.ro` symbol for `<SessionFiles as SessionStore>`. -/
abbrev cliSessionVtRoSym : String := "libsignal_cli:.rodata..Lanon.34"

/-- Placed `SessionStoreSpec` at `0#64` whose session vtable, shim, poll, and drop addresses
and box sizes are the CLI's under `[LibsignalPlacement]`. -/
structure CliSessKitOffsetsPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) : Prop where
  ssVt : kit.ss_vt = lsρ cliSessionVtRoSym
  loadShim : kit.loadShimOff = lsmpl.base 604
  storeShim : kit.storeShimOff = lsmpl.base 605
  loadFutVt : kit.loadFutVtOff = lsρ sessLoadFutVtSym
  storeFutVt : kit.storeFutVtOff = lsρ sessStoreFutVtSym
  loadPoll : kit.loadPollOff = lsmpl.base 569
  storePoll : kit.storePollOff = lsmpl.base 570
  loadFutDrop : kit.loadFutDropOff = lsmpl.base 547
  storeFutDrop : kit.storeFutDropOff = lsmpl.base 547
  loadBoxSize : kit.loadBoxSize = 24
  storeBoxSize : kit.storeBoxSize = 32

private noncomputable abbrev sessVtChecksBool : Bool :=
  (fastLookupBlockSym sessLoadShimName == some (604, 0)) &&
  (fastLookupBlockSym sessStoreShimName == some (605, 0)) &&
  lsroReloc64Check cliSessionVtRoSym 24 sessLoadShimName &&
  lsroReloc64Check cliSessionVtRoSym 32 sessStoreShimName

private theorem sessVtChecksBool_eq : sessVtChecksBool = true := by
  decide +kernel

private theorem sessVt_kernel_checks :
    fastLookupBlockSym sessLoadShimName = some (604, 0) ∧
    fastLookupBlockSym sessStoreShimName = some (605, 0) ∧
    lsroReloc64Check cliSessionVtRoSym 24 sessLoadShimName = true ∧
    lsroReloc64Check cliSessionVtRoSym 32 sessStoreShimName = true := by
  have h := sessVtChecksBool_eq
  simpa only [sessVtChecksBool, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem rodata_cliSession_loadSlot_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliSessionVtRoSym + 0x18#64) ↦₆₄ᵣ lsmpl.base 604) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text sessVt_kernel_checks.1).symm sessVt_kernel_checks.2.2.1 hP

theorem rodata_cliSession_storeSlot_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (((lsρ cliSessionVtRoSym + 0x20#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P) :=
  lsro_reloc64_intro hro (by lsro_addr)
    (ls_resolve_text sessVt_kernel_checks.2.1).symm sessVt_kernel_checks.2.2.2 hP

/-- Every `SessionStoreSpec A 0#64` satisfying `CliSessKitOffsetsPlaced` satisfies
`SessionOnlyVtablesPlacedOk`. -/
theorem cliSessionOnlyVtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} (h : CliSessKitOffsetsPlaced kit) :
    SessionOnlyVtablesPlacedOk kit where
  loadSlot hro hP := by
    rw [h.ssVt, h.loadShim, BitVec.zero_add]
    exact rodata_cliSession_loadSlot_placed hro hP
  storeSlot hro hP := by
    rw [h.ssVt, h.storeShim, BitVec.zero_add]
    exact rodata_cliSession_storeSlot_placed hro hP
  loadFutDrop hro hP := by
    rw [h.loadFutVt, h.loadFutDrop, BitVec.zero_add, BitVec.zero_add]
    exact rodata_sessLoadFut_drop_placed hro hP
  loadFutSize hro hP := by
    rw [h.loadFutVt, h.loadBoxSize, BitVec.zero_add]
    exact rodata_sessLoadFut_size_placed hro hP
  loadFutAlign hro hP := by
    rw [h.loadFutVt, BitVec.zero_add]
    exact rodata_sessLoadFut_align_placed hro hP
  loadFutPoll hro hP := by
    rw [h.loadFutVt, h.loadPoll, BitVec.zero_add, BitVec.zero_add]
    exact rodata_sessLoadFut_poll_placed hro hP
  storeFutDrop hro hP := by
    rw [h.storeFutVt, h.storeFutDrop, BitVec.zero_add, BitVec.zero_add]
    exact rodata_sessStoreFut_drop_placed hro hP
  storeFutSize hro hP := by
    rw [h.storeFutVt, h.storeBoxSize, BitVec.zero_add]
    exact rodata_sessStoreFut_size_placed hro hP
  storeFutAlign hro hP := by
    rw [h.storeFutVt, BitVec.zero_add]
    exact rodata_sessStoreFut_align_placed hro hP
  storeFutPoll hro hP := by
    rw [h.storeFutVt, h.storePoll, BitVec.zero_add, BitVec.zero_add]
    exact rodata_sessStoreFut_poll_placed hro hP

end CryptoVerification.SignalSession.Cli.KitInst
