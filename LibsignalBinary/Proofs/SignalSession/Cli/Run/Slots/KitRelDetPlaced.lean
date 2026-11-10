/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
public import LibsignalBinary.Proofs.SessionRecordMin.Deserialize
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `SessionRecord::deserialize` Contracts at `scopeKit`

Proves `sessDeserializeSpecPlaced` for Block `46` (`SessionRecord::deserialize`) at `scopeKit` (and
any `Scope ⊆ scopeKit`) under `[LibsignalPlacement]`, with cross-block transfer to any caller block
`i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-- Block `46` (`SessionRecord::deserialize`) satisfies `sessDeserializeSpecPlaced scopeKit E2E.HooksE.A0` under `Stage2ContractsMinPlaced H`. -/
theorem sessDeserialize_scopeKit_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (sessDeserializeSpecPlaced scopeKit E2E.HooksE.A0) := by
  have hQ := Symbolic.Swarm.TRREF.B3DeserQ.deserializeBodyQ_placed_ok_of_stage2Min hStage2
  refine subroutine_ok_mono hQ (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  simpa only [sessDeserializeSpecPlaced, Symbolic.Swarm.TRREF.B3DeserQ.deserializeQPlacedSpecW,
    Symbolic.Swarm.TRREF.B3DeserQ.deserializeQRawSpecW,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded,
    LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded,
    LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded,
    LibsignalTripleRatchet.LibsignalCodeRoLoaded,
    scopeKit, sepConj_assoc] using hpre

theorem sessDeserialize_of_sub_scopeKit_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced H)
    (hsub : ∀ r, Scope r → scopeKit r) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (sessDeserializeSpecPlaced Scope E2E.HooksE.A0) := by
  refine subroutine_ok_mono (sessDeserialize_scopeKit_placed_ok hStage2)
    (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  have ⟨hrocl, hrest⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [sessDeserializeSpecPlaced] at hrest
  rw [sepConj_assoc, satisfies_pure_sepConj] at hrest
  obtain ⟨⟨hx0, hx1, hx8, hsc⟩, hmem⟩ := hrest
  dsimp only [sessDeserializeSpecPlaced, LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hrocl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx8, hsub x.r hsc⟩, hmem⟩

/-- Transfers `sessDeserialize_of_sub_scopeKit_placed_ok` to any caller block `i < 619`. -/
theorem sessDeserialize_of_sub_scopeKit_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced H)
    (hsub : ∀ r, Scope r → scopeKit r)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_46).base
      (sessDeserializeSpecPlaced Scope E2E.HooksE.A0) := by
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_46 H) i 46 H
    hcaller (instIsLsBlockProg_46 H) (blkPl_46).base _
    (sessDeserialize_of_sub_scopeKit_placed_ok hStage2 hsub) _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

end CryptoVerification.SignalSession.Cli.Slots
