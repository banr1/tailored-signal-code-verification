/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget

/-!
# Budget-Threaded `E2E.HooksE` Shared Contracts

`VmPreserved`-carrying and `RustCliAllocBudget M` counterparts of the external hook contracts in
`E2E.HooksE.Common`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.HooksE.CommonBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SystemTime)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.E2E (rustAllocName bcmpName randomKeysName stringCloneName allocErrName)
open CryptoVerification.E2E.HooksE (BcmpCall)
open LibsignalBinary.Heap
  (VmPreserved AllocCostModel BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (withVmPreserved TripleRatchetHooksBudget timeAddBudgetSpec durationSinceBudgetSpec)
open LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget
  (rustAllocNWSpec hookOk_rustAllocSpec_of_NW hookSat_rustAllocSpec_of_NW)

export LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.DefsBudget
  (rustAllocNWSpec rustAllocNoOomNWSpec hookOk_rustAllocSpec_of_NW hookSat_rustAllocSpec_of_NW)

/-- `bcmp(a = x0, b = x1, n = x2) -> w0` contract with `sf.vregs = s0.vregs` and `VmPreserved`. -/
def bcmpVregsSpec : Spec BcmpCall :=
  withVmPreserved CryptoVerification.E2E.HooksE.bcmpVregsSpec

/-- `bcmp(a = x0, b = x1, n = x2) -> w0` contract without `vregs` preservation, with `VmPreserved`. -/
def e2eBcmpSpec : Spec BcmpCall :=
  withVmPreserved CryptoVerification.E2E.HooksE.e2eBcmpSpec

theorem hookOk_bcmpSpec_of_vregs {h : State → State}
    (hok : HookOk h bcmpVregsSpec) : HookOk h e2eBcmpSpec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hst, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hst, ?_⟩
  rcases hout with ⟨hret, habi, hpost⟩ | hrest
  · refine Or.inl ⟨hret, habi, ?_⟩
    dsimp only [bcmpVregsSpec, e2eBcmpSpec, withVmPreserved,
      CryptoVerification.E2E.HooksE.bcmpVregsSpec,
      CryptoVerification.E2E.HooksE.e2eBcmpSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, ⟨hpost.2.1.1, hpost.2.1.2.2⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- `hashmap_random_keys` contract with `VmPreserved` (`0` allocations). -/
def randomKeysSpec : Spec Unit :=
  withVmPreserved CryptoVerification.E2E.HooksE.randomKeysSpec

/-- `hashmap_random_keys` contract preserving `tpidrEl0`, wrapped with `VmPreserved`. -/
def randomKeysTpidrSpec : Spec Unit :=
  withVmPreserved CryptoVerification.E2E.HooksE.randomKeysTpidrSpec

theorem hookOk_randomKeysSpec_of_tpidr {h : State → State}
    (hok : HookOk h randomKeysTpidrSpec) : HookOk h randomKeysSpec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hst, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hst, ?_⟩
  rcases hout with ⟨hret, habi, hpost⟩ | hrest
  · refine Or.inl ⟨hret, habi, ?_⟩
    dsimp only [randomKeysTpidrSpec, randomKeysSpec, withVmPreserved,
      CryptoVerification.E2E.StoreNew.randomKeysTpidrSpec,
      CryptoVerification.E2E.StoreNew.randomKeysSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1.1, hpost.2.2⟩
  · exact Or.inr hrest

abbrev stringCloneSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :=
  stringCloneBudgetSpec M A lim

abbrev timeAddSpec : Spec (SystemTime × Nat) :=
  timeAddBudgetSpec

abbrev durationSinceSpec : Spec (BitVec 64 × BitVec 64) :=
  durationSinceBudgetSpec

/-- Budget-threaded abstract hook bundle for `HashbrownBin`. -/
structure HashbrownBinAbsHooks [LibsignalPlacement] (C : Crypto) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop where
  tripleRatchet : TripleRatchetHooksBudget C M A lim S abs
  allocNW : HookSat abs rustAllocName (rustAllocNWSpec M A lim)
  bcmp : HookSat abs bcmpName bcmpVregsSpec
  randomKeys : HookSat abs randomKeysName randomKeysSpec
  stringClone : HookSat abs stringCloneName (stringCloneSpec M A lim)
  fallibilityAllocErr : abs allocErrName = some Rust.panicked

end LibsignalBinary.Proofs.E2E.HooksE.CommonBudget
