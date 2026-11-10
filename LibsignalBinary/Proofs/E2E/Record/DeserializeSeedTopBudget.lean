/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeedTop
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget

/-!
# Budget-Threaded Top-Level Specification of Seed `SessionRecord::deserialize`

Defines the `RustCliAllocBudget M` specification `deserializeSeedPlacedSpec` (block `46`),
input-length allocation envelope `DeserializeSeedEnv`, and external hook bundle
`PlacedDeserializeHooks` for `SessionRecord::deserialize` on `seedRecord f`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.DeserializeSeedTopBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (
  LibsignalPlacement lsmpl
  lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym lsRustDeallocSym lsMemcpySym
  lsHandleErrorSym
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.E2E.Record (
  encodeRecord SeedOk seedRecord recDeserializeStack DeserializeSeedGhost lsDeserHandleAllocErrorSym
)
open CryptoVerification.E2E.Record.Placed (blkPl_46 lsProg_46)
open CryptoVerification.E2E.Record.Serialization (CanonRecord)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
  rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)

/-- Input-length-bounded allocation envelope for `SessionRecord::deserialize` on seed bytes `bs`. -/
def DeserializeSeedEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (8 * bs.length + 64) (256 * (bs.length + 16)) evs

/-- Image-free budget-threaded contract of `SessionRecord::deserialize` on seed bytes `seedRecord f`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv M lim st (DeserializeSeedEnv x.bs)`). -/
noncomputable def deserializeSeedRawSpec (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DeserializeSeedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.bs.length ∧
      s.readReg64 .x8 = x.out ∧ SeedOk x.f ∧ x.bs = seedRecord x.f ∧
      FitsEnv M lim st (DeserializeSeedEnv x.bs)⌝ ∗
      (x.p ↦ₛ x.bs) ∗ memRegion x.out 368 ∗ A.pool lim st s ∗
      stackAt s.sp recDeserializeStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ DeserializeSeedEnv x.bs evs⌝ ∗ (x.p ↦ₛ x.bs) ∗
        (∃∗ g : RecordGhost, ∃∗ r : SessionRecord (List (BitVec 8)),
          ⌜CanonRecord g r ∧ encodeRecord r = x.bs⌝ ∗
          sessionRecordAt A.repAlloc x.out g r) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp recDeserializeStack

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract of `SessionRecord::deserialize`
    (Block `46`) on seed bytes, carrying `LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeSeedPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DeserializeSeedGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (deserializeSeedRawSpec M A lim)

/-- `SessionRecord::deserialize` (Block `46`) satisfies `deserializeSeedPlacedSpec M A lim` on
    `lsProg_46 H`. -/
def DeserializeSeedPlacedOk [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_46 H) (blkPl_46).base (deserializeSeedPlacedSpec M A lim)

/-- Budget-threaded external hook contracts required by `SessionRecord::deserialize` and its
    `prost` / `RawVec` callees on hook map `H`. -/
structure PlacedDeserializeHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (H : String → Option (State → State)) : Prop where
  shim : H lsRustNoAllocShimSym = some hookNoop
  alloc : ∀ lim : BudgetLimits, HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  realloc : ∀ lim : BudgetLimits, HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)
  dealloc : ∀ lim : BudgetLimits, HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec
  panic_alloc : H lsDeserHandleAllocErrorSym = some Rust.panicked
  panic_raw : H lsHandleErrorSym = some Rust.panicked

end LibsignalBinary.Proofs.E2E.Record.DeserializeSeedTopBudget
