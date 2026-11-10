/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs

/-!
# Budget-Threaded `OutgoingTripleRatchet` Raw Apply Contract

Defines the allocation envelope `OtrApplyEnv`, the `RustCliAllocBudget` specification
`otrApplyRawSpec`, and its `PhaseCreditSpec` and `FitsEnv` non-vacuity lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FreeOnlyEvs SeqEnv
   rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel FineStepBound)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineStepReserveOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineMaxGroupsOfCum)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open CryptoVerification.LibsignalTripleRatchet (OtrApplyGhost)

/-- Exact binary allocation envelope of
    `<OutgoingTripleRatchet>::apply_to_session_state`:
    one `32`-byte `Vec<u8>` allocation (`ChainKey::to_pb`) followed by optional
    sender-chain / PQ-ratchet buffer deallocations (`FreeOnlyEvs`). -/
def OtrApplyEnv : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs

/-- Budget-threaded image-independent specification of
    `<OutgoingTripleRatchet>::apply_to_session_state` (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def otrApplyRawSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (OtrApplyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st OtrApplyEnv⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜OtrApplyEnv evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrApplyRawSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- `OtrApplyEnv` exercises its `32`-byte `Vec<u8>` allocation (`[.alloc 32]`). -/
theorem otrApplyEnv_alloc_mem : OtrApplyEnv (rustAllocEvents 32 1) :=
  Or.inl rfl

/-- Parametric `PhaseCreditSpec` for `OtrApplyEnv` under `ModelHyps M`. -/
theorem otrApplyEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M OtrApplyEnv 9603 8227 8227 32 := by
  have h32 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  exact (h32.seq hfr).mono (by decide) (by decide) (by decide) (by decide)

/-- Non-vacuity witness: `OtrApplyEnv` satisfies `FitsEnv fineCostModel` from
    `fineCostModel.init` under a `1 GiB` RAM budget (`enforced = true`). -/
theorem otrApplyEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init OtrApplyEnv := by
  refine fitsEnv_fineCostModel_of_phaseCredit
    (otrApplyEnv_phaseCreditSpec fineCostModel_modelHyps)
    (by decide) rfl ?_ ?_
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    decide
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget
