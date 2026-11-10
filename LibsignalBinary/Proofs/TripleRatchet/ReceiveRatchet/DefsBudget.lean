/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs

/-!
# Budget-Threaded `TripleRatchet::apply_to_session_state` Specifications

Bounded allocator-event envelopes (`TrApplySenderAllocEnv`, `TrApplyEnv`), `RustCliAllocBudget`-threaded
specifications (`trApplySpec`, `trApplySpecX`), and `PhaseCreditSpec` / `FitsEnv` witnesses for
`<TripleRatchet>::apply_to_session_state`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
   SeqEnv FreeOnlyEvs rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineStepReserveOfCum)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open CryptoVerification.LibsignalTripleRatchet (TrApplyGhost)

/-- Deterministic allocation sequence of the `senderChain.isSome` arm of
    `<TripleRatchet>::apply_to_session_state`:
    `senderRatchetKey.public` (`33` B), `senderRatchetKey.private` (`33` B),
    `senderChainKey` (`32` B), and two temporary `32` B key clones, all at `align = 1`. -/
def TrApplySenderAllocEnv : List AllocEvent → Prop :=
  SeqEnv (fun evs => evs = rustAllocEvents 33 1)
    (SeqEnv (fun evs => evs = rustAllocEvents 33 1)
      (SeqEnv (fun evs => evs = rustAllocEvents 32 1)
        (SeqEnv (fun evs => evs = rustAllocEvents 32 1)
          (fun evs => evs = rustAllocEvents 32 1))))

/-- Bounded allocation-event envelope of `<TripleRatchet>::apply_to_session_state`:
    1. `rootKey` clone (`rustAllocEvents 32 1`);
    2. Old `rootKey` / receiver-chain drops (`FreeOnlyEvs`);
    3. Optional `senderChain` allocations (`evs = [] ∨ TrApplySenderAllocEnv evs`);
    4. Epilogue drops (`FreeOnlyEvs`). -/
def TrApplyEnv : List AllocEvent → Prop :=
  SeqEnv (fun evs => evs = rustAllocEvents 32 1)
    (SeqEnv FreeOnlyEvs
      (SeqEnv (fun evs => evs = [] ∨ TrApplySenderAllocEnv evs) FreeOnlyEvs))

/-- Budget-threaded specification of `<TripleRatchet>::apply_to_session_state`
    at `trApplyStack` (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def trApplySpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (TrApplyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st TrApplyEnv⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.trApplySpec
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜TrApplyEnv evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.trApplySpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Budget-threaded specification of `<TripleRatchet>::apply_to_session_state`
    at `trApplyStackX` (`onOom = ⌜False⌝`, `onPanic = ⌜False⌝`). -/
def trApplySpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (TrApplyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st TrApplyEnv⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.trApplySpecX
        (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜TrApplyEnv evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.trApplySpecX
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Non-empty 6-allocation witness trace (`senderChain.isSome` arm) belongs to `TrApplyEnv`. -/
theorem trApplyEnv_senderSome_mem :
    TrApplyEnv
      (rustAllocEvents 32 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 33 1 ++
            (rustAllocEvents 32 1 ++
              (rustAllocEvents 32 1 ++ rustAllocEvents 32 1))))) := by
  have hsnd : TrApplySenderAllocEnv
      (rustAllocEvents 33 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 32 1 ++
            (rustAllocEvents 32 1 ++ rustAllocEvents 32 1)))) :=
    SeqEnv.append rfl (SeqEnv.append rfl (SeqEnv.append rfl (SeqEnv.append rfl rfl)))
  have hmid : SeqEnv (fun evs => evs = [] ∨ TrApplySenderAllocEnv evs) FreeOnlyEvs
      (rustAllocEvents 33 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 32 1 ++
            (rustAllocEvents 32 1 ++ rustAllocEvents 32 1)))) := by
    simpa using SeqEnv.append (Or.inr hsnd) FreeOnlyEvs.nil
  have hfree : SeqEnv FreeOnlyEvs
      (SeqEnv (fun evs => evs = [] ∨ TrApplySenderAllocEnv evs) FreeOnlyEvs)
      (rustAllocEvents 33 1 ++
        (rustAllocEvents 33 1 ++
          (rustAllocEvents 32 1 ++
            (rustAllocEvents 32 1 ++ rustAllocEvents 32 1)))) := by
    simpa using SeqEnv.append FreeOnlyEvs.nil hmid
  exact SeqEnv.append rfl hfree

/-- Parametric `PhaseCreditSpec` for `TrApplyEnv` under `ModelHyps M`. -/
theorem trApplyEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M TrApplyEnv 57622 49364 49364 33 := by
  have h32 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
  have h33 := PhaseCreditSpec.rustAlloc_aff hM (req := 33) (al := 1) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  have hsnd : PhaseCreditSpec M TrApplySenderAllocEnv 48019 41137 41137 33 :=
    (h33.seq (h33.seq (h32.seq (h32.seq h32)))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hopt : PhaseCreditSpec M (fun evs => evs = [] ∨ TrApplySenderAllocEnv evs)
      48019 41137 41137 33 :=
    ((PhaseCreditSpec.nil M).or hsnd).congr_mono (fun _ h => h)
      (by decide) (by decide) (by decide) (by decide)
  exact (h32.seq (hfr.seq (hopt.seq hfr))).mono
    (by decide) (by decide) (by decide) (by decide)

/-- Non-vacuity witness: `TrApplyEnv` satisfies `FitsEnv fineCostModel` from `fineCostModel.init`
under an explicit 1 GiB RAM budget (`enforced = true`). -/
theorem trApplyEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init TrApplyEnv := by
  refine fitsEnv_fineCostModel_of_phaseCredit
    (trApplyEnv_phaseCreditSpec fineCostModel_modelHyps)
    (by decide) rfl ?_ ?_
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    decide
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

end LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
