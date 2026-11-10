/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.ChainPbCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpers
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget

/-!
# Budget-Threaded Specifications for `<spqr::chain::Chain>::into_pb` (Block `365`)

Defines the allocator event envelopes (`ChainIntoPbAllocEnv`, `ChainIntoPbEnv`) and
cost-model-parametric specifications (`chainIntoPbPinnedSpec`, `chainIntoPbSpec`,
`chainIntoPbPinnedSpecX`, `chainIntoPbSpecX`) for `<spqr::chain::Chain>::into_pb` (Block `365`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_365 blkPl_365)
open CryptoVerification.SpqrV1.Top.ChainFrom (chainPBAt)
open CryptoVerification.SpqrV1.ChainProofs
  (chainAt chainIntoPbStack chainIntoPbStackX toChainEpochPBGhost ChainIntoPbCall)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   FitsEnv FreeOnlyEvs rustAllocEvents)

/-- Precondition allocation envelope of `<spqr::chain::Chain>::into_pb`:
`[]` when `x.chain.links = []`, or `rustAllocEvents (x.chain.links.length * 112) 8` when
`x.chain.links ≠ []` (executed before any deallocation). -/
def ChainIntoPbAllocEnv (x : ChainIntoPbCall) (evs : List AllocEvent) : Prop :=
  if x.chain.links = [] then
    evs = []
  else
    evs = rustAllocEvents (x.chain.links.length * 112) 8

/-- Full postcondition event envelope of `<spqr::chain::Chain>::into_pb`:
`FreeOnlyEvs` when `x.chain.links = []`, or the initial `links` buffer allocation followed by
`FreeOnlyEvs` deallocations when `x.chain.links ≠ []`. -/
def ChainIntoPbEnv (x : ChainIntoPbCall) (evs : List AllocEvent) : Prop :=
  if x.chain.links = [] then
    FreeOnlyEvs evs
  else
    ∃ evs_free, FreeOnlyEvs evs_free ∧
      evs = rustAllocEvents (x.chain.links.length * 112) 8 ++ evs_free

theorem chainIntoPbAllocEnv_imp_chainIntoPbEnv {x : ChainIntoPbCall} {evs : List AllocEvent}
    (h : ChainIntoPbAllocEnv x evs) :
    ChainIntoPbEnv x evs := by
  unfold ChainIntoPbAllocEnv ChainIntoPbEnv at *
  split at h <;> simp_all only [↓reduceIte]
  · exact FreeOnlyEvs.nil
  · exact ⟨[], FreeOnlyEvs.nil, by simp⟩

theorem fitsEnv_chainIntoPbAllocEnv_of_chainIntoPbEnv {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {x : ChainIntoPbCall}
    (h : FitsEnv M lim st (ChainIntoPbEnv x)) :
    FitsEnv M lim st (ChainIntoPbAllocEnv x) :=
  FitsEnv.mono (fun _ => chainIntoPbAllocEnv_imp_chainIntoPbEnv) h

/-- Budget-threaded pinned spec of `<spqr::chain::Chain>::into_pb` at `chainIntoPbStack`
(`onPanic = ⌜False⌝`). -/
def chainIntoPbPinnedSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainIntoPbCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.chainPtr ∧
      FitsEnv M lim st (ChainIntoPbAllocEnv x)⌝ ∗
      memRegion x.out 80 ∗ chainAt A.repAlloc x.chainPtr x.gChain x.chain ∗
      A.pool lim st s ∗ stackAt s.sp chainIntoPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ChainIntoPbEnv x evs ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      (∃∗ linksPtr : BitVec 64,
        chainPBAt A.repAlloc
          ⟨BitVec.ofNat 64 x.chain.links.length, linksPtr,
            x.gChain.epochs.map toChainEpochPBGhost, x.gChain.nextRoot⟩
          x.out x.chain.intoPb) ∗
      memRegion x.chainPtr 88 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainIntoPbStack

/-- Budget-threaded unpinned `ProtoRepr.chainPBAt` spec of `<spqr::chain::Chain>::into_pb`
at `chainIntoPbStack` (`onPanic = ⌜False⌝`). -/
def chainIntoPbSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainIntoPbCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.chainPtr ∧
      FitsEnv M lim st (ChainIntoPbAllocEnv x)⌝ ∗
      memRegion x.out 80 ∗ chainAt A.repAlloc x.chainPtr x.gChain x.chain ∗
      A.pool lim st s ∗ stackAt s.sp chainIntoPbStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ChainIntoPbEnv x evs ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A.repAlloc x.out x.chain.intoPb ∗
      memRegion x.chainPtr 88 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainIntoPbStack

/-- Budget-threaded pinned spec of `<spqr::chain::Chain>::into_pb` at `chainIntoPbStackX`
(`onPanic = ⌜False⌝`). -/
def chainIntoPbPinnedSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainIntoPbCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.chainPtr ∧
      FitsEnv M lim st (ChainIntoPbAllocEnv x)⌝ ∗
      memRegion x.out 80 ∗ chainAt A.repAlloc x.chainPtr x.gChain x.chain ∗
      A.pool lim st s ∗ stackAt s.sp chainIntoPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ChainIntoPbEnv x evs ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      (∃∗ linksPtr : BitVec 64,
        chainPBAt A.repAlloc
          ⟨BitVec.ofNat 64 x.chain.links.length, linksPtr,
            x.gChain.epochs.map toChainEpochPBGhost, x.gChain.nextRoot⟩
          x.out x.chain.intoPb) ∗
      memRegion x.chainPtr 88 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainIntoPbStackX

/-- Budget-threaded unpinned `ProtoRepr.chainPBAt` spec of `<spqr::chain::Chain>::into_pb`
at `chainIntoPbStackX` (`onPanic = ⌜False⌝`). -/
def chainIntoPbSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainIntoPbCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.chainPtr ∧
      FitsEnv M lim st (ChainIntoPbAllocEnv x)⌝ ∗
      memRegion x.out 80 ∗ chainAt A.repAlloc x.chainPtr x.gChain x.chain ∗
      A.pool lim st s ∗ stackAt s.sp chainIntoPbStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ChainIntoPbEnv x evs ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A.repAlloc x.out x.chain.intoPb ∗
      memRegion x.chainPtr 88 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainIntoPbStackX

def ChainIntoPbPinnedPlacedOk [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
    (blkPl_365).base
    (chainIntoPbPinnedSpec M A lim)

def ChainIntoPbPlacedOk [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
    (blkPl_365).base
    (chainIntoPbSpec M A lim)

def ChainIntoPbPinnedPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
    (blkPl_365).base
    (chainIntoPbPinnedSpecX M A lim)

def ChainIntoPbPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
    (blkPl_365).base
    (chainIntoPbSpecX M A lim)

end LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
