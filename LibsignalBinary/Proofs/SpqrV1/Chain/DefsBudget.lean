/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs

/-!
# Budget-Threaded Specifications for SPQR V1 Chain

Deterministic `AllocEvent` envelopes and `RustCliAllocBudget`-threaded specifications for
`Concat<u8>::concat [local#2]`, `<VecDeque<ChainEpoch>>::grow`,
`<ChainEpochDirection>::next_key_internal`, and `<spqr::chain::Chain>::new`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget

open Arm64 ProofLib
open CryptoVerification.LibsignalSpqrV1 (HkdfFn chainNextInfo)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainGhost ChainNewGhost NextKeyInternalGhost SliceConcat2Ghost VecDequeGrowGhost
  bytesAt chainAt chainEpochAlign chainEpochAt chainEpochSize chainNewStackExt chainNewStackX
  chainNewVal newCapChainEpoch nextKeyInternalStackExt nextKeyInternalStackX
  nextKeyNext nextKeyOut nextKeyOutAt vecDequeAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustAllocEvents rustDeallocEvents rustReallocEvents
)

/-! ## `Concat<u8>::concat [local#2]` -/

/-- Deterministic `AllocEvent` list emitted by `Concat<u8>::concat [local#2]` on total length `n`. -/
def sliceConcat2Events (n : Nat) : List AllocEvent :=
  if n = 0 then [] else rustAllocEvents n 1

def SliceConcat2Env (x : SliceConcat2Ghost) (evs : List AllocEvent) : Prop :=
  evs = sliceConcat2Events (x.bs0.length + x.bs1.length)

/-- Budget-threaded spec of `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]` for `len = 2`. -/
def sliceConcat2Spec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SliceConcat2Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length + x.bs1.length < 2 ^ 63 ∧
      FitsEnv M lim st (SliceConcat2Env x)⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ SliceConcat2Env x evs⌝ ∗
      (∃∗ ptr : BitVec 64,
        vecU8At A.repAlloc x.outVec (BitVec.ofNat 64 (x.bs0.length + x.bs1.length))
          ptr (x.bs0 ++ x.bs1)) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      bytesAt x.ro0 x.p0 x.bs0 ∗ bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-! ## `<VecDeque<ChainEpoch>>::grow` -/

/-- Deterministic `AllocEvent` list emitted by `<VecDeque<ChainEpoch>>::grow` from capacity `cap`. -/
def vecDequeGrowEvents (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then
    rustAllocEvents (4 * chainEpochSize) chainEpochAlign
  else
    rustReallocEvents (cap.toNat * chainEpochSize)
      (max (2 * cap.toNat) 4 * chainEpochSize) chainEpochAlign

def VecDequeGrowEnv (x : VecDequeGrowGhost) (evs : List AllocEvent) : Prop :=
  evs = vecDequeGrowEvents x.cap

/-- Budget-threaded spec of `<alloc::collections::vec_deque::VecDeque<spqr::chain::ChainEpoch>>::grow`. -/
def vecDequeGrowSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (VecDequeGrowGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.xs.length = x.cap.toNat ∧
      max (2 * x.cap.toNat) 4 * chainEpochSize < 2 ^ 63 ∧
      FitsEnv M lim st (VecDequeGrowEnv x)⌝ ∗
      vecDequeAt A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc)
        x.v x.cap x.ptr x.head x.xs ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ VecDequeGrowEnv x evs⌝ ∗
      (∃∗ (ptr' : BitVec 64), ∃∗ (head' : BitVec 64),
        ⌜x.head = 0#64 → head' = 0#64⌝ ∗
        vecDequeAt A.repAlloc chainEpochSize chainEpochAlign (chainEpochAt A.repAlloc)
          x.v (newCapChainEpoch x.cap) ptr' head' x.xs) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-! ## `<spqr::chain::ChainEpochDirection>::next_key_internal` -/

/-- Deterministic `AllocEvent` list emitted by `<ChainEpochDirection>::next_key_internal`. -/
def nextKeyInternalEvents : List AllocEvent :=
  rustAllocEvents (4 + chainNextInfo.length) 1 ++
    rustDeallocEvents (4 + chainNextInfo.length) 1

def NextKeyInternalEnv (evs : List AllocEvent) : Prop :=
  evs = nextKeyInternalEvents

/-- Budget-threaded spec of `<spqr::chain::ChainEpochDirection>::next_key_internal` at
`nextKeyInternalStackX`. -/
def nextKeyInternalSpecX (hkdf : HkdfFn) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (NextKeyInternalGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.nextA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = x.ctrA ∧
      x.next.length = 32 ∧ x.ctr ≠ 0xffffffff#32 ∧
      FitsEnv M lim st NextKeyInternalEnv⌝ ∗
      memRegion x.out 36 ∗ (x.nextA ↦ₛ x.next) ∗ (x.ctrA ↦₃₂ x.ctr) ∗
      A.pool lim st s ∗ stackAt s.sp nextKeyInternalStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ NextKeyInternalEnv evs⌝ ∗
      nextKeyOutAt x.out (x.ctr + 1#32) (nextKeyOut hkdf x.next x.ctr) ∗
      (x.nextA ↦ₛ nextKeyNext hkdf x.next x.ctr) ∗
      (x.ctrA ↦₃₂ (x.ctr + 1#32)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp nextKeyInternalStackX

/-- Contract-backed budget-threaded spec of `<spqr::chain::ChainEpochDirection>::next_key_internal`
at `nextKeyInternalStackExt`. -/
def nextKeyInternalSpecExt (hkdf : HkdfFn) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (NextKeyInternalGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.nextA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = x.ctrA ∧
      x.next.length = 32 ∧ x.ctr ≠ 0xffffffff#32 ∧
      FitsEnv M lim st NextKeyInternalEnv⌝ ∗
      memRegion x.out 36 ∗ (x.nextA ↦ₛ x.next) ∗ (x.ctrA ↦₃₂ x.ctr) ∗
      A.pool lim st s ∗ stackAt s.sp nextKeyInternalStackExt
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ NextKeyInternalEnv evs⌝ ∗
      nextKeyOutAt x.out (x.ctr + 1#32) (nextKeyOut hkdf x.next x.ctr) ∗
      (x.nextA ↦ₛ nextKeyNext hkdf x.next x.ctr) ∗
      (x.ctrA ↦₃₂ (x.ctr + 1#32)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp nextKeyInternalStackExt

/-! ## `<spqr::chain::Chain>::new` -/

/-- Deterministic `AllocEvent` list emitted by `<spqr::chain::Chain>::new`. -/
def chainNewEvents : List AllocEvent :=
  rustAllocEvents 72 1 ++ rustAllocEvents 32 1 ++
    rustAllocEvents 72 1 ++ rustAllocEvents 32 1 ++
    rustAllocEvents (4 * chainEpochSize) chainEpochAlign ++
    rustAllocEvents 32 1

def ChainNewEnv (evs : List AllocEvent) : Prop :=
  evs = chainNewEvents

/-- Budget-threaded spec of `<spqr::chain::Chain>::new` at `chainNewStackX`. -/
def chainNewSpecX (hkdf : HkdfFn) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainNewGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.ikmA ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.initialKey.length ∧
      (s.readReg64 .x3).setWidth 32 = x.dir.toI32 ∧
      (s.readReg64 .x4).setWidth 32 = x.params.maxJump ∧
      (s.readReg64 .x5).setWidth 32 = x.params.maxOooKeys ∧
      x.initialKey.length < 2 ^ 63 ∧
      FitsEnv M lim st ChainNewEnv⌝ ∗
      memRegion x.out 88 ∗ bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool lim st s ∗ stackAt s.sp chainNewStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ ChainNewEnv evs⌝ ∗
      (∃∗ G : ChainGhost,
        ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗
        chainAt A.repAlloc x.out G (chainNewVal hkdf x.initialKey x.dir x.params)) ∗
      bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainNewStackX

/-- Contract-backed budget-threaded spec of `<spqr::chain::Chain>::new` at `chainNewStackExt`. -/
def chainNewSpecExt (hkdf : HkdfFn) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainNewGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.ikmA ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.initialKey.length ∧
      (s.readReg64 .x3).setWidth 32 = x.dir.toI32 ∧
      (s.readReg64 .x4).setWidth 32 = x.params.maxJump ∧
      (s.readReg64 .x5).setWidth 32 = x.params.maxOooKeys ∧
      x.initialKey.length < 2 ^ 63 ∧
      (¬x.ikmRO ∨ x.initialKey.length < 64) ∧
      FitsEnv M lim st ChainNewEnv⌝ ∗
      memRegion x.out 88 ∗ bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool lim st s ∗ stackAt s.sp chainNewStackExt
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ ChainNewEnv evs⌝ ∗
      (∃∗ G : ChainGhost,
        ⌜G.linksCap = 4#64 ∧ G.linksHead = 0#64⌝ ∗
        chainAt A.repAlloc x.out G (chainNewVal hkdf x.initialKey x.dir x.params)) ∗
      bytesAt x.ikmRO x.ikmA x.initialKey ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainNewStackExt

end LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
