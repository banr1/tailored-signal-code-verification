/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpers
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WPp -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Helpers and Specifications for `<spqr::chain::Chain>::recv_key` (Block `366`)

Defines the deterministic allocation/reallocation schedule `chainRecvKeyEvents` (`doReserveStep`,
`keyHistoryAddStep`, `keyAdvanceLoopEvents`) and budget-threaded specifications
`chainRecvKeySpecX`, `chainRecvKeySpecExt`, and `ChainRecvKeyPlacedOkX` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalPlacement lsmpl blkPC_366 blkPl_366)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes Chain ChainEpochDirection ChainParamsPB ChainResult Epoch Error HkdfFn KeyHistory
)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainRecvKeyGhost NextKeyInternalGhost RecvPrevFits
  chainAt chainRecvKeyName chainRecvKeyStackExt chainRecvKeyStackX nextKeyInternalStackX
  nextKeyNext nextKeyOut nextKeyOutAt recvKeyPostAt
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (NextKeyInternalEnv nextKeyInternalEvents)

namespace LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget

open Arm64 ProofLib

/-! ## Deterministic Allocation Event Schedule -/

/-- Exact event step of `RawVecInner::reserve::do_reserve_and_handle` (`stride = 1, align = 1`)
for current capacity `cap`, length `len`, and `additional` bytes. -/
def doReserveStep (cap len additional : Nat) : Nat × List AllocEvent :=
  if len + additional ≤ cap then
    (cap, [])
  else
    let cap' := reserveCap cap len additional
    (cap', if cap = 0 then rustAllocEvents cap' 1 else rustReallocEvents cap cap' 1)

/-- Exact two-step `do_reserve_and_handle` sequence inside `KeyHistory::add`
(`4`-byte counter push followed by `32`-byte key push). -/
def keyHistoryAddStep (cap len : Nat) : Nat × List AllocEvent :=
  let (cap1, ev1) := doReserveStep cap len 4
  let (cap2, ev2) := doReserveStep cap1 (len + 4) 32
  (cap2, ev1 ++ ev2)

/-- Exact allocation/reallocation events emitted across `ChainEpochDirection.keyAdvanceLoop`
starting from `(ced, cap)` with `rem` remaining loop steps (`atIdx.toNat - ced.ctr.toNat ≤ rem`). -/
def keyAdvanceLoopEvents (hkdf : HkdfFn) (params : ChainParamsPB) (atIdx : BitVec 32) :
    Nat → ChainEpochDirection → Nat → List AllocEvent
  | 0, _, _ => []
  | rem + 1, ced, cap =>
    if ced.ctr.toNat + 1 < atIdx.toNat then
      match ChainEpochDirection.nextKeyInternal hkdf ced.next ced.ctr with
      | .error _ => []
      | .ok (next1, ctr1, (_, key)) =>
        let maxOoo := params.maxOooKeysOrDefault
        if ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32 then
          nextKeyInternalEvents
        else if ctr1 + maxOoo ≥ atIdx then
          let (cap', evAdd) := keyHistoryAddStep cap ced.prev.data.length
          let ced' : ChainEpochDirection :=
            { ctr := ctr1, next := next1, prev := ced.prev.add (ctr1, key) params }
          nextKeyInternalEvents ++ evAdd ++ keyAdvanceLoopEvents hkdf params atIdx rem ced' cap'
        else
          let ced' : ChainEpochDirection :=
            { ctr := ctr1, next := next1, prev := ced.prev }
          nextKeyInternalEvents ++ keyAdvanceLoopEvents hkdf params atIdx rem ced' cap
    else
      []

/-- Deterministic allocator event sequence emitted by `<spqr::chain::Chain>::recv_key` on a
non-panicking execution from ghost state `x`. -/
def chainRecvKeyEvents (hkdf : HkdfFn) (x : ChainRecvKeyGhost) : List AllocEvent :=
  if x.epoch == 0#64 && x.index == 0#32 then
    []
  else
    match x.self.epochIdx x.epoch with
    | .error _ => []
    | .ok epochIndex =>
      if h : epochIndex < x.self.links.length then
        let link := x.self.links[epochIndex]'h
        let gCap :=
          if hg : epochIndex < x.G.epochs.length then
            (x.G.epochs[epochIndex]'hg).recv.prev.cap.toNat
          else
            0
        if x.index < link.recv.ctr then
          match link.recv.prev.get x.index link.recv.ctr x.self.params with
          | .ok _ => rustAllocEvents 32 1
          | .error _ => []
        else if x.index == link.recv.ctr then
          []
        else if x.index - link.recv.ctr > x.self.params.maxJumpOrDefault then
          []
        else if link.recv.ctr.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32 then
          []
        else
          let maxOoo := x.self.params.maxOooKeysOrDefault
          let self0 :=
            if x.index > link.recv.ctr + maxOoo then
              { link.recv with prev := link.recv.prev.clear }
            else
              link.recv
          let rem := x.index.toNat - self0.ctr.toNat
          keyAdvanceLoopEvents hkdf x.self.params x.index rem self0 gCap ++
            nextKeyInternalEvents ++ rustAllocEvents 32 1
      else
        []

/-- Envelope predicate for `<spqr::chain::Chain>::recv_key`: non-panicking executions emit
`chainRecvKeyEvents hkdf x`. -/
def ChainRecvKeyEnv (hkdf : HkdfFn) (x : ChainRecvKeyGhost) (evs : List AllocEvent) : Prop :=
  evs = chainRecvKeyEvents hkdf x

/-! ## Budget-Threaded Specifications -/

/-- Budget-threaded specification of `<spqr::chain::Chain>::recv_key` (`chainRecvKeyStackX` stack). -/
def chainRecvKeySpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hkdf : HkdfFn) : Spec (ChainRecvKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.selfPtr ∧
      s.readReg64 .x2 = x.epoch ∧ (s.readReg64 .x3).setWidth 32 = x.index ∧
      RecvPrevFits x.self ∧ FitsEnv M lim st (ChainRecvKeyEnv hkdf x)⌝ ∗
      memRegion x.out 32 ∗
      chainAt A.repAlloc x.selfPtr x.G x.self ∗
      A.pool lim st s ∗ stackAt s.sp chainRecvKeyStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
      A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) sf ∗
      stackAt s0.sp chainRecvKeyStackX
  onPanic := fun (x, _) s0 sf =>
    ⌜(Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true ∧ sf.trace = s0.trace⌝ ∗ anyHeap

def ChainRecvKeyPlacedOkX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hkdf : HkdfFn) (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
    (blkPl_366).base
    (withLsCallInv lsmpl (chainRecvKeySpecX M A lim hkdf))

/-- Budget-threaded specification of `<spqr::chain::Chain>::recv_key` under `CliExternsOk`
(`chainRecvKeyStackExt = 17920` B stack). -/
def chainRecvKeySpecExt (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hkdf : HkdfFn) : Spec (ChainRecvKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.selfPtr ∧
      s.readReg64 .x2 = x.epoch ∧ (s.readReg64 .x3).setWidth 32 = x.index ∧
      RecvPrevFits x.self ∧ FitsEnv M lim st (ChainRecvKeyEnv hkdf x)⌝ ∗
      memRegion x.out 32 ∗
      chainAt A.repAlloc x.selfPtr x.G x.self ∗
      A.pool lim st s ∗ stackAt s.sp chainRecvKeyStackExt
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
      A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) sf ∗
      stackAt s0.sp chainRecvKeyStackExt
  onPanic := fun (x, _) s0 sf =>
    ⌜(Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true ∧ sf.trace = s0.trace⌝ ∗ anyHeap

def nextKeyInternalSpecRecvCore (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hkdf : HkdfFn) (extra : Nat) :
    Spec (NextKeyInternalGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.nextA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = x.ctrA ∧
      x.next.length = 32 ∧ x.ctr ≠ 0xffffffff#32 ∧
      FitsEnv M lim st NextKeyInternalEnv⌝ ∗
      memRegion x.out 36 ∗ (x.nextA ↦ₛ x.next) ∗ (x.ctrA ↦₃₂ x.ctr) ∗
      A.pool lim st s ∗ memRegion (s.sp - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra ∗
      stackAt s.sp nextKeyInternalStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ NextKeyInternalEnv evs⌝ ∗
      nextKeyOutAt x.out (x.ctr + 1#32) (nextKeyOut hkdf x.next x.ctr) ∗
      (x.nextA ↦ₛ nextKeyNext hkdf x.next x.ctr) ∗ (x.ctrA ↦₃₂ (x.ctr + 1#32)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      memRegion (s0.sp - BitVec.ofNat 64 (extra + nextKeyInternalStackX)) extra ∗
      stackAt s0.sp nextKeyInternalStackX
  onPanic := fun _ _ _ => ⌜False⌝

def chainRecvKeySpecCore (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hkdf : HkdfFn) (extra : Nat) : Spec (ChainRecvKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.selfPtr ∧
      s.readReg64 .x2 = x.epoch ∧ (s.readReg64 .x3).setWidth 32 = x.index ∧
      RecvPrevFits x.self ∧ FitsEnv M lim st (ChainRecvKeyEnv hkdf x)⌝ ∗
      memRegion x.out 32 ∗
      chainAt A.repAlloc x.selfPtr x.G x.self ∗
      A.pool lim st s ∗
      memRegion (s.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra ∗
      stackAt s.sp chainRecvKeyStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      recvKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
      A.pool lim (M.stepEvents (chainRecvKeyEvents hkdf x) st) sf ∗
      memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra ∗
      stackAt s0.sp chainRecvKeyStackX
  onPanic := fun (x, _) s0 sf =>
    ⌜(Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true ∧ sf.trace = s0.trace⌝ ∗ anyHeap

abbrev recvKeyPostCore (extra : Nat) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hkdf : HkdfFn) (x : ChainRecvKeyGhost) (st : M.σ) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P' ⊢ (chainRecvKeySpecCore M A lim hkdf extra).post (x, st) s0 sf)

theorem recvKey_frame_extra {extra : Nat} {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hkdf : HkdfFn}
    {x : ChainRecvKeyGhost} {st : M.σ} {s0 s : State} {P0 P : SepProp} {R : SepProp}
    (hpre : P ⊢ P0 ∗ memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
    (h : ∀ {R0 : SepProp}, SepWPp prog (s0.readReg64 (.gpr 30#5)) s P0
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P' ⊢ (chainRecvKeySpecX M A lim hkdf).post (x, st) s0 sf))
      (fun sf P' => (sf.mem ⊨ P' ∗ R0) →
        (sf.mem ⊨ (chainRecvKeySpecX M A lim hkdf).onPanic (x, st) s0 sf ∗ R0))) :
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s P
      (recvKeyPostCore extra M A lim hkdf x st s0)
      (fun sf P' => (sf.mem ⊨ P' ∗ R) →
        (sf.mem ⊨ (chainRecvKeySpecX M A lim hkdf).onPanic (x, st) s0 sf ∗ R)) :=
  CryptoVerification.SpqrV1.ChainProofs.SepWPp.frame_entails_anyHeap hpre
    (fun _ => by
      dsimp only [chainRecvKeySpecX, chainRecvKeySpecCore]
      exact Entails.of_eq (by sep_ac_rfl))
    h

end LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget
