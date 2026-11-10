/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpers

/-!
# Budget-Threaded Specifications for `<spqr::chain::Chain>::send_key` (Block `367`)

Defines the front-epoch pop deallocation schedule (`chainEpochPopEvents`, `chainSendKeyPopEvents`),
allocator event envelopes (`ChainSendKeyEnv`, `ChainSendKeyAllocEnv`), and budget-threaded
specifications (`chainSendKeySpecX`, `chainSendKeySpecExt`, `ChainSendKeyPlacedOkX`) for Block `367`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsmpl blkPC_367 blkPl_367)
open CryptoVerification.LibsignalSpqrV1 (Chain HkdfFn)
open CryptoVerification.SpqrV1.ChainProofs
  (chainAt chainSendKeyStackX chainSendKeyStackExt sendKeyPostAt ChainEpochGhost ChainSendKeyGhost)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   FitsEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (nextKeyInternalEvents)

/-- Exact deallocation events emitted when `Chain::send_key` pops a single front `ChainEpoch`
(`send.next`, `send.prev`, `recv.next`, `recv.prev` in order). -/
def chainEpochPopEvents (gce : ChainEpochGhost) : List AllocEvent :=
  (if gce.send.next.cap = 0#64 then [] else rustDeallocEvents gce.send.next.cap.toNat 1) ++
    (if gce.send.prev.cap = 0#64 then [] else rustDeallocEvents gce.send.prev.cap.toNat 1) ++
    (if gce.recv.next.cap = 0#64 then [] else rustDeallocEvents gce.recv.next.cap.toNat 1) ++
    (if gce.recv.prev.cap = 0#64 then [] else rustDeallocEvents gce.recv.prev.cap.toNat 1)

/-- Exact deallocation events emitted by `Chain::send_key`'s front-epoch pop loop prior to
`next_key_internal`: pops `i - 1` front epochs when `self.sendEpoch < epoch` and
`self.epochIdx epoch = .ok i`. -/
def chainSendKeyPopEvents (x : ChainSendKeyGhost) : List AllocEvent :=
  if x.epoch ≤ x.self.sendEpoch then
    []
  else
    match x.self.epochIdx x.epoch with
    | .error _ => []
    | .ok i => (x.G.epochs.take (i - 1)).flatMap chainEpochPopEvents

/-- Exact allocator events of `<spqr::chain::Chain>::send_key` on the `.ok` path:
front-epoch deallocations followed by `next_key_internal` and `rust_alloc(32, 1)` for the returned
32-byte message key. -/
def chainSendKeyEvents (x : ChainSendKeyGhost) : List AllocEvent :=
  chainSendKeyPopEvents x ++ nextKeyInternalEvents ++ rustAllocEvents 32 1

/-- Relational allocator event envelope of `<spqr::chain::Chain>::send_key`:
* `.ok _`: `chainSendKeyEvents x`;
* `.error (.err _)`: `[]` (no heap calls);
* `.error (.panic _)`: `chainSendKeyPopEvents x` (deallocations only, no `rust_alloc`). -/
def ChainSendKeyEnv (hkdf : HkdfFn) (x : ChainSendKeyGhost) (evs : List AllocEvent) : Prop :=
  match Chain.sendKey hkdf x.self x.epoch with
  | .ok _ => evs = chainSendKeyEvents x
  | .error (.err _) => evs = []
  | .error (.panic _) => evs = chainSendKeyPopEvents x

/-- Precondition allocation envelope of `<spqr::chain::Chain>::send_key` (only the `.ok` path
allocates; `.error` paths only deallocate or return immediately). -/
def ChainSendKeyAllocEnv (hkdf : HkdfFn) (x : ChainSendKeyGhost) (evs : List AllocEvent) : Prop :=
  match Chain.sendKey hkdf x.self x.epoch with
  | .ok _ => evs = chainSendKeyEvents x
  | .error _ => evs = []

/-- Budget-threaded spec of `<spqr::chain::Chain>::send_key` at `chainSendKeyStackX`. -/
def chainSendKeySpecX (hkdf : HkdfFn) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainSendKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.epoch ∧ s.readReg64 .x8 = x.out ∧
      FitsEnv M lim st (ChainSendKeyAllocEnv hkdf x)⌝ ∗
      memRegion x.out 40 ∗
      chainAt A.repAlloc x.selfPtr x.G x.self ∗
      A.pool lim st s ∗ stackAt s.sp chainSendKeyStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ChainSendKeyAllocEnv hkdf x evs ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      sendKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.sendKey hkdf x.self x.epoch) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainSendKeyStackX
  onPanic := fun (x, _) s0 sf =>
    ⌜(Chain.sendKey hkdf x.self x.epoch).isPanic = true ∧ sf.trace = s0.trace⌝ ∗ anyHeap

/-- Budget-threaded spec of `<spqr::chain::Chain>::send_key` at `chainSendKeyStackExt` (`18000` B). -/
def chainSendKeySpecExt (hkdf : HkdfFn) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainSendKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.epoch ∧ s.readReg64 .x8 = x.out ∧
      FitsEnv M lim st (ChainSendKeyAllocEnv hkdf x)⌝ ∗
      memRegion x.out 40 ∗
      chainAt A.repAlloc x.selfPtr x.G x.self ∗
      A.pool lim st s ∗ stackAt s.sp chainSendKeyStackExt
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ChainSendKeyAllocEnv hkdf x evs ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      sendKeyPostAt A.repAlloc x.selfPtr x.out x.self (Chain.sendKey hkdf x.self x.epoch) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainSendKeyStackExt
  onPanic := fun (x, _) s0 sf =>
    ⌜(Chain.sendKey hkdf x.self x.epoch).isPanic = true ∧ sf.trace = s0.trace⌝ ∗ anyHeap

def ChainSendKeyPlacedOkX [LibsignalPlacement] (hkdf : HkdfFn)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
    (blkPl_367).base
    (withLsCallInv lsmpl (chainSendKeySpecX hkdf M A lim))

end LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget
