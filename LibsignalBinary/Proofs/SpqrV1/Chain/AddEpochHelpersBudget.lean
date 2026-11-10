/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.ChainPbCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget

/-!
# Budget-Threaded Specifications for `<spqr::chain::Chain>::add_epoch` (Block `368`)

Defines the allocator event envelope `ChainAddEpochEnv` and cost-model-parametric specifications
`chainAddEpochSpecX`, `chainAddEpochSpecExt`, and `ChainAddEpochPlacedOkX` for Block `368`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsmpl blkPC_368 blkPl_368)
open CryptoVerification.LibsignalSpqrV1 (Chain EpochSecret HkdfFn)
open CryptoVerification.SpqrV1.ChainProofs
  (chainAddEpochStackX chainAddEpochStackExt chainAt chainEpochSize chainRepr
   epochSecretAt ChainAddEpochGhost)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   FitsEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (vecDequeGrowEvents)

/-- Exact allocator event sequence of `<spqr::chain::Chain>::add_epoch` on the `.ok` path:
1. `rust_alloc(32, 1)` for `new_root: Vec<u8>`;
2. `rust_dealloc(G.nextRoot.cap, 1)` if `G.nextRoot.cap ≠ 0`;
3. `rust_alloc(72, 1)` + `rust_alloc(32, 1)` for `send` (`prev` cap 72, `next` len 32);
4. `rust_alloc(72, 1)` + `rust_alloc(32, 1)` for `recv` (`prev` cap 72, `next` len 32);
5. `vecDequeGrowEvents G.linksCap` if `self.links.length = G.linksCap.toNat`;
6. `rust_dealloc(esPin.cap, 1)` if `esPin.cap ≠ 0`. -/
def chainAddEpochEvents (x : ChainAddEpochGhost) : List AllocEvent :=
  rustAllocEvents 32 1 ++
    (if x.G.nextRoot.cap = 0#64 then [] else rustDeallocEvents x.G.nextRoot.cap.toNat 1) ++
    rustAllocEvents 72 1 ++
    rustAllocEvents 32 1 ++
    rustAllocEvents 72 1 ++
    rustAllocEvents 32 1 ++
    (if x.self.links.length = x.G.linksCap.toNat then vecDequeGrowEvents x.G.linksCap else []) ++
    (if x.esPin.cap = 0#64 then [] else rustDeallocEvents x.esPin.cap.toNat 1)

/-- Relational allocator event envelope of `<spqr::chain::Chain>::add_epoch`. -/
def ChainAddEpochEnv (hkdf : HkdfFn) (x : ChainAddEpochGhost) (evs : List AllocEvent) : Prop :=
  match Chain.addEpoch hkdf x.self x.epochSecret with
  | .error _ => evs = []
  | .ok _ => evs = chainAddEpochEvents x

/-- Budget-threaded spec of `<spqr::chain::Chain>::add_epoch` at `chainAddEpochStackX`. -/
def chainAddEpochSpecX [LibsignalPlacement] (hkdf : HkdfFn) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (ChainAddEpochGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.esPtr ∧
      (x.self.links.length < x.G.linksCap.toNat ∨
        max (2 * x.G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63) ∧
      FitsEnv M lim st (ChainAddEpochEnv hkdf x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      chainAt A.repAlloc x.selfPtr x.G x.self ∗
      epochSecretAt A.repAlloc x.esPtr x.esPin x.epochSecret ∗
      A.pool lim st s ∗ stackAt s.sp chainAddEpochStackX
  post := fun (x, st) s0 sf =>
    match Chain.addEpoch hkdf x.self x.epochSecret with
    | .error _ => ⌜False⌝
    | .ok c' =>
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
        chainRepr A.repAlloc x.selfPtr c' ∗
        memRegion x.esPtr 32 ∗
        A.pool lim (M.stepEvents (chainAddEpochEvents x) st) sf ∗
        stackAt s0.sp chainAddEpochStackX
  onPanic := fun (x, _) s0 sf =>
    ⌜(Chain.addEpoch hkdf x.self x.epochSecret).isOk = false ∧ sf.trace = s0.trace⌝ ∗ anyHeap

/-- Budget-threaded spec of `<spqr::chain::Chain>::add_epoch` at `chainAddEpochStackExt` (`17808` B). -/
def chainAddEpochSpecExt [LibsignalPlacement] (hkdf : HkdfFn) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (ChainAddEpochGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.selfPtr ∧ s.readReg64 .x1 = x.esPtr ∧
      (x.self.links.length < x.G.linksCap.toNat ∨
        max (2 * x.G.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63) ∧
      FitsEnv M lim st (ChainAddEpochEnv hkdf x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      chainAt A.repAlloc x.selfPtr x.G x.self ∗
      epochSecretAt A.repAlloc x.esPtr x.esPin x.epochSecret ∗
      A.pool lim st s ∗ stackAt s.sp chainAddEpochStackExt
  post := fun (x, st) s0 sf =>
    match Chain.addEpoch hkdf x.self x.epochSecret with
    | .error _ => ⌜False⌝
    | .ok c' =>
      ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
        chainRepr A.repAlloc x.selfPtr c' ∗
        memRegion x.esPtr 32 ∗
        A.pool lim (M.stepEvents (chainAddEpochEvents x) st) sf ∗
        stackAt s0.sp chainAddEpochStackExt
  onPanic := fun (x, _) s0 sf =>
    ⌜(Chain.addEpoch hkdf x.self x.epochSecret).isOk = false ∧ sf.trace = s0.trace⌝ ∗ anyHeap

def ChainAddEpochPlacedOkX [LibsignalPlacement] (hkdf : HkdfFn)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
    (blkPl_368).base
    (withLsCallInv lsmpl (chainAddEpochSpecX hkdf M A lim))

end LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
