/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBase
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget

/-!
# Budget-threaded `<Chain as Clone>::clone` specifications

Defines the budget-threaded `protoChainCloneSpec` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEnv M lim st (ChainCloneEnv x.gc)`) and `Chain::clone` / `SenderChain::clone` contract
predicates for block `82`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBaseBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E.Record.Placed (blkPl_82 lsProg_82)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalTripleRatchet (trTrapProgAt tripleRatchetProgAt)
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (
  protoChainAt chainCloneLocal1Name
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  chainCloneStack ChainCloneGhost
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv chainCloneSpec senderChainCloneSpec
)

/-! ## Budget-threaded `protoChainCloneSpec` -/

/-- Budget-threaded `protoChainAt` specification of `<Chain as Clone>::clone`, ruling out OOM and
`handle_error` panics under `FitsEnv M lim st (ChainCloneEnv x.gc)`. -/
def protoChainCloneSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (ChainCloneEnv x.gc)⌝ ∗
      memRegion x.dst 104 ∗ protoChainAt A.repAlloc x.gc x.src ∗
      A.pool lim st s ∗ stackAt s.sp chainCloneStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A.repAlloc (g', x.gc.2) x.dst) ∗
      protoChainAt A.repAlloc x.gc x.src ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack

/-! ## Fixed-base contract predicates -/

def ProtoChainCloneLocal1Ok_trap (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr chainCloneLocal1Name)
    (protoChainCloneSpec M A lim)

def ProtoChainCloneLocal1Ok (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name)
    (protoChainCloneSpec M A lim)

def ChainCloneLocal1Ok_trap (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr chainCloneLocal1Name)
    (chainCloneSpec M A lim)

def ChainCloneLocal1Ok (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name)
    (chainCloneSpec M A lim)

def SenderChainCloneLocal1Ok_trap (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr chainCloneLocal1Name)
    (senderChainCloneSpec M A lim)

def SenderChainCloneLocal1Ok (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainCloneLocal1Name)
    (senderChainCloneSpec M A lim)

/-! ## Relocatable `[LibsignalPlacement]` contract predicates (block `82`) -/

section Placed

def ProtoChainCloneLocal1PlacedOk [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base (protoChainCloneSpec M A lim)

def ChainCloneLocal1PlacedOk [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base (chainCloneSpec M A lim)

def SenderChainCloneLocal1PlacedOk [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base (senderChainCloneSpec M A lim)

end Placed

end LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBaseBudget
