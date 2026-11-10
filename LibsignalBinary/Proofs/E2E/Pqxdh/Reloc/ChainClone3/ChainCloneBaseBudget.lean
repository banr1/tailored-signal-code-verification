/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBase
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget

/-!
# Budget-Threaded Base Specifications for `Chain::clone [local#3]` (Block `468`)

Defines the `RustCliAllocBudget M` specification `protoChainCloneSpec` under `ChainCloneEnv` and
the `ProtoChainClone3*` / `ChainClone3*` / `SenderChainClone3*` contract predicates on
`trTrapProgAt` and `tripleRatchetProgAt`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBaseBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalTripleRatchet (trTrapProgAt tripleRatchetProgAt)
open CryptoVerification.LibsignalTripleRatchet.ChainClone3 (
  protoChainAt chainClone3Name
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

/-! ## 1. Budget-Threaded `protoChainCloneSpec` -/

/-- Budget-threaded internal `protoChainAt` specification of `<session_structure::Chain as Clone>::clone`
    (`[local#3]`, Block `468`): under `FitsEnv M lim st (ChainCloneEnv x.gc)`, neither OOM nor
    `handle_error` panic can occur (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
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

/-! ## 2. `trTrapProgAt` and `tripleRatchetProgAt` Contract Predicates -/

def ProtoChainClone3Ok_trap (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr chainClone3Name)
    (protoChainCloneSpec M A lim)

def ProtoChainClone3Ok (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainClone3Name)
    (protoChainCloneSpec M A lim)

def ChainClone3Ok_trap (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr chainClone3Name)
    (chainCloneSpec M A lim)

def ChainClone3Ok (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainClone3Name)
    (chainCloneSpec M A lim)

def SenderChainClone3Ok_trap (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr chainClone3Name)
    (senderChainCloneSpec M A lim)

def SenderChainClone3Ok (M : AllocCostModel) (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainClone3Name)
    (senderChainCloneSpec M A lim)

end LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneBaseBudget
