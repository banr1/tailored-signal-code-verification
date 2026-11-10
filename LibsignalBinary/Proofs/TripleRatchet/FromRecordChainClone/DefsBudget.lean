/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Defs

/-!
# Budget-Threaded `Chain::clone [local#2]` Specifications

Defines deterministic allocation-event traces (`chainCloneEvents`, `senderChainCloneEvents`),
envelopes (`ChainCloneEnv`, `SenderChainCloneEnv`), and total-correctness budget contracts
(`chainCloneSpec`, `senderChainCloneSpec`) over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ReceiverChain SenderChain)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost optSenderChainAt)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (
  chainCloneStack ChainCloneGhost SenderChainCloneGhost
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEvents FitsEnv rustAllocEvents
)

/-! ## 1. Deterministic `AllocEvent` Trace & Envelope for `Chain::clone` -/

/-- Deterministic `AllocEvent` sequence emitted by `<session_structure::Chain as Clone>::clone`
    in execution order:
    1. `sender_ratchet_key` (`len > 0` → `rustAllocEvents len 1`);
    2. `sender_ratchet_key_private` (`len > 0` → `rustAllocEvents len 1`);
    3. `chain_key` (`some _` → `rustAllocEvents 32 1`);
    4. `message_keys` (`nonempty` → `rustAllocEvents (104 * len) 8` followed by `len` per-element
       `seed` allocations `rustAllocEvents mkg.seed.length 1`). -/
def chainCloneEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  (if gc.1.srk.bytes.length = 0 then [] else rustAllocEvents gc.1.srk.bytes.length 1) ++
  (if gc.1.priv.bytes.length = 0 then [] else rustAllocEvents gc.1.priv.bytes.length 1) ++
  (match gc.2.chainKey with
   | none => []
   | some _ => rustAllocEvents 32 1) ++
  (if gc.2.messageKeys = [] then []
   else rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
     gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1))

/-- Allocation envelope for `<session_structure::Chain as Clone>::clone` on `gc`. -/
def ChainCloneEnv (gc : ChainGhost × ReceiverChain) (evs : List AllocEvent) : Prop :=
  evs = chainCloneEvents gc

theorem chainCloneEnv_events (gc : ChainGhost × ReceiverChain) :
    ChainCloneEnv gc (chainCloneEvents gc) := rfl

theorem fitsEvents_chainClone_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (st : M.σ) (gc : ChainGhost × ReceiverChain) (h : FitsEnv M lim st (ChainCloneEnv gc)) :
    FitsEvents M lim st (chainCloneEvents gc) :=
  h (chainCloneEvents gc) rfl

/-! ## 2. Budget-Threaded `chainCloneSpec` -/

/-- Budget-threaded specification of `<session_structure::Chain as Clone>::clone`:
    under `FitsEnv M lim st (ChainCloneEnv x.gc)`, neither OOM nor `handle_error` panic can occur
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chainCloneSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (ChainCloneEnv x.gc)⌝ ∗
      memRegion x.dst 104 ∗ chainAt A.repAlloc x.gc x.src ∗
      A.pool lim st s ∗ stackAt s.sp chainCloneStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ ChainCloneEnv x.gc evs⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        chainAt A.repAlloc (g', x.gc.2) x.dst) ∗
      chainAt A.repAlloc x.gc x.src ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack

/-! ## 3. Sender-Chain Clone Trace, Envelope, and `senderChainCloneSpec` -/

/-- Underlying `(ChainGhost × ReceiverChain)` view of a `Some` sender chain `(g, sc)`. -/
def senderChainAsProtoGhost (g : SenderChainGhost) (sc : SenderChain) :
    ChainGhost × ReceiverChain :=
  (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
    ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩)

/-- Deterministic `AllocEvent` sequence emitted when cloning a `Some` sender chain `(g, sc)`. -/
def senderChainCloneEvents (g : SenderChainGhost) (sc : SenderChain) : List AllocEvent :=
  chainCloneEvents (senderChainAsProtoGhost g sc)

/-- Allocation envelope for cloning a `Some` sender chain `(g, sc)`. -/
def SenderChainCloneEnv (g : SenderChainGhost) (sc : SenderChain)
    (evs : List AllocEvent) : Prop :=
  evs = senderChainCloneEvents g sc

theorem senderChainCloneEnv_events (g : SenderChainGhost) (sc : SenderChain) :
    SenderChainCloneEnv g sc (senderChainCloneEvents g sc) := rfl

/-- Budget-threaded sender-chain clone specification (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`
    under `FitsEnv M lim st (SenderChainCloneEnv x.g x.sc)`). -/
def senderChainCloneSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SenderChainCloneGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧
      FitsEnv M lim st (SenderChainCloneEnv x.g x.sc)⌝ ∗
      memRegion x.dst 104 ∗ optSenderChainAt A.repAlloc x.src (some x.g) (some x.sc) ∗
      A.pool lim st s ∗ stackAt s.sp chainCloneStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SenderChainCloneEnv x.g x.sc evs⌝ ∗
      (∃∗ g' : SenderChainGhost,
        ⌜g'.srk.bytes = x.g.srk.bytes ∧ g'.priv.bytes = x.g.priv.bytes⌝ ∗
        optSenderChainAt A.repAlloc x.dst (some g') (some x.sc)) ∗
      optSenderChainAt A.repAlloc x.src (some x.g) (some x.sc) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainCloneStack

end LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
