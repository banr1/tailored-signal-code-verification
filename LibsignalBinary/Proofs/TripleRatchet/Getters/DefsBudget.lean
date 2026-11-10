/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs

/-!
# Budget-Threaded Specifications for Identity Getters, `clear_unacknowledged_pre_key_message`, and Drop Glue

Defines budget-threaded specifications over `RustCliAllocBudget M`:
- `localIdentityKeyPlacedSpec` and `remoteIdentityKeyPlacedSpec` (blocks `28` and `29`, `VmPreserved`);
- pure-deallocation contracts (`clearUpkSpec`, `dropChainSpec`, `dropProtoChainSpec`,
  `dropVecMessageKeySpec`, `dropVecChainSpec`, `dropSpeSpec`, and their `*X` / `*Base` variants)
  emitting `FreeOnlyEvs` with `onPanic = onOom = ⌜False⌝`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SessionState)
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.RustHeap (RustAlloc vecAt)
open CryptoVerification.LibsignalSessionRepr (chainAt messageKeyAt)
open CryptoVerification.LibsignalTripleRatchetRepr (sessionStateAt speAt)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved FreeOnlyEvs
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  localIdentityKeyStack remoteIdentityKeyStack
  clearUpkStack clearUpkStackX
  dropChainStack dropChainStackX
  dropVecMessageKeyStack dropVecMessageKeyStackX
  dropVecChainStack dropVecChainStackX
  dropSpeStack dropSpeStackX
  LocalIdentityKeyGhost RemoteIdentityKeyGhost
  ClearUpkGhost DropChainGhost DropVecMessageKeyGhost DropVecChainGhost DropSpeGhost
  protoChainAt
)

/-! ## 1. `SessionState::clear_unacknowledged_pre_key_message` -/

/-- Budget-threaded specification of `<SessionState>::clear_unacknowledged_pre_key_message`
(`clearUpkStack = 32 + allocHookStack`). -/
def clearUpkSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ClearUpkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗ stackAt s.sp clearUpkStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionStateAt A.repAlloc x.ss { x.G with pending := none, kyber := none }
        x.st.clearUnacknowledgedPreKeyMessage ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp clearUpkStack

def clearUpkSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ClearUpkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗ stackAt s.sp clearUpkStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionStateAt A.repAlloc x.ss { x.G with pending := none, kyber := none }
        x.st.clearUnacknowledgedPreKeyMessage ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp clearUpkStackX

/-! ## 2. `drop_glue<session_structure::Chain>` -/

/-- Budget-threaded specification of `core::ptr::drop_glue::<session_structure::Chain>`
(`dropChainStack = 48 + allocHookStack`). -/
def dropChainSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      chainAt A.repAlloc x.gc x.a ∗ A.pool lim st s ∗ stackAt s.sp dropChainStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropChainStack

def dropChainSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      chainAt A.repAlloc x.gc x.a ∗ A.pool lim st s ∗ stackAt s.sp dropChainStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropChainStackX

/-- Budget-threaded specification of `core::ptr::drop_glue::<session_structure::Chain>` on
`protoChainAt` (`dropChainStack = 48 + allocHookStack`). -/
def dropProtoChainSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗ A.pool lim st s ∗ stackAt s.sp dropChainStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropChainStack

def dropProtoChainSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗ A.pool lim st s ∗ stackAt s.sp dropChainStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropChainStackX

/-! ## 3. `drop_glue<Vec<chain::MessageKey>>` -/

/-- Budget-threaded specification of `core::ptr::drop_glue::<Vec<chain::MessageKey>>`
(`dropVecMessageKeyStack = 48 + allocHookStack`). -/
def dropVecMessageKeySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropVecMessageKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.v x.cap x.ptr x.mks ∗
      A.pool lim st s ∗ stackAt s.sp dropVecMessageKeyStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropVecMessageKeyStack

def dropVecMessageKeySpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropVecMessageKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.v x.cap x.ptr x.mks ∗
      A.pool lim st s ∗ stackAt s.sp dropVecMessageKeyStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropVecMessageKeyStackX

/-! ## 4. `drop_glue<Vec<session_structure::Chain>>` -/

/-- Budget-threaded specification of `core::ptr::drop_glue::<Vec<session_structure::Chain>>`
(`dropVecChainStack = 48 + dropVecMessageKeyStack`). -/
def dropVecChainSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropVecChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) x.v x.cap x.ptr x.cs ∗
      A.pool lim st s ∗ stackAt s.sp dropVecChainStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropVecChainStack

def dropVecChainSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropVecChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) x.v x.cap x.ptr x.cs ∗
      A.pool lim st s ∗ stackAt s.sp dropVecChainStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropVecChainStackX

/-! ## 5. `drop_glue<SignalProtocolError>` -/

/-- Budget-threaded specification of `core::ptr::drop_glue::<SignalProtocolError>`
(`dropSpeStack = 32 + allocHookStack`). -/
def dropSpeSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropSpeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      speAt A.repAlloc x.fnName x.a x.e ∗ A.pool lim st s ∗ stackAt s.sp dropSpeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 48 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropSpeStack

def dropSpeSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (DropSpeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .x30)⌝ ∗
      speAt A.repAlloc x.fnName x.a x.e ∗ A.pool lim st s ∗ stackAt s.sp dropSpeStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 48 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropSpeStackX

/-! ## 6. Relocatable `[LibsignalPlacement]` Specs for `local_identity_key` and `remote_identity_key` -/

/-- Non-allocating `<SessionState>::local_identity_key` (Block `28`) preserving `VmPreserved`. -/
def localIdentityKeyPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec LocalIdentityKeyGhost :=
  let base := CryptoVerification.LibsignalTripleRatchet.Getters.localIdentityKeyPlacedSpec A
  { base with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ base.post x s0 sf }

/-- Non-allocating `<SessionState>::remote_identity_key` (Block `29`) preserving `VmPreserved`. -/
def remoteIdentityKeyPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec RemoteIdentityKeyGhost :=
  let base := CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyPlacedSpec A
  { base with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ base.post x s0 sf }

/-! ## 7. Un-narrowed `*Base` Specifications for Unplaced (`bare_b`) Producers -/

/-- Un-narrowed (`bare_b`) specification of `core::ptr::drop_glue::<session_structure::Chain>`. -/
def dropChainSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chainAt A.repAlloc x.gc x.a ∗ A.pool lim st s ∗ stackAt s.sp dropChainStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropChainStack

/-- Un-narrowed (`bare_b`) specification of `core::ptr::drop_glue::<session_structure::Chain>` on
`protoChainAt`. -/
def dropProtoChainSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗ A.pool lim st s ∗ stackAt s.sp dropChainStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a 104 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropChainStack

/-- Un-narrowed (`bare_b`) specification of `core::ptr::drop_glue::<Vec<chain::MessageKey>>`. -/
def dropVecMessageKeySpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropVecMessageKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.v x.cap x.ptr x.mks ∗
      A.pool lim st s ∗ stackAt s.sp dropVecMessageKeyStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropVecMessageKeyStack

/-- Un-narrowed (`bare_b`) specification of `core::ptr::drop_glue::<Vec<session_structure::Chain>>`. -/
def dropVecChainSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropVecChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v⌝ ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) x.v x.cap x.ptr x.cs ∗
      A.pool lim st s ∗ stackAt s.sp dropVecChainStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp dropVecChainStack

end LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
