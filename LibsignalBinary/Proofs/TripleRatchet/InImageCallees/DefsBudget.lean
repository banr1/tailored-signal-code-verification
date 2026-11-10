/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Heap.SpecBudget

/-!
# Budget-Threaded Contracts for In-Image Whole-Crate Callees

`VmPreserved` and `RustCliAllocBudget` contracts for `Uuid::try_parse`,
`ServiceId::parse_from_service_id_string`, `PrivateKey::serialize`, and
`<ProtocolAddress as Display>::fmt`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (
  addrDisplayStack extHookStack parseSidCodeSpec parseSidCodeStackSpec privSerializeStackX
  uuidTryParseCodeSpec uuidTryParseSpec uuidTryParseStackSpec
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv withVmPreserved)

/-! ## `VmPreserved`-strengthened `Uuid::try_parse` and `ServiceId::parse_from_service_id_string` -/

def uuidTryParseBudgetSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (uuidTryParseSpec parse)

def uuidTryParseCodeBudgetSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (uuidTryParseCodeSpec parse)

def uuidTryParseStackBudgetSpec (hookStack : Nat := 0) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (uuidTryParseStackSpec hookStack)

def parseSidCodeBudgetSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (parseSidCodeSpec parse)

def parseSidCodeStackBudgetSpec (hookStack : Nat := 0) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (parseSidCodeStackSpec hookStack)

/-! ## `PrivateKey::serialize` -/

/-- Exact allocator event sequence of `<PrivateKey>::serialize`: a single 32-byte, 1-aligned
allocation (`self.key.to_vec()`). -/
def privSerializeEvents : List AllocEvent :=
  rustAllocEvents 32 1

def PrivSerializeEnv (evs : List AllocEvent) : Prop :=
  evs = privSerializeEvents

/-- Stack-parameterized budget contract for `<PrivateKey>::serialize` (Block `208`).
Ghost: `(k, bs, ret, st)`. Under `FitsEnv M lim st PrivSerializeEnv`, `__rust_alloc(32, 1)`
returns non-null and `onPanic = ⌜False⌝`. -/
def privSerializeSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (totalStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) where
  pre := fun (k, bs, ret, st) s =>
    ⌜s.readReg64 .x0 = k ∧ s.readReg64 .x8 = ret ∧ bs.length = 32 ∧
      FitsEnv M lim st PrivSerializeEnv⌝ ∗
      (k ↦ₛ bs) ∗ memRegion ret 24 ∗ A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun (k, bs, ret, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (k ↦ₛ bs) ∗ vecU8 A.repAlloc ret bs ∗
      A.pool lim (M.stepEvents privSerializeEvents st) sf ∗ stackAt s0.sp totalStack

abbrev privSerializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) :=
  privSerializeSpecWithStack M A lim extHookStack

abbrev privSerializeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) :=
  privSerializeSpecWithStack M A lim privSerializeStackX

/-! ## `<ProtocolAddress as Display>::fmt` -/

/-- Envelope-parametric budget contract for `<ProtocolAddress as Display>::fmt` (Block `215`),
defaulting to `FmtWriteEnv`. Ghost: `(f, v, vt, bs, st)`. -/
def addrDisplayEnvSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (Env : List AllocEvent → Prop := FmtWriteEnv) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × M.σ) where
  pre := fun (f, v, vt, bs, st) s =>
    ⌜s.readReg64 .x1 = f ∧ FitsEnv M lim st Env⌝ ∗
      (f ↦₆₄ v) ∗ ((f + 8#64) ↦₆₄ vt) ∗ vecU8 A.repAlloc v bs ∗
      A.pool lim st s ∗ stackAt s.sp addrDisplayStack
  post := fun (f, v, vt, _, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace ∧ Env evs⌝ ∗
      (f ↦₆₄ v) ∗ ((f + 8#64) ↦₆₄ vt) ∗
      (∃∗ bs' : List (BitVec 8), vecU8 A.repAlloc v bs') ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp addrDisplayStack

abbrev addrDisplaySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × M.σ) :=
  addrDisplayEnvSpec M A lim FmtWriteEnv

end LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
