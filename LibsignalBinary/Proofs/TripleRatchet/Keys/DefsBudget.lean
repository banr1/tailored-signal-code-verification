/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# Budget-Threaded Key-Derivation Specifications

`RustCliAllocBudget` and `VmPreserved` contracts and allocator event envelopes for
`ct_eq`, `<PrivateKey>::calculate_agreement`, `<RootKey>::create_chain`, and
`<MessageKeyGenerator>::generate_keys`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget

open Arm64 ProofLib
open CryptoGames.Ratchet (X25519Fn)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto ShaCompress rootCreateChain)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes)
open CryptoVerification.LibsignalTripleRatchet (
  calculateAgreementStack calculateAgreementStackX
  createChainStack createChainStackX
  generateKeysStack generateKeysStackX
  CalculateAgreementGhost CreateChainGhost GenerateKeysGhost
  calculateAgreement calculateAgreementResultAt
  createChainResultAt messageKeysAt
  mkgAt spqrRecvKeyAt
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
  FitsEnv FreeOnlyEvs rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

/-! ## Read-only `ct_eq` with `VmPreserved` -/

noncomputable def ctEqSliceROSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved CryptoVerification.LibsignalTripleRatchet.ctEqSliceROSpec

/-! ## `<PrivateKey>::calculate_agreement` -/

def calculateAgreementEvents (X : X25519Fn) (x : CalculateAgreementGhost) :
    List AllocEvent :=
  match calculateAgreement X x.their x.our with
  | some _ => rustAllocEvents 32 1
  | none => []

def CalculateAgreementEnv (X : X25519Fn) (x : CalculateAgreementGhost)
    (evs : List AllocEvent) : Prop :=
  evs = calculateAgreementEvents X x

def calculateAgreementSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (X : X25519Fn) (totalStack : Nat) :
    Spec (CalculateAgreementGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ourA ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret ∧
      FitsEnv M lim st (CalculateAgreementEnv X x)⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      memRegion x.ret 24 ∗ A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ CalculateAgreementEnv X x evs⌝ ∗
        (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
        calculateAgreementResultAt A.repAlloc x.ret (calculateAgreement X x.their x.our) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp totalStack

abbrev calculateAgreementSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (X : X25519Fn) :
    Spec (CalculateAgreementGhost × M.σ) :=
  calculateAgreementSpecWithStack M A lim X calculateAgreementStack

abbrev calculateAgreementSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (X : X25519Fn) :
    Spec (CalculateAgreementGhost × M.σ) :=
  calculateAgreementSpecWithStack M A lim X calculateAgreementStackX

/-! ## `<RootKey>::create_chain` -/

def createChainEvents (C : Crypto) (x : CreateChainGhost) : List AllocEvent :=
  match calculateAgreement C.X x.their x.our with
  | some _ => rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
  | none => []

def CreateChainEnv (C : Crypto) (x : CreateChainGhost) (evs : List AllocEvent) : Prop :=
  evs = createChainEvents C x

def createChainSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (C : Crypto) (totalStack : Nat) :
    Spec (CreateChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.rkA ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ourA ∧
      s.readReg64 .x8 = x.ret ∧ x.rkA ≠ 0#64 ∧
      FitsEnv M lim st (CreateChainEnv C x)⌝ ∗
      (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ memRegion x.ret 72 ∗
      A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ CreateChainEnv C x evs⌝ ∗
        (x.rkA ↦ₛ keyToBytes32 x.rk) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ourA ↦ₛ x.our.bytes.toList) ∗
        createChainResultAt x.ret (rootCreateChain C x.rk x.their x.our) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp totalStack

abbrev createChainSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (C : Crypto) :
    Spec (CreateChainGhost × M.σ) :=
  createChainSpecWithStack M A lim C createChainStack

abbrev createChainSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (C : Crypto) :
    Spec (CreateChainGhost × M.σ) :=
  createChainSpecWithStack M A lim C createChainStackX

/-! ## `<MessageKeyGenerator>::generate_keys` -/

/-- Concrete binary deallocation envelope of `<MessageKeyGenerator>::generate_keys`
(`Keys/GenerateKeys.lean`):
1. Frees `g.seed`'s 32-byte `Vec<u8>` buffer (`rustDeallocEvents c₁ 1`, `32 ≤ c₁ < 2 ^ 63`).
2. When `pqrKey = some _`, frees `pqrKey`'s 32-byte `Vec<u8>` buffer (`rustDeallocEvents c₂ 1`,
   `32 ≤ c₂ < 2 ^ 63`); when `pqrKey = none`, either `pqrKey` has no positive-capacity buffer (`[]`)
   or frees a positive-capacity empty `Vec` (`rustDeallocEvents c₂ 1`, `0 < c₂ < 2 ^ 63`). -/
def GenerateKeysEnv (x : GenerateKeysGhost) (evs : List AllocEvent) : Prop :=
  ∃ c₁ : Nat, 32 ≤ c₁ ∧ c₁ < 2 ^ 63 ∧
    match x.pqrKey with
    | some _ =>
      ∃ c₂ : Nat, 32 ≤ c₂ ∧ c₂ < 2 ^ 63 ∧
        evs = rustDeallocEvents c₁ 1 ++ rustDeallocEvents c₂ 1
    | none =>
      evs = rustDeallocEvents c₁ 1 ∨
        ∃ c₂ : Nat, 0 < c₂ ∧ c₂ < 2 ^ 63 ∧
          evs = rustDeallocEvents c₁ 1 ++ rustDeallocEvents c₂ 1

theorem generateKeysEnv_canonical (x : GenerateKeysGhost) :
    GenerateKeysEnv x
      (match x.pqrKey with
       | some _ => rustDeallocEvents 32 1 ++ rustDeallocEvents 32 1
       | none => rustDeallocEvents 32 1) := by
  refine ⟨32, Nat.le_refl 32, by decide, ?_⟩
  cases x.pqrKey with
  | some _ => exact ⟨32, Nat.le_refl 32, by decide, rfl⟩
  | none => exact Or.inl rfl

theorem freeOnlyEvs_of_generateKeysEnv {x : GenerateKeysGhost} {evs : List AllocEvent}
    (h : GenerateKeysEnv x evs) : FreeOnlyEvs evs := by
  rcases h with ⟨c₁, _, _, hpqr⟩
  cases hp : x.pqrKey <;> simp only [hp] at hpqr
  · rcases hpqr with rfl | ⟨c₂, _, _, rfl⟩
    · exact FreeOnlyEvs.singleton 1 c₁
    · exact (FreeOnlyEvs.singleton 1 c₁).append (FreeOnlyEvs.singleton 1 c₂)
  · rcases hpqr with ⟨c₂, _, _, rfl⟩
    exact (FreeOnlyEvs.singleton 1 c₁).append (FreeOnlyEvs.singleton 1 c₂)

def generateKeysSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (totalStack : Nat) :
    Spec (GenerateKeysGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.genA ∧ s.readReg64 .x1 = x.pqrKeyA ∧ s.readReg64 .x8 = x.ret ∧
      x.g.seed.length = 32⌝ ∗
      mkgAt A.repAlloc x.genA x.g ∗ spqrRecvKeyAt A.repAlloc x.pqrKeyA x.pqrKey ∗
      memRegion x.ret 84 ∗ A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ GenerateKeysEnv x evs⌝ ∗
        memRegion x.genA 40 ∗ memRegion x.pqrKeyA 24 ∗
        messageKeysAt x.ret (x.g.generateKeys F x.pqrKey) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp totalStack

abbrev generateKeysSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (GenerateKeysGhost × M.σ) :=
  generateKeysSpecWithStack M A lim F generateKeysStack

abbrev generateKeysSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (GenerateKeysGhost × M.σ) :=
  generateKeysSpecWithStack M A lim F generateKeysStackX

end LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
