/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Placed Stage P2 Over-Path Call-Stack Bounds

Proves `retag*Store` and `A.atState` call-stack equalities together with `[LibsignalPlacement]`
stack-floor, 4K-equivalence, and `< 2 ^ 32` bounds for `stageP2OverCallStack` and
`stageP2OverV1CallStack` over `A : RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2PlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentitySelfStoreSpec IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec
  SignedPreKeyStoreSpec
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP2CallStack stageP2V1CallStack
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  p2_over_callStack_le_v1CallStack p2_over_callStack_le_v1CallStack_placed
  p2_over_callStack_lt_32 p2_over_pure_le_callStack p2_over_pure_le_callStack_placed
  p2_over_pure_le_v1CallStack p2_over_pure_le_v1CallStack_placed p2_over_v1CallStack_lt_32
  stageP2OverCallStack stageP2OverCallStack4K stageP2OverCallStack4K_eq
  stageP2OverPureAndErrStack stageP2OverV1CallStack stageP2OverV1CallStack4K
  stageP2OverV1CallStack4K_eq
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (retagSignedPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (retagKyberPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (retagPreKeyStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (retagIdentitySelfStore)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  p2_over_pure_le_callStack_placed
  p2_over_pure_le_v1CallStack_placed
  p2_over_callStack_le_v1CallStack_placed
)

/-! ## Store-Retagging and `A.atState` Stack Equalities -/

theorem stageP2OverCallStack_retag_eq [LibsignalPlacement] {A A' : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack
        (retagSignedPreKeyStore (A' := A') spkKit)
        (retagKyberPreKeyStore (A' := A') kpkKit)
        (retagPreKeyStore (A' := A') pkKit)
        (retagIdentitySelfStore (A' := A') skit) =
      stageP2OverCallStack spkKit kpkKit pkKit skit :=
  rfl

theorem stageP2OverCallStack4K_retag_eq [LibsignalPlacement] {A A' : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack4K
        (retagSignedPreKeyStore (A' := A') spkKit)
        (retagKyberPreKeyStore (A' := A') kpkKit)
        (retagPreKeyStore (A' := A') pkKit)
        (retagIdentitySelfStore (A' := A') skit) =
      stageP2OverCallStack4K spkKit kpkKit pkKit skit :=
  rfl

theorem stageP2OverV1CallStack_retag_eq [LibsignalPlacement] {A A' : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverV1CallStack
        (retagSignedPreKeyStore (A' := A') spkKit)
        (retagKyberPreKeyStore (A' := A') kpkKit)
        (retagPreKeyStore (A' := A') pkKit)
        (retagIdentitySelfStore (A' := A') skit) =
      stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  rfl

theorem stageP2OverV1CallStack4K_retag_eq [LibsignalPlacement] {A A' : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverV1CallStack4K
        (retagSignedPreKeyStore (A' := A') spkKit)
        (retagKyberPreKeyStore (A' := A') kpkKit)
        (retagPreKeyStore (A' := A') pkKit)
        (retagIdentitySelfStore (A' := A') skit) =
      stageP2OverV1CallStack4K spkKit kpkKit pkKit skit :=
  rfl

theorem stageP2OverCallStack_atState_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack
        (retagSignedPreKeyStore (A' := A.atState lim st s) spkKit)
        (retagKyberPreKeyStore (A' := A.atState lim st s) kpkKit)
        (retagPreKeyStore (A' := A.atState lim st s) pkKit)
        (retagIdentitySelfStore (A' := A.atState lim st s) skit) =
      stageP2OverCallStack spkKit kpkKit pkKit skit :=
  rfl

theorem stageP2OverV1CallStack_atState_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverV1CallStack
        (retagSignedPreKeyStore (A' := A.atState lim st s) spkKit)
        (retagKyberPreKeyStore (A' := A.atState lim st s) kpkKit)
        (retagPreKeyStore (A' := A.atState lim st s) pkKit)
        (retagIdentitySelfStore (A' := A.atState lim st s) skit) =
      stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  rfl

theorem stageP2OverV1CallStack4K_atState_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverV1CallStack4K
        (retagSignedPreKeyStore (A' := A.atState lim st s) spkKit)
        (retagKyberPreKeyStore (A' := A.atState lim st s) kpkKit)
        (retagPreKeyStore (A' := A.atState lim st s) pkKit)
        (retagIdentitySelfStore (A' := A.atState lim st s) skit) =
      stageP2OverV1CallStack4K spkKit kpkKit pkKit skit :=
  rfl

/-! ## Placed Stack-Floor and 4K-Equivalence Lemmas -/

theorem stageP2OverCallStack4K_budget_placed_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack4K spkKit kpkKit pkKit skit =
      stageP2OverCallStack spkKit kpkKit pkKit skit :=
  stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit

theorem stageP2OverV1CallStack4K_budget_placed_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverV1CallStack4K spkKit kpkKit pkKit skit =
      stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  stageP2OverV1CallStack4K_eq spkKit kpkKit pkKit skit

theorem p2_over_pure_le_callStack_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverPureAndErrStack ≤ stageP2OverCallStack spkKit kpkKit pkKit skit :=
  p2_over_pure_le_callStack spkKit kpkKit pkKit skit

theorem p2_over_pure_le_callStack4K_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverPureAndErrStack ≤ stageP2OverCallStack4K spkKit kpkKit pkKit skit := by
  rw [stageP2OverCallStack4K_eq]
  exact p2_over_pure_le_callStack spkKit kpkKit pkKit skit

theorem p2_over_pure_le_v1CallStack_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverPureAndErrStack ≤ stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  p2_over_pure_le_v1CallStack spkKit kpkKit pkKit skit

theorem p2_over_pure_le_v1CallStack4K_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverPureAndErrStack ≤ stageP2OverV1CallStack4K spkKit kpkKit pkKit skit := by
  rw [stageP2OverV1CallStack4K_eq]
  exact p2_over_pure_le_v1CallStack spkKit kpkKit pkKit skit

theorem p2_over_callStack_le_v1CallStack_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack spkKit kpkKit pkKit skit ≤
      stageP2OverV1CallStack spkKit kpkKit pkKit skit :=
  p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit

theorem p2_over_callStack4K_le_v1CallStack4K_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2OverCallStack4K spkKit kpkKit pkKit skit ≤
      stageP2OverV1CallStack4K spkKit kpkKit pkKit skit := by
  rw [stageP2OverCallStack4K_eq, stageP2OverV1CallStack4K_eq]
  exact p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit

theorem p2_over_callStack_lt_32_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit)
    (hcall_lt : stageP2CallStack spkKit kpkKit pkKit skit < 2 ^ 32) :
    stageP2OverCallStack spkKit kpkKit pkKit skit < 2 ^ 32 :=
  p2_over_callStack_lt_32 spkKit kpkKit pkKit skit hcall_lt

theorem p2_over_v1CallStack_lt_32_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit)
    (hcall_lt : stageP2V1CallStack spkKit kpkKit pkKit skit < 2 ^ 32) :
    stageP2OverV1CallStack spkKit kpkKit pkKit skit < 2 ^ 32 :=
  p2_over_v1CallStack_lt_32 spkKit kpkKit pkKit skit hcall_lt

theorem p2_over_callStack4K_lt_32_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit)
    (hcall_lt : stageP2CallStack spkKit kpkKit pkKit skit < 2 ^ 32) :
    stageP2OverCallStack4K spkKit kpkKit pkKit skit < 2 ^ 32 := by
  rw [stageP2OverCallStack4K_eq]
  exact p2_over_callStack_lt_32 spkKit kpkKit pkKit skit hcall_lt

theorem p2_over_v1CallStack4K_lt_32_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (spkKit : SignedPreKeyStoreSpec A.repAlloc b)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc b)
    (pkKit : PreKeyStoreSpec A.repAlloc b)
    (skit : IdentitySelfStoreSpec ikit)
    (hcall_lt : stageP2V1CallStack spkKit kpkKit pkKit skit < 2 ^ 32) :
    stageP2OverV1CallStack4K spkKit kpkKit pkKit skit < 2 ^ 32 := by
  rw [stageP2OverV1CallStack4K_eq]
  exact p2_over_v1CallStack_lt_32 spkKit kpkKit pkKit skit hcall_lt

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2PlacedBudget
