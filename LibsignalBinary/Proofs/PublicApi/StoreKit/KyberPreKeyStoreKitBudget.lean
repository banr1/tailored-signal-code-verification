/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit

/-!
# Budget-Threaded `KyberPreKeyStore` Contracts

`RustCliAllocBudget M` counterparts of `KyberPreKeyStoreKit`, providing `retagKyberPreKeyStore`,
`KyberPreKeyStoreBudgetEnv`, and total-correctness shim and poll contracts (`onPanic = ⌜False⌝`,
`onOom = ⌜False⌝`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (PreKeyShimCall PreKeyPollCall KyberMarkShimCall KyberMarkPollCall
   KyberPreKeyStoreSpec kpkGetPollOutAt kpkMarkPollOutAt withEnvPre)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)

/-- Retag phantom `RustAlloc` parameter on `KyberPreKeyStoreSpec` (`rfl` on all projections). -/
abbrev retagKyberPreKeyStore {A A' : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) : KyberPreKeyStoreSpec A' b :=
  { kit with }

/-- Store-specific poll allocation envelopes for `KyberPreKeyStoreSpec`. -/
structure KyberPreKeyStoreBudgetEnv {A : RustAlloc} {b : BitVec 64}
    (kit : KyberPreKeyStoreSpec A b) where
  getPollEnv : kit.KpkState → BitVec 32 → List AllocEvent → Prop
  markPollEnv : kit.KpkState → BitVec 32 → BitVec 32 → PublicKey → List AllocEvent → Prop

/-- Budget-threaded `get_kyber_pre_key` shim contract. -/
def kitKpkGetShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : KyberPreKeyStoreSpec A.repAlloc b) (fds : Bool := false) :
    Spec (PreKeyShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜match fds with
     | false =>
       (b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
         FitsEnv M lim st (BoxAllocEnv kit.getBoxSize)
     | true =>
       (b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
         FitsEnv M lim st (BoxAllocEnv kit.getBoxSize) ∧ kit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp kit.getShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + kit.getFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.getBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + kit.getFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.getBoxSize evs ∧ kit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) kit.getBoxSize 8 ∗
      kit.getBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.getShimStack

/-- Budget-threaded `mark_kyber_pre_key_used` shim contract. -/
def kitKpkMarkShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : KyberPreKeyStoreSpec A.repAlloc b) (fds : Bool := false) :
    Spec (KyberMarkShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜match fds with
     | false =>
       (b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
         s.readReg32 .x2 = x.signedId ∧ s.readReg64 .x3 = x.baseKeyA ∧
         FitsEnv M lim st (BoxAllocEnv kit.markBoxSize)
     | true =>
       (b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
         s.readReg32 .x2 = x.signedId ∧ s.readReg64 .x3 = x.baseKeyA ∧
         FitsEnv M lim st (BoxAllocEnv kit.markBoxSize) ∧ kit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp kit.markShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + kit.markFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.markBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + kit.markFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.markBoxSize evs ∧ kit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) kit.markBoxSize 8 ∗
      kit.markBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.markShimStack

/-- Budget-threaded `get_kyber_pre_key` poll contract. -/
def kitKpkGetPollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : KyberPreKeyStoreSpec A.repAlloc b)
    (kitEnv : KyberPreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (PreKeyPollCall × kit.KpkState × M.σ) where
  pre := fun (x, st0, st) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.getIdOk x.id ∧ FitsEnv M lim st (kitEnv.getPollEnv st0 x.id)⌝ ∗
      kit.getBoxAt x.fut x.self x.id 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 88 ∗
      A.pool lim st s ∗ stackAt s.sp kit.getPollStack
  post := fun (x, st0, st) s0 sf =>
    ∃∗ ans : Except kit.GetErr KyberPreKeyRecord, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans ∧
           kitEnv.getPollEnv st0 x.id evs
       | true =>
         kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans ∧
           kitEnv.getPollEnv st0 x.id evs ∧ kit.fdsOk sf.fs⌝ ∗
      kit.getBoxAt x.fut x.self x.id 1#8 ∗
      kit.storeAt x.self (kit.getUpdate st0 x.id ans) ∗
      kpkGetPollOutAt kit x.out ans ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.getPollStack

/-- Budget-threaded `mark_kyber_pre_key_used` poll contract. -/
def kitKpkMarkPollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : KyberPreKeyStoreSpec A.repAlloc b)
    (kitEnv : KyberPreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (KyberMarkPollCall × kit.KpkState × M.σ) where
  pre := fun (x, st0, st) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.markOk x.id x.signedId x.baseKey ∧
      FitsEnv M lim st (kitEnv.markPollEnv st0 x.id x.signedId x.baseKey)⌝ ∗
      kit.markBoxAt x.fut x.self x.baseKeyA x.id x.signedId 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 48 ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      A.pool lim st s ∗ stackAt s.sp kit.markPollStack
  post := fun (x, st0, st) s0 sf =>
    ∃∗ ans : Except kit.MarkErr Unit, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         kit.markRel st0 x.id x.signedId x.baseKey ans ∧
           sf.trace = s0.trace ++ kit.markEvs x.id x.signedId x.baseKey ans ∧
           kitEnv.markPollEnv st0 x.id x.signedId x.baseKey evs
       | true =>
         kit.markRel st0 x.id x.signedId x.baseKey ans ∧
           sf.trace = s0.trace ++ kit.markEvs x.id x.signedId x.baseKey ans ∧
           kitEnv.markPollEnv st0 x.id x.signedId x.baseKey evs ∧ kit.fdsOk sf.fs⌝ ∗
      kit.markBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
      kit.storeAt x.self (kit.markUpdate st0 x.id x.signedId x.baseKey ans) ∗
      kpkMarkPollOutAt kit x.out ans ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.markPollStack

/-- `get_kyber_pre_key` budget poll contract with `kit.envOk` (and `kit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitKpkGetPollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : KyberPreKeyStoreSpec A.repAlloc b)
    (kitEnv : KyberPreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (PreKeyPollCall × kit.KpkState × M.σ) :=
  withEnvPre (kitKpkGetPollSpec M A lim kit kitEnv fds)
    (match fds with
     | false => fun s => kit.envOk s.fs.files
     | true => fun s => kit.envOk s.fs.files ∧ kit.fdsOk s.fs)

/-- `mark_kyber_pre_key_used` budget poll contract with `kit.envOk` (and `kit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitKpkMarkPollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : KyberPreKeyStoreSpec A.repAlloc b)
    (kitEnv : KyberPreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (KyberMarkPollCall × kit.KpkState × M.σ) :=
  withEnvPre (kitKpkMarkPollSpec M A lim kit kitEnv fds)
    (match fds with
     | false => fun s => kit.envOk s.fs.files
     | true => fun s => kit.envOk s.fs.files ∧ kit.fdsOk s.fs)

end LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
