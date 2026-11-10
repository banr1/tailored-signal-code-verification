/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit

/-!
# Budget-Threaded `SignedPreKeyStore` Contract

`RustCliAllocBudget`-threaded `SignedPreKeyStore` contracts: `SignedPreKeyStoreBudgetEnv` and
non-panicking/non-OOM shim and poll specifications for `get_signed_pre_key`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (SignedPreKeyRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (PreKeyShimCall PreKeyPollCall SignedPreKeyStoreSpec spkGetPollOutAt withEnvPre)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)

/-- Retag phantom `RustAlloc` parameter on `SignedPreKeyStoreSpec` (`rfl` on all projections). -/
abbrev retagSignedPreKeyStore {A A' : RustAlloc} {b : BitVec 64}
    (kit : SignedPreKeyStoreSpec A b) : SignedPreKeyStoreSpec A' b :=
  { kit with }

/-- Store-specific poll allocation envelope for `SignedPreKeyStoreSpec`. -/
structure SignedPreKeyStoreBudgetEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SignedPreKeyStoreSpec A b) where
  getPollEnv : kit.SpkState → BitVec 32 → List AllocEvent → Prop

/-- Budget-threaded `get_signed_pre_key` shim contract parameterized by
    `kit : SignedPreKeyStoreSpec A.repAlloc b`. -/
def kitSpkGetShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SignedPreKeyStoreSpec A.repAlloc b) (fds : Bool := false) :
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

/-- Budget-threaded `get_signed_pre_key` poll contract parameterized by
    `kit : SignedPreKeyStoreSpec A.repAlloc b` and `kitEnv : SignedPreKeyStoreBudgetEnv kit`. -/
def kitSpkGetPollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SignedPreKeyStoreSpec A.repAlloc b)
    (kitEnv : SignedPreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (PreKeyPollCall × kit.SpkState × M.σ) where
  pre := fun (x, st0, st) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.idOk x.id ∧ FitsEnv M lim st (kitEnv.getPollEnv st0 x.id)⌝ ∗
      kit.getBoxAt x.fut x.self x.id 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 88 ∗
      A.pool lim st s ∗ stackAt s.sp kit.getPollStack
  post := fun (x, st0, st) s0 sf =>
    ∃∗ ans : Except kit.GetErr SignedPreKeyRecord, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans ∧
           kitEnv.getPollEnv st0 x.id evs
       | true =>
         kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans ∧
           kitEnv.getPollEnv st0 x.id evs ∧ kit.fdsOk sf.fs⌝ ∗
      kit.getBoxAt x.fut x.self x.id 1#8 ∗
      kit.storeAt x.self (kit.getUpdate st0 x.id ans) ∗
      spkGetPollOutAt kit x.out ans ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.getPollStack

/-- `get_signed_pre_key` budget poll contract with `kit.envOk` (and `kit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitSpkGetPollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SignedPreKeyStoreSpec A.repAlloc b)
    (kitEnv : SignedPreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (PreKeyPollCall × kit.SpkState × M.σ) :=
  withEnvPre (kitSpkGetPollSpec M A lim kit kitEnv fds)
    (match fds with
     | false => fun s => kit.envOk s.fs.files
     | true => fun s => kit.envOk s.fs.files ∧ kit.fdsOk s.fs)

end LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
