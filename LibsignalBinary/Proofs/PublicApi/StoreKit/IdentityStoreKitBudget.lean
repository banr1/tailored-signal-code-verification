/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit

/-!
# Budget-Threaded `IdentityKeyStore` Contracts

`RustCliAllocBudget M` counterparts of `IdentityStoreKit`, providing `PublicApiHooksNoStores`,
`retagIdentityStore`, `IdentityStoreBudgetEnv`, step envelopes `TrustStepEnv` and `SaveStepEnv`, and
total-correctness shim and poll contracts (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto IdentityKey)
open CryptoGames.LibsignalSessionApi (Direction IdentityChange SessionRecord)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal directionByte)
open CryptoVerification.LibsignalPublicApi (IdentityCall)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (IdentityShimCall IdentityPollCall IdentityStoreSpec trustPollOutAt savePollOutAt withEnvPre)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv SeqEnv rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (PublicApiStoreEnv PublicApiHooksNoSessionStoreBudget PublicApiHooksBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (PublicApiHooksNoSessionStore)

/-- Store-free subset of `PublicApiHooksBudget` without any session-store or identity-store hooks
    (alias of `SpecBudget.PublicApiHooksNoSessionStoreBudget`). -/
abbrev PublicApiHooksNoStores [CryptoVerification.LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  PublicApiHooksNoSessionStoreBudget C M A lim S abs

theorem PublicApiHooksNoSessionStore.toNoStores [CryptoVerification.LibsignalPlacement]
    {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {S : SpqrModel}
    {abs : String → Option (State → State)}
    {trustEnv : IdentityCall → Direction → List AllocEvent → Prop}
    {saveEnv : IdentityCall → List AllocEvent → Prop}
    (h : PublicApiHooksNoSessionStore C M A lim S abs trustEnv saveEnv) :
    PublicApiHooksNoStores C M A lim S abs where
  toTripleRatchetHooksBudget := h.toTripleRatchetHooksBudget
  timeAdd := h.timeAdd
  durationSince := h.durationSince
  stringClone := h.stringClone

theorem PublicApiHooksBudget.toNoStores [CryptoVerification.LibsignalPlacement]
    {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {storeEnv : PublicApiStoreEnv}
    (h : PublicApiHooksBudget C M A lim S encRecord abs storeEnv) :
    PublicApiHooksNoStores C M A lim S abs :=
  h.toPublicApiHooksNoSessionStoreBudget

/-- Retag phantom `RustAlloc` parameter on `IdentityStoreSpec` (`rfl` on all projections). -/
abbrev retagIdentityStore {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) : IdentityStoreSpec A' b :=
  { ikit with }

/-- Store-specific poll allocation envelopes for `IdentityStoreSpec`. -/
structure IdentityStoreBudgetEnv {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) where
  trustPollEnv : ikit.IdState → AddrVal → IdentityKey → Direction → List AllocEvent → Prop
  savePollEnv : ikit.IdState → AddrVal → IdentityKey → List AllocEvent → Prop

/-- `is_trusted_identity` shim + poll + `Box` dealloc step envelope. -/
def TrustStepEnv {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (rem : AddrVal) (key : IdentityKey) (d : Direction) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv ikit.trustBoxSize)
    (SeqEnv (ikitEnv.trustPollEnv ist0 rem key d)
      (· = rustDeallocEvents ikit.trustBoxSize 8))

/-- `save_identity` shim + poll + `Box` dealloc step envelope. -/
def SaveStepEnv {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (rem : AddrVal) (key : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv ikit.saveBoxSize)
    (SeqEnv (ikitEnv.savePollEnv ist0 rem key)
      (· = rustDeallocEvents ikit.saveBoxSize 8))

/-- Budget-threaded `is_trusted_identity` shim contract. -/
def kitTrustShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b) (fds : Bool := false) :
    Spec (IdentityShimCall × BitVec 8 × M.σ) where
  pre := fun (x, d, st) s =>
    ⌜match fds with
     | false =>
       s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
         (s.readReg64 .x3).setWidth 8 = d ∧ FitsEnv M lim st (BoxAllocEnv ikit.trustBoxSize)
     | true =>
       s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
         (s.readReg64 .x3).setWidth 8 = d ∧ FitsEnv M lim st (BoxAllocEnv ikit.trustBoxSize) ∧
         ikit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp ikit.trustShimStack
  post := fun (x, d, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + ikit.trustFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv ikit.trustBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + ikit.trustFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv ikit.trustBoxSize evs ∧ ikit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) ikit.trustBoxSize 8 ∗
      ikit.trustBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 d ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.trustShimStack

/-- Budget-threaded `save_identity` shim contract. -/
def kitSaveShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b) (fds : Bool := false) :
    Spec (IdentityShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜match fds with
     | false =>
       s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
         FitsEnv M lim st (BoxAllocEnv ikit.saveBoxSize)
     | true =>
       s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
         FitsEnv M lim st (BoxAllocEnv ikit.saveBoxSize) ∧ ikit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp ikit.saveShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + ikit.saveFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv ikit.saveBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + ikit.saveFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv ikit.saveBoxSize evs ∧ ikit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) ikit.saveBoxSize 8 ∗
      ikit.saveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.saveShimStack

/-- Budget-threaded `is_trusted_identity` poll contract. -/
def kitTrustPollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (fds : Bool := false) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState × M.σ) where
  pre := fun (x, d, self, ist0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val ∧
      FitsEnv M lim st (ikitEnv.trustPollEnv ist0 x.call.addr.val x.call.key d)⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim st s ∗ stackAt s.sp ikit.trustPollStack
  post := fun (x, d, self, ist0, st) s0 sf =>
    ∃∗ ans : Except Unit Bool, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         ikit.trustRel ist0 x.call.addr.val x.call.key d ans ∧
           sf.trace = s0.trace ++ ikit.trustEvs x.call.addr.val x.call.key d ans ∧
           ikitEnv.trustPollEnv ist0 x.call.addr.val x.call.key d evs
       | true =>
         ikit.trustRel ist0 x.call.addr.val x.call.key d ans ∧
           sf.trace = s0.trace ++ ikit.trustEvs x.call.addr.val x.call.key d ans ∧
           ikitEnv.trustPollEnv ist0 x.call.addr.val x.call.key d evs ∧ ikit.fdsOk sf.fs⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
      ikit.identityAt self (ikit.trustUpdate ist0 x.call.addr.val x.call.key d ans) ∗
      trustPollOutAt b x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.trustPollStack

/-- Budget-threaded `save_identity` poll contract. -/
def kitSavePollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (fds : Bool := false) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) where
  pre := fun (x, self, ist0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val ∧
      FitsEnv M lim st (ikitEnv.savePollEnv ist0 x.call.addr.val x.call.key)⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim st s ∗ stackAt s.sp ikit.savePollStack
  post := fun (x, self, ist0, st) s0 sf =>
    ∃∗ ans : Except Unit IdentityChange, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         ikit.saveRel ist0 x.call.addr.val x.call.key ans ∧
           sf.trace = s0.trace ++ ikit.saveEvs x.call.addr.val x.call.key ans ∧
           ikitEnv.savePollEnv ist0 x.call.addr.val x.call.key evs
       | true =>
         ikit.saveRel ist0 x.call.addr.val x.call.key ans ∧
           sf.trace = s0.trace ++ ikit.saveEvs x.call.addr.val x.call.key ans ∧
           ikitEnv.savePollEnv ist0 x.call.addr.val x.call.key evs ∧ ikit.fdsOk sf.fs⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
      ikit.identityAt self (ikit.saveUpdate ist0 x.call.addr.val x.call.key ans) ∗
      savePollOutAt b x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.savePollStack

/-- `is_trusted_identity` budget poll contract with `ikit.envOk` (and `ikit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitTrustPollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (fds : Bool := false) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitTrustPollSpec M A lim ikit ikitEnv fds)
    (match fds with
     | false => fun s => ikit.envOk s.fs.files
     | true => fun s => ikit.envOk s.fs.files ∧ ikit.fdsOk s.fs)

/-- `save_identity` budget poll contract with `ikit.envOk` (and `ikit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitSavePollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (fds : Bool := false) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitSavePollSpec M A lim ikit ikitEnv fds)
    (match fds with
     | false => fun s => ikit.envOk s.fs.files
     | true => fun s => ikit.envOk s.fs.files ∧ ikit.fdsOk s.fs)

end LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
