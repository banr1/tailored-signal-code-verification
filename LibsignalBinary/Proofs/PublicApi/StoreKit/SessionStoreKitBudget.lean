/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKit

/-!
# Budget-Threaded `SessionStore` Contract

`RustCliAllocBudget`-threaded `SessionStore` contracts: `PublicApiHooksNoSessionStore`,
`SessionStoreBudgetEnv`, `LoadStepEnv`, `StoreStepEnv`, and non-panicking/non-OOM shim and poll
specifications for `load_session` and `store_session`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal sessionRecordAt)
open CryptoVerification.LibsignalPublicApi
  (IdentityCall isTrustedHookName saveIdentityHookName timeAddHookName durationSinceHookName
   stringCloneHookName)
open CryptoVerification.LibsignalPublicApi.StoreSession (StoreShimCall StorePollCall)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LoadShimCall SessionStoreSpec storePollOutAt withEnvPre)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv SeqEnv rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (TripleRatchetHooksBudget IsTrustedEnv SaveIdentityEnv PublicApiStoreEnv
   isTrustedBudgetSpec saveIdentityBudgetSpec
   timeAddBudgetSpec durationSinceBudgetSpec PublicApiHooksBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)

/-- Budget-threaded hook bundle omitting `load_session` and `store_session` hooks
    (retaining `isTrusted` and `saveIdentity` hooks). -/
structure PublicApiHooksNoSessionStore [CryptoVerification.LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (abs : String → Option (State → State))
    (trustEnv : IdentityCall → CryptoGames.LibsignalSessionApi.Direction → List AllocEvent → Prop :=
      IsTrustedEnv)
    (saveEnv : IdentityCall → List AllocEvent → Prop := SaveIdentityEnv) : Prop
    extends TripleRatchetHooksBudget C M A lim S abs where
  isTrusted : HookSat abs isTrustedHookName (isTrustedBudgetSpec M A lim trustEnv)
  saveIdentity : HookSat abs saveIdentityHookName (saveIdentityBudgetSpec M A lim saveEnv)
  timeAdd : HookSat abs timeAddHookName timeAddBudgetSpec
  durationSince : HookSat abs durationSinceHookName durationSinceBudgetSpec
  stringClone : HookSat abs stringCloneHookName (stringCloneBudgetSpec M A lim)

theorem PublicApiHooksBudget.toNoSessionStore [CryptoVerification.LibsignalPlacement]
    {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {storeEnv : PublicApiStoreEnv}
    (h : PublicApiHooksBudget C M A lim S encRecord abs storeEnv) :
    PublicApiHooksNoSessionStore C M A lim S abs storeEnv.trustEnv storeEnv.saveEnv where
  toTripleRatchetHooksBudget := h.toTripleRatchetHooksBudget
  isTrusted := h.isTrusted
  saveIdentity := h.saveIdentity
  timeAdd := h.timeAdd
  durationSince := h.durationSince
  stringClone := h.stringClone

/-- Retag phantom `RustAlloc` parameter on `SessionStoreSpec` (`rfl` on all projections). -/
abbrev retagSessionStore {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) : SessionStoreSpec A' b :=
  { kit with }

/-- Store-specific poll allocation envelopes for `SessionStoreSpec`. -/
structure SessionStoreBudgetEnv {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) where
  loadPollEnv : kit.StoreState → AddrVal → List AllocEvent → Prop
  storePollEnv : kit.StoreState → AddrVal → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop

/-- `load_session` shim + poll + `Box` dealloc step envelope. -/
def LoadStepEnv {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (rem : AddrVal) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.loadBoxSize)
    (SeqEnv (kitEnv.loadPollEnv st0 rem)
      (· = rustDeallocEvents kit.loadBoxSize 8))

/-- `store_session` shim + poll + `Box` dealloc step envelope. -/
def StoreStepEnv {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (rem : AddrVal) (rec : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv kit.storeBoxSize)
    (SeqEnv (kitEnv.storePollEnv st0 rem rec)
      (· = rustDeallocEvents kit.storeBoxSize 8))

/-- Budget-threaded `load_session` shim contract parameterized by
    `kit : SessionStoreSpec A.repAlloc b`. -/
def kitLoadShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SessionStoreSpec A.repAlloc b) (fds : Bool := false) :
    Spec (LoadShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜match fds with
     | false =>
       s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧
         FitsEnv M lim st (BoxAllocEnv kit.loadBoxSize)
     | true =>
       s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧
         FitsEnv M lim st (BoxAllocEnv kit.loadBoxSize) ∧ kit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp kit.loadShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + kit.loadFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.loadBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + kit.loadFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.loadBoxSize evs ∧ kit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) kit.loadBoxSize 8 ∗
      kit.loadBoxAt (sf.readReg64 .x0) x.self x.addrA 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.loadShimStack

/-- Budget-threaded `store_session` shim contract parameterized by
    `kit : SessionStoreSpec A.repAlloc b`. -/
def kitStoreShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SessionStoreSpec A.repAlloc b) (fds : Bool := false) :
    Spec (StoreShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜match fds with
     | false =>
       s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.recA ∧
         FitsEnv M lim st (BoxAllocEnv kit.storeBoxSize)
     | true =>
       s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.recA ∧
         FitsEnv M lim st (BoxAllocEnv kit.storeBoxSize) ∧ kit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp kit.storeShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + kit.storeFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.storeBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + kit.storeFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.storeBoxSize evs ∧ kit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) kit.storeBoxSize 8 ∗
      kit.storeBoxAt (sf.readReg64 .x0) x.self x.addrA x.recA 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.storeShimStack

/-- Budget-threaded `store_session` poll contract parameterized by
    `kit : SessionStoreSpec A.repAlloc b` and `kitEnv : SessionStoreBudgetEnv kit`. -/
def kitStorePollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SessionStoreSpec A.repAlloc b)
    (kitEnv : SessionStoreBudgetEnv kit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (fds : Bool := false) :
    Spec (StorePollCall × BitVec 64 × kit.StoreState × M.σ) where
  pre := fun (x, self, st0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ kit.RecOk x.call.record ∧
      kit.addrOk x.call.addr.val ∧
      FitsEnv M lim st (kitEnv.storePollEnv st0 x.call.addr.val x.call.record)⌝ ∗
      kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗
      kit.storeAt self st0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      sessionRecordAt A.repAlloc x.call.recA x.call.g x.call.record ∗
      A.pool lim st s ∗ stackAt s.sp kit.storePollStack
  post := fun (x, self, st0, st) s0 sf =>
    ∃∗ ans : Except Unit Unit, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         kit.storeRel st0 x.call.addr.val x.call.record ans ∧
           sf.trace = s0.trace ++ kit.storeEvs encRecord x.call.addr.val x.call.record ans ∧
           kitEnv.storePollEnv st0 x.call.addr.val x.call.record evs
       | true =>
         kit.storeRel st0 x.call.addr.val x.call.record ans ∧
           sf.trace = s0.trace ++ kit.storeEvs encRecord x.call.addr.val x.call.record ans ∧
           kitEnv.storePollEnv st0 x.call.addr.val x.call.record evs ∧ kit.fdsOk sf.fs⌝ ∗
      kit.storeBoxAt x.fut self x.call.addrA x.call.recA 1#8 ∗
      kit.storeAt self (kit.storeUpdate st0 x.call.addr.val x.call.record ans) ∗
      storePollOutAt b x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      sessionRecordAt A.repAlloc x.call.recA x.call.g x.call.record ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.storePollStack

/-- `store_session` budget poll contract with `kit.envOk` (and `kit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitStorePollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SessionStoreSpec A.repAlloc b)
    (kitEnv : SessionStoreBudgetEnv kit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (fds : Bool := false) :
    Spec (StorePollCall × BitVec 64 × kit.StoreState × M.σ) :=
  withEnvPre (kitStorePollSpec M A lim kit kitEnv encRecord fds)
    (match fds with
     | false => fun s => kit.envOk s.fs.files
     | true => fun s => kit.envOk s.fs.files ∧ kit.fdsOk s.fs)

end LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
