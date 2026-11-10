/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Store-Kit Contracts

`RustCliAllocBudget`-threaded relocatable poll contracts (`b := 0#64`), cross-block
`futDropBudgetSpec` transfer lemmas, and caller-block-polymorphic `subroutine_ok` bundles across
all six store-kit traits.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSessionApi (Direction IdentityChange SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (directionByte sessionRecordAt)
open CryptoVerification.LibsignalPublicApi.StoreSession (StorePollCall)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LoadPollCall IdentityPollCall SessionStoreSpec IdentityStoreSpec
   PreKeyStoreSpec SignedPreKeyStoreSpec KyberPreKeyStoreSpec IdentitySelfStoreSpec
   withEnvPre withLsRoCl ls_subroutine_ok_rocl_of_plain withLsLogOff
   loadPollPlacedOutAtS storePollPlacedOutAt trustPollPlacedOutAt savePollPlacedOutAt)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (futDropBudgetSpec futDropBudgetSpecFs subroutine_ok_futDropBudgetSpec_of_fs
   PreKeyStoreBudgetEnv
   kitPreKeyGetShimSpec kitPreKeyRemoveShimSpec
   kitPreKeyGetPollSpec kitPreKeyRemovePollSpec
   kitPreKeyGetPollSpecE kitPreKeyRemovePollSpecE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
  (SignedPreKeyStoreBudgetEnv kitSpkGetShimSpec kitSpkGetPollSpec kitSpkGetPollSpecE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv kitKpkGetShimSpec kitKpkMarkShimSpec
   kitKpkGetPollSpec kitKpkMarkPollSpec
   kitKpkGetPollSpecE kitKpkMarkPollSpecE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv kitLoadShimSpec kitStoreShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv kitTrustShimSpec kitSaveShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
  (IdentitySelfStoreBudgetEnv kitKpShimSpec kitRegIdShimSpec
   kitKpPollSpec kitRegIdPollSpec kitKpPollSpecE kitRegIdPollSpecE)

/-! ## 1. Cross-Block `futDropBudgetSpec` Transfer -/

/-- Cross-block `futDropBudgetSpec` transfer across any two blocks `j` and `i`. -/
theorem ls_futDrop_ok_of_block [LibsignalPlacement]
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {fdsOk : FsState → Prop} {fds : Bool}
    (hcallee : subroutine_ok calleeProg entry (futDropBudgetSpec fdsOk fds))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsRoCl lsmpl (futDropBudgetSpec fdsOk fds)) :=
  ls_subroutine_ok_rocl_of_plain (callerProg := callerProg) hcallee hi hj hj_unmut

/-- Cross-block `futDropBudgetSpec` transfer from a `futDropBudgetSpecFs` (`sf.fs = s0.fs`) proof,
    instantiable at any `fdsOk` and `fds`. -/
theorem ls_futDrop_ok_of_block_fs [LibsignalPlacement]
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64}
    (hcallee : subroutine_ok calleeProg entry futDropBudgetSpecFs)
    (fdsOk : FsState → Prop) (fds : Bool)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsRoCl lsmpl (futDropBudgetSpec fdsOk fds)) :=
  ls_futDrop_ok_of_block
    (subroutine_ok_futDropBudgetSpec_of_fs hcallee fdsOk fds) hi hj hj_unmut

/-! ## 2. Generic Budget-Threaded Placed Poll Contracts (`b := 0#64`) -/

/-- Relocatable budget-threaded `load_session` poll contract parameterized by
    `kit : SessionStoreSpec A.repAlloc 0#64` and `kitEnv : SessionStoreBudgetEnv kit`. -/
def kitLoadPollPlacedSpecS (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (fds : Bool := false) :
    Spec (LoadPollCall × BitVec 64 × kit.StoreState × M.σ) where
  pre := fun (x, self, st0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ kit.addrOk x.addr.val ∧
      FitsEnv M lim st (kitEnv.loadPollEnv st0 x.addr.val)⌝ ∗
      kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st0 ∗ memRegion x.out 368 ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗ A.pool lim st s ∗ stackAt s.sp kit.loadPollStack
  post := fun (x, self, st0, st) s0 sf =>
    ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))), ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         kit.loadRel st0 x.addr.val ans ∧
           sf.trace = s0.trace ++ kit.loadEvs encRecord x.addr.val ans ∧
           kitEnv.loadPollEnv st0 x.addr.val evs
       | true =>
         kit.loadRel st0 x.addr.val ans ∧
           sf.trace = s0.trace ++ kit.loadEvs encRecord x.addr.val ans ∧
           kitEnv.loadPollEnv st0 x.addr.val evs ∧ kit.fdsOk sf.fs⌝ ∗
      kit.loadBoxAt x.fut self x.addrA 1#8 ∗ kit.storeAt self st0 ∗
      loadPollPlacedOutAtS Scope A.repAlloc x.out ans ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.loadPollStack

abbrev kitLoadPollPlacedSpecSE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (fds : Bool := false) :
    Spec (LoadPollCall × BitVec 64 × kit.StoreState × M.σ) :=
  withEnvPre (kitLoadPollPlacedSpecS M A lim kit kitEnv Scope encRecord fds)
    (match fds with
     | false => fun s => kit.envOk s.fs.files
     | true => fun s => kit.envOk s.fs.files ∧ kit.fdsOk s.fs)

/-- Relocatable budget-threaded `store_session` poll contract parameterized by
    `kit : SessionStoreSpec A.repAlloc 0#64` and `kitEnv : SessionStoreBudgetEnv kit`. -/
def kitStorePollPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
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
      storePollPlacedOutAt x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      sessionRecordAt A.repAlloc x.call.recA x.call.g x.call.record ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.storePollStack

abbrev kitStorePollPlacedSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (fds : Bool := false) :
    Spec (StorePollCall × BitVec 64 × kit.StoreState × M.σ) :=
  withEnvPre (kitStorePollPlacedSpec M A lim kit kitEnv encRecord fds)
    (match fds with
     | false => fun s => kit.envOk s.fs.files
     | true => fun s => kit.envOk s.fs.files ∧ kit.fdsOk s.fs)

/-- Relocatable budget-threaded `is_trusted_identity` poll contract parameterized by
    `ikit : IdentityStoreSpec A.repAlloc 0#64` and `ikitEnv : IdentityStoreBudgetEnv ikit`. -/
def kitTrustPollPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (fds : Bool := false) :
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
      trustPollPlacedOutAt x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.trustPollStack

abbrev kitTrustPollPlacedSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (fds : Bool := false) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitTrustPollPlacedSpec M A lim ikit ikitEnv fds)
    (match fds with
     | false => fun s => ikit.envOk s.fs.files
     | true => fun s => ikit.envOk s.fs.files ∧ ikit.fdsOk s.fs)

abbrev kitTrustPollPlacedSpecI [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (fds : Bool := false) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState × M.σ) :=
  withLsLogOff (kitTrustPollPlacedSpecE M A lim ikit ikitEnv fds)

/-- Relocatable budget-threaded `save_identity` poll contract parameterized by
    `ikit : IdentityStoreSpec A.repAlloc 0#64` and `ikitEnv : IdentityStoreBudgetEnv ikit`. -/
def kitSavePollPlacedSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (fds : Bool := false) :
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
      savePollPlacedOutAt x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.savePollStack

abbrev kitSavePollPlacedSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (fds : Bool := false) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitSavePollPlacedSpec M A lim ikit ikitEnv fds)
    (match fds with
     | false => fun s => ikit.envOk s.fs.files
     | true => fun s => ikit.envOk s.fs.files ∧ ikit.fdsOk s.fs)

abbrev kitSavePollPlacedSpecI [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (fds : Bool := false) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) :=
  withLsLogOff (kitSavePollPlacedSpecE M A lim ikit ikitEnv fds)

abbrev kitKpPollPlacedSpecI [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (fds : Bool := false) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState × M.σ) :=
  withLsLogOff (kitKpPollSpecE M A lim skit senv fds)

abbrev kitRegIdPollPlacedSpecI [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (fds : Bool := false) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState × M.σ) :=
  withLsLogOff (kitRegIdPollSpecE M A lim skit senv fds)

/-! ## 3. Caller-Block-Polymorphic `subroutine_ok` Bundles (`b := 0#64`) -/

/-- Relocatable budget-threaded `SessionOnlyKitPlacedOkSE` (`callerBlk < 619`). -/
structure SessionOnlyKitPlacedOkSE [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (fds : Bool := false) : Prop where
  loadShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadShimOff)
      (withLsRoCl lsmpl (kitLoadShimSpec M A lim kit fds))
  loadPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadPollOff)
      (withLsRoCl lsmpl (kitLoadPollPlacedSpecSE M A lim kit kitEnv Scope encRecord fds))
  loadFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk fds))
  storeShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storeShimOff)
      (withLsRoCl lsmpl (kitStoreShimSpec M A lim kit fds))
  storePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storePollOff)
      (withLsRoCl lsmpl (kitStorePollPlacedSpecE M A lim kit kitEnv encRecord fds))
  storeFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storeFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk fds))

abbrev SessionOnlyKitPlacedOkSEFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H true

/-- Relocatable budget-threaded `IdentityStoreKitPlacedOkI` (`callerBlk < 619`). -/
structure IdentityStoreKitPlacedOkI [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (H : LibsignalHooks) (fds : Bool := false) : Prop where
  trustShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustShimOff)
      (withLsRoCl lsmpl (kitTrustShimSpec M A lim ikit fds))
  trustPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustPollOff)
      (withLsRoCl lsmpl (kitTrustPollPlacedSpecI M A lim ikit ikitEnv fds))
  trustFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec ikit.fdsOk fds))
  saveShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.saveShimOff)
      (withLsRoCl lsmpl (kitSaveShimSpec M A lim ikit fds))
  savePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.savePollOff)
      (withLsRoCl lsmpl (kitSavePollPlacedSpecI M A lim ikit ikitEnv fds))
  saveFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.saveFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec ikit.fdsOk fds))

abbrev IdentityStoreKitPlacedOkIFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (H : LibsignalHooks) : Prop :=
  IdentityStoreKitPlacedOkI A lim ikit ikitEnv H true

/-- Relocatable budget-threaded `PreKeyStoreKitPlacedOk` (`get_pre_key` and `remove_pre_key`). -/
structure PreKeyStoreKitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : PreKeyStoreSpec A.repAlloc 0#64) (kitEnv : PreKeyStoreBudgetEnv kit)
    (H : LibsignalHooks) (fds : Bool := false) : Prop where
  getShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getShimOff)
      (withLsRoCl lsmpl (kitPreKeyGetShimSpec M A lim kit fds))
  getPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getPollOff)
      (withLsRoCl lsmpl (kitPreKeyGetPollSpecE M A lim kit kitEnv fds))
  getFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk fds))
  removeShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.removeShimOff)
      (withLsRoCl lsmpl (kitPreKeyRemoveShimSpec M A lim kit fds))
  removePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.removePollOff)
      (withLsRoCl lsmpl (kitPreKeyRemovePollSpecE M A lim kit kitEnv fds))
  removeFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.removeFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk fds))

abbrev PreKeyStoreKitPlacedOkFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : PreKeyStoreSpec A.repAlloc 0#64) (kitEnv : PreKeyStoreBudgetEnv kit)
    (H : LibsignalHooks) : Prop :=
  PreKeyStoreKitPlacedOk A lim kit kitEnv H true

/-- Relocatable budget-threaded `SignedPreKeyStoreKitPlacedOk` (`get_signed_pre_key`). -/
structure SignedPreKeyStoreKitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SignedPreKeyStoreSpec A.repAlloc 0#64) (kitEnv : SignedPreKeyStoreBudgetEnv kit)
    (H : LibsignalHooks) (fds : Bool := false) : Prop where
  getShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getShimOff)
      (withLsRoCl lsmpl (kitSpkGetShimSpec M A lim kit fds))
  getPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getPollOff)
      (withLsRoCl lsmpl (kitSpkGetPollSpecE M A lim kit kitEnv fds))
  getFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk fds))

abbrev SignedPreKeyStoreKitPlacedOkFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SignedPreKeyStoreSpec A.repAlloc 0#64) (kitEnv : SignedPreKeyStoreBudgetEnv kit)
    (H : LibsignalHooks) : Prop :=
  SignedPreKeyStoreKitPlacedOk A lim kit kitEnv H true

/-- Relocatable budget-threaded `KyberPreKeyStoreKitPlacedOk` (`get_kyber_pre_key` and
    `mark_kyber_pre_key_used`). -/
structure KyberPreKeyStoreKitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (H : LibsignalHooks) (fds : Bool := false) : Prop where
  getShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getShimOff)
      (withLsRoCl lsmpl (kitKpkGetShimSpec M A lim kit fds))
  getPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getPollOff)
      (withLsRoCl lsmpl (kitKpkGetPollSpecE M A lim kit kitEnv fds))
  getFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk fds))
  markShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markShimOff)
      (withLsRoCl lsmpl (kitKpkMarkShimSpec M A lim kit fds))
  markPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markPollOff)
      (withLsRoCl lsmpl (kitKpkMarkPollSpecE M A lim kit kitEnv fds))
  markFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk fds))

abbrev KyberPreKeyStoreKitPlacedOkFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kitEnv : KyberPreKeyStoreBudgetEnv kit)
    (H : LibsignalHooks) : Prop :=
  KyberPreKeyStoreKitPlacedOk A lim kit kitEnv H true

/-- Relocatable budget-threaded `IdentitySelfStoreKitPlacedOkI` (`get_identity_key_pair` and
    `get_local_registration_id`). -/
structure IdentitySelfStoreKitPlacedOkI [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (H : LibsignalHooks) (fds : Bool := false) : Prop where
  kpShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.kpShimOff)
      (withLsRoCl lsmpl (kitKpShimSpec M A lim skit fds))
  kpPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.kpPollOff)
      (withLsRoCl lsmpl (kitKpPollPlacedSpecI M A lim skit senv fds))
  kpFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.kpFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec skit.fdsOk fds))
  regIdShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.regIdShimOff)
      (withLsRoCl lsmpl (kitRegIdShimSpec M A lim skit fds))
  regIdPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.regIdPollOff)
      (withLsRoCl lsmpl (kitRegIdPollPlacedSpecI M A lim skit senv fds))
  regIdFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.regIdFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec skit.fdsOk fds))

abbrev IdentitySelfStoreKitPlacedOkIFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (H : LibsignalHooks) : Prop :=
  IdentitySelfStoreKitPlacedOkI A lim ikit skit senv H true

/-! ## 4. Trivial-`fdsOk` Upgrade Bridges (`fds = false` → `fds = true` for Non-CLI Kits) -/

private theorem eq_true_of_fdsOk {fdsOk : FsState → Prop} (htriv : ∀ fs, fdsOk fs) :
    fdsOk = fun _ => True :=
  funext fun fs => propext ⟨fun _ => trivial, fun _ => htriv fs⟩

/-- Any `SessionOnlyKitPlacedOkSE` whose `kit.fdsOk` always holds (including all non-CLI kits
    using the default `fdsOk := fun _ => True`) upgrades automatically to `fds = true`. -/
theorem SessionOnlyKitPlacedOkSE.toFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (h : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H false)
    (htriv : ∀ fs, kit.fdsOk fs := by intro _; trivial) :
    SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H true where
  loadShim hblk := by
    simpa only [kitLoadShimSpec, eq_true_of_fdsOk htriv, and_true] using h.loadShim hblk
  loadPoll hblk := by
    simpa only [kitLoadPollPlacedSpecSE, kitLoadPollPlacedSpecS, eq_true_of_fdsOk htriv,
      and_true] using h.loadPoll hblk
  loadFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.loadFutDrop hblk
  storeShim hblk := by
    simpa only [kitStoreShimSpec, eq_true_of_fdsOk htriv, and_true] using h.storeShim hblk
  storePoll hblk := by
    simpa only [kitStorePollPlacedSpecE, kitStorePollPlacedSpec, eq_true_of_fdsOk htriv,
      and_true] using h.storePoll hblk
  storeFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.storeFutDrop hblk

/-- Any `IdentityStoreKitPlacedOkI` whose `ikit.fdsOk` always holds upgrades automatically to
    `fds = true`. -/
theorem IdentityStoreKitPlacedOkI.toFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {H : LibsignalHooks}
    (h : IdentityStoreKitPlacedOkI A lim ikit ikitEnv H false)
    (htriv : ∀ fs, ikit.fdsOk fs := by intro _; trivial) :
    IdentityStoreKitPlacedOkI A lim ikit ikitEnv H true where
  trustShim hblk := by
    simpa only [kitTrustShimSpec, eq_true_of_fdsOk htriv, and_true] using h.trustShim hblk
  trustPoll hblk := by
    simpa only [kitTrustPollPlacedSpecI, kitTrustPollPlacedSpecE, kitTrustPollPlacedSpec,
      eq_true_of_fdsOk htriv, and_true] using h.trustPoll hblk
  trustFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.trustFutDrop hblk
  saveShim hblk := by
    simpa only [kitSaveShimSpec, eq_true_of_fdsOk htriv, and_true] using h.saveShim hblk
  savePoll hblk := by
    simpa only [kitSavePollPlacedSpecI, kitSavePollPlacedSpecE, kitSavePollPlacedSpec,
      eq_true_of_fdsOk htriv, and_true] using h.savePoll hblk
  saveFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.saveFutDrop hblk

/-- Any `PreKeyStoreKitPlacedOk` whose `kit.fdsOk` always holds upgrades automatically to
    `fds = true`. -/
theorem PreKeyStoreKitPlacedOk.toFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : PreKeyStoreSpec A.repAlloc 0#64} {kitEnv : PreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks}
    (h : PreKeyStoreKitPlacedOk A lim kit kitEnv H false)
    (htriv : ∀ fs, kit.fdsOk fs := by intro _; trivial) :
    PreKeyStoreKitPlacedOk A lim kit kitEnv H true where
  getShim hblk := by
    simpa only [kitPreKeyGetShimSpec, eq_true_of_fdsOk htriv, and_true] using h.getShim hblk
  getPoll hblk := by
    simpa only [kitPreKeyGetPollSpecE, kitPreKeyGetPollSpec, eq_true_of_fdsOk htriv,
      and_true] using h.getPoll hblk
  getFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.getFutDrop hblk
  removeShim hblk := by
    simpa only [kitPreKeyRemoveShimSpec, eq_true_of_fdsOk htriv, and_true] using h.removeShim hblk
  removePoll hblk := by
    simpa only [kitPreKeyRemovePollSpecE, kitPreKeyRemovePollSpec, eq_true_of_fdsOk htriv,
      and_true] using h.removePoll hblk
  removeFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.removeFutDrop hblk

/-- Any `SignedPreKeyStoreKitPlacedOk` whose `kit.fdsOk` always holds upgrades automatically to
    `fds = true`. -/
theorem SignedPreKeyStoreKitPlacedOk.toFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SignedPreKeyStoreSpec A.repAlloc 0#64} {kitEnv : SignedPreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks}
    (h : SignedPreKeyStoreKitPlacedOk A lim kit kitEnv H false)
    (htriv : ∀ fs, kit.fdsOk fs := by intro _; trivial) :
    SignedPreKeyStoreKitPlacedOk A lim kit kitEnv H true where
  getShim hblk := by
    simpa only [kitSpkGetShimSpec, eq_true_of_fdsOk htriv, and_true] using h.getShim hblk
  getPoll hblk := by
    simpa only [kitSpkGetPollSpecE, kitSpkGetPollSpec, eq_true_of_fdsOk htriv, and_true] using
      h.getPoll hblk
  getFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.getFutDrop hblk

/-- Any `KyberPreKeyStoreKitPlacedOk` whose `kit.fdsOk` always holds upgrades automatically to
    `fds = true`. -/
theorem KyberPreKeyStoreKitPlacedOk.toFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : KyberPreKeyStoreSpec A.repAlloc 0#64} {kitEnv : KyberPreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks}
    (h : KyberPreKeyStoreKitPlacedOk A lim kit kitEnv H false)
    (htriv : ∀ fs, kit.fdsOk fs := by intro _; trivial) :
    KyberPreKeyStoreKitPlacedOk A lim kit kitEnv H true where
  getShim hblk := by
    simpa only [kitKpkGetShimSpec, eq_true_of_fdsOk htriv, and_true] using h.getShim hblk
  getPoll hblk := by
    simpa only [kitKpkGetPollSpecE, kitKpkGetPollSpec, eq_true_of_fdsOk htriv, and_true] using
      h.getPoll hblk
  getFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.getFutDrop hblk
  markShim hblk := by
    simpa only [kitKpkMarkShimSpec, eq_true_of_fdsOk htriv, and_true] using h.markShim hblk
  markPoll hblk := by
    simpa only [kitKpkMarkPollSpecE, kitKpkMarkPollSpec, eq_true_of_fdsOk htriv, and_true] using
      h.markPoll hblk
  markFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.markFutDrop hblk

/-- Any `IdentitySelfStoreKitPlacedOkI` whose `skit.fdsOk` always holds upgrades automatically to
    `fds = true`. -/
theorem IdentitySelfStoreKitPlacedOkI.toFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {skit : IdentitySelfStoreSpec ikit} {senv : IdentitySelfStoreBudgetEnv skit}
    {H : LibsignalHooks}
    (h : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv H false)
    (htriv : ∀ fs, skit.fdsOk fs := by intro _; trivial) :
    IdentitySelfStoreKitPlacedOkI A lim ikit skit senv H true where
  kpShim hblk := by
    simpa only [kitKpShimSpec, eq_true_of_fdsOk htriv, and_true] using h.kpShim hblk
  kpPoll hblk := by
    simpa only [kitKpPollPlacedSpecI, kitKpPollSpecE, kitKpPollSpec, eq_true_of_fdsOk htriv,
      and_true] using h.kpPoll hblk
  kpFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.kpFutDrop hblk
  regIdShim hblk := by
    simpa only [kitRegIdShimSpec, eq_true_of_fdsOk htriv, and_true] using h.regIdShim hblk
  regIdPoll hblk := by
    simpa only [kitRegIdPollPlacedSpecI, kitRegIdPollSpecE, kitRegIdPollSpec,
      eq_true_of_fdsOk htriv, and_true] using h.regIdPoll hblk
  regIdFutDrop hblk := by
    simpa only [futDropBudgetSpec, eq_true_of_fdsOk htriv, imp_self, and_true] using
      h.regIdFutDrop hblk

end LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
