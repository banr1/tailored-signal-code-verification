/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKit

/-!
# Budget-Threaded `IdentitySelfStore` Contracts

`RustCliAllocBudget M` counterparts of `IdentitySelfStoreKit`, providing `retagIdentitySelfStore`,
`IdentitySelfStoreBudgetEnv`, step envelopes `KpStepEnv` and `RegIdStepEnv`, and total-correctness
shim and poll contracts (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget

open Arm64 ProofLib
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (IdentityStoreSpec IdentitySelfStoreSpec kpPollOutAt regIdPollOutAt withEnvPre)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv SeqEnv rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (retagIdentityStore)

/-- Retag phantom `RustAlloc` parameter on `IdentitySelfStoreSpec` (`rfl` on all projections). -/
abbrev retagIdentitySelfStore {A A' : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} (skit : IdentitySelfStoreSpec ikit) :
    IdentitySelfStoreSpec (retagIdentityStore (A' := A') ikit) where
  KpErr := skit.KpErr
  RegIdErr := skit.RegIdErr
  kpErr := skit.kpErr
  regIdErr := skit.regIdErr
  kpRel := skit.kpRel
  regIdRel := skit.regIdRel
  kpEvs := skit.kpEvs
  regIdEvs := skit.regIdEvs
  kpShimOff := skit.kpShimOff
  kpFutVtOff := skit.kpFutVtOff
  kpPollOff := skit.kpPollOff
  kpFutDropOff := skit.kpFutDropOff
  regIdShimOff := skit.regIdShimOff
  regIdFutVtOff := skit.regIdFutVtOff
  regIdPollOff := skit.regIdPollOff
  regIdFutDropOff := skit.regIdFutDropOff
  kpBoxSize := skit.kpBoxSize
  regIdBoxSize := skit.regIdBoxSize
  kpShimStack := skit.kpShimStack
  kpPollStack := skit.kpPollStack
  regIdShimStack := skit.regIdShimStack
  regIdPollStack := skit.regIdPollStack
  kpBoxAt := skit.kpBoxAt
  regIdBoxAt := skit.regIdBoxAt
  kpBoxAt_memRegion := skit.kpBoxAt_memRegion
  regIdBoxAt_memRegion := skit.regIdBoxAt_memRegion
  kpBoxSize_ne_zero := skit.kpBoxSize_ne_zero
  regIdBoxSize_ne_zero := skit.regIdBoxSize_ne_zero
  kpBoxSize_lt := skit.kpBoxSize_lt
  regIdBoxSize_lt := skit.regIdBoxSize_lt
  kpFutDrop_ne_zero := skit.kpFutDrop_ne_zero
  regIdFutDrop_ne_zero := skit.regIdFutDrop_ne_zero
  fdsOk := skit.fdsOk

/-- Store-specific poll allocation envelopes for `IdentitySelfStoreSpec`. -/
structure IdentitySelfStoreBudgetEnv {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} (skit : IdentitySelfStoreSpec ikit) where
  kpPollEnv : ikit.IdState → List AllocEvent → Prop
  regIdPollEnv : ikit.IdState → List AllocEvent → Prop

/-- `get_identity_key_pair` shim + poll + `Box` dealloc step envelope. -/
def KpStepEnv {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (ist0 : ikit.IdState) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv skit.kpBoxSize)
    (SeqEnv (senv.kpPollEnv ist0)
      (· = rustDeallocEvents skit.kpBoxSize 8))

/-- `get_local_registration_id` shim + poll + `Box` dealloc step envelope. -/
def RegIdStepEnv {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (ist0 : ikit.IdState) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv skit.regIdBoxSize)
    (SeqEnv (senv.regIdPollEnv ist0)
      (· = rustDeallocEvents skit.regIdBoxSize 8))

/-- Budget-threaded `get_identity_key_pair` shim contract. -/
def kitKpShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (skit : IdentitySelfStoreSpec ikit) (fds : Bool := false) :
    Spec (BitVec 64 × M.σ) where
  pre := fun (self, st) s =>
    ⌜match fds with
     | false => s.readReg64 .x0 = self ∧ FitsEnv M lim st (BoxAllocEnv skit.kpBoxSize)
     | true =>
       s.readReg64 .x0 = self ∧ FitsEnv M lim st (BoxAllocEnv skit.kpBoxSize) ∧ skit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp skit.kpShimStack
  post := fun (self, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + skit.kpFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv skit.kpBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + skit.kpFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv skit.kpBoxSize evs ∧ skit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) skit.kpBoxSize 8 ∗
      skit.kpBoxAt (sf.readReg64 .x0) self 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp skit.kpShimStack

/-- Budget-threaded `get_local_registration_id` shim contract. -/
def kitRegIdShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (skit : IdentitySelfStoreSpec ikit) (fds : Bool := false) :
    Spec (BitVec 64 × M.σ) where
  pre := fun (self, st) s =>
    ⌜match fds with
     | false => s.readReg64 .x0 = self ∧ FitsEnv M lim st (BoxAllocEnv skit.regIdBoxSize)
     | true =>
       s.readReg64 .x0 = self ∧ FitsEnv M lim st (BoxAllocEnv skit.regIdBoxSize) ∧ skit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp skit.regIdShimStack
  post := fun (self, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + skit.regIdFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv skit.regIdBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + skit.regIdFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv skit.regIdBoxSize evs ∧ skit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) skit.regIdBoxSize 8 ∗
      skit.regIdBoxAt (sf.readReg64 .x0) self 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp skit.regIdShimStack

/-- Budget-threaded `get_identity_key_pair` poll contract. -/
def kitKpPollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (fds : Bool := false) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState × M.σ) where
  pre := fun (fut, out, self, ist0, st) s =>
    ⌜s.readReg64 .x0 = fut ∧ s.readReg64 .x8 = out ∧
      FitsEnv M lim st (senv.kpPollEnv ist0)⌝ ∗
      skit.kpBoxAt fut self 0#8 ∗
      ikit.identityAt self ist0 ∗
      memRegion out 72 ∗
      A.pool lim st s ∗ stackAt s.sp skit.kpPollStack
  post := fun (fut, out, self, ist0, st) s0 sf =>
    ∃∗ ans : Except skit.KpErr IdentityKeyPair, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         skit.kpRel ist0 ans ∧ sf.trace = s0.trace ++ skit.kpEvs ans ∧
           senv.kpPollEnv ist0 evs
       | true =>
         skit.kpRel ist0 ans ∧ sf.trace = s0.trace ++ skit.kpEvs ans ∧
           senv.kpPollEnv ist0 evs ∧ skit.fdsOk sf.fs⌝ ∗
      skit.kpBoxAt fut self 1#8 ∗
      ikit.identityAt self ist0 ∗
      kpPollOutAt skit out ans ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp skit.kpPollStack

/-- Budget-threaded `get_local_registration_id` poll contract. -/
def kitRegIdPollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (fds : Bool := false) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState × M.σ) where
  pre := fun (fut, out, self, ist0, st) s =>
    ⌜s.readReg64 .x0 = fut ∧ s.readReg64 .x8 = out ∧
      FitsEnv M lim st (senv.regIdPollEnv ist0)⌝ ∗
      skit.regIdBoxAt fut self 0#8 ∗
      ikit.identityAt self ist0 ∗
      memRegion out 48 ∗
      A.pool lim st s ∗ stackAt s.sp skit.regIdPollStack
  post := fun (fut, out, self, ist0, st) s0 sf =>
    ∃∗ ans : Except skit.RegIdErr (BitVec 32), ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         skit.regIdRel ist0 ans ∧ sf.trace = s0.trace ++ skit.regIdEvs ans ∧
           senv.regIdPollEnv ist0 evs
       | true =>
         skit.regIdRel ist0 ans ∧ sf.trace = s0.trace ++ skit.regIdEvs ans ∧
           senv.regIdPollEnv ist0 evs ∧ skit.fdsOk sf.fs⌝ ∗
      skit.regIdBoxAt fut self 1#8 ∗
      ikit.identityAt self ist0 ∗
      regIdPollOutAt skit out ans ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp skit.regIdPollStack

/-- `get_identity_key_pair` budget poll contract with `ikit.envOk` (and `skit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitKpPollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (fds : Bool := false) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitKpPollSpec M A lim skit senv fds)
    (match fds with
     | false => fun s => ikit.envOk s.fs.files
     | true => fun s => ikit.envOk s.fs.files ∧ skit.fdsOk s.fs)

/-- `get_local_registration_id` budget poll contract with `ikit.envOk` (and `skit.fdsOk` when
    `fds = true`) on the entry state. -/
abbrev kitRegIdPollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} {ikit : IdentityStoreSpec A.repAlloc b}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (fds : Bool := false) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitRegIdPollSpec M A lim skit senv fds)
    (match fds with
     | false => fun s => ikit.envOk s.fs.files
     | true => fun s => ikit.envOk s.fs.files ∧ skit.fdsOk s.fs)

end LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
