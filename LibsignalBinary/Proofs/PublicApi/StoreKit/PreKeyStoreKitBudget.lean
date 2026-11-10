/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit

/-!
# Budget-Threaded `PreKeyStore` Contract

`RustCliAllocBudget`-threaded `PreKeyStore` contracts: shared boxed-future allocation/deallocation
envelopes (`BoxAllocEnv`, `BoxDeallocEnv`), `futDropBudgetSpec`, `PreKeyStoreBudgetEnv`, and
non-panicking/non-OOM shim and poll specifications for `get_pre_key` and `remove_pre_key`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FreeOnlyEvs VmPreserved
   rustAllocEvents rustDeallocEvents)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.RecordCodecs (PreKeyRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (PreKeyShimCall PreKeyPollCall PreKeyStoreSpec preKeyGetPollOutAt preKeyRemovePollOutAt
   withEnvPre)

/-! ## Shared Boxed-Future Envelopes & `futDropBudgetSpec` -/

/-- Concrete allocation envelope for boxed store future shims
    (`boxSize = 0` or `rustAllocEvents boxSize 8`). -/
def BoxAllocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  (boxSize = 0 ∧ evs = []) ∨
  (0 < boxSize ∧ evs = rustAllocEvents boxSize 8)

/-- Concrete deallocation envelope for boxed store futures
    (`boxSize = 0` or `rustDeallocEvents boxSize 8`). -/
def BoxDeallocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  (boxSize = 0 ∧ evs = []) ∨
  (0 < boxSize ∧ evs = rustDeallocEvents boxSize 8)

theorem BoxDeallocEnv.freeOnly {boxSize : Nat} {evs : List AllocEvent}
    (h : BoxDeallocEnv boxSize evs) : FreeOnlyEvs evs := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 8 boxSize

/-- Budget-threaded no-op future drop (`0` allocations, preserves `VmPreserved`; when `fds = true`,
    also preserves `fdsOk` from `s0.fs` to `sf.fs`). -/
def futDropBudgetSpec (fdsOk : FsState → Prop := fun _ => True)
    (fds : Bool := false) : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜match fds with
     | false => sf.trace = s0.trace ∧ VmPreserved s0 sf
     | true => sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ (fdsOk s0.fs → fdsOk sf.fs)⌝

/-- Stronger `futDropBudgetSpec` carrying `sf.fs = s0.fs` (upgrades to `futDropBudgetSpec fdsOk fds`
    for every `fdsOk` and `fds`). -/
def futDropBudgetSpecFs : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf ∧ sf.fs = s0.fs⌝

theorem subroutine_ok_futDropBudgetSpec_of_fs {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry futDropBudgetSpecFs)
    (fdsOk : FsState → Prop) (fds : Bool) :
    subroutine_ok prog entry (futDropBudgetSpec fdsOk fds) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ s0 sf hq => ?_)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  dsimp only [futDropBudgetSpecFs, futDropBudgetSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq ⊢
  obtain ⟨⟨htr, hvm, hfs⟩, hR⟩ := hq
  cases fds
  · exact ⟨⟨htr, hvm⟩, hR⟩
  · exact ⟨⟨htr, hvm, fun hf0 => hfs ▸ hf0⟩, hR⟩

theorem subroutine_ok_futDropBudgetSpec_true_of_false {prog : Program} {entry : BitVec 64}
    {fdsOk : FsState → Prop}
    (h : subroutine_ok prog entry (futDropBudgetSpec fdsOk false))
    (htriv : ∀ fs, fdsOk fs := by intro _; trivial) :
    subroutine_ok prog entry (futDropBudgetSpec fdsOk true) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ s0 sf hq => ?_)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  dsimp only [futDropBudgetSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq ⊢
  obtain ⟨⟨htr, hvm⟩, hR⟩ := hq
  exact ⟨⟨htr, hvm, fun _ => htriv sf.fs⟩, hR⟩

/-! ## `PreKeyStore` Retag, Poll Envelopes, and Budget-Threaded Contracts -/

/-- Retag phantom `RustAlloc` parameter on `PreKeyStoreSpec` (`rfl` on all projections). -/
abbrev retagPreKeyStore {A A' : RustAlloc} {b : BitVec 64}
    (kit : PreKeyStoreSpec A b) : PreKeyStoreSpec A' b :=
  { kit with }

/-- Store-specific poll allocation envelopes for `PreKeyStoreSpec`. -/
structure PreKeyStoreBudgetEnv {A : RustAlloc} {b : BitVec 64}
    (kit : PreKeyStoreSpec A b) where
  getPollEnv : kit.PkState → BitVec 32 → List AllocEvent → Prop
  removePollEnv : kit.PkState → BitVec 32 → List AllocEvent → Prop

/-- Budget-threaded `get_pre_key` shim contract parameterized by
    `kit : PreKeyStoreSpec A.repAlloc b`. -/
def kitPreKeyGetShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : PreKeyStoreSpec A.repAlloc b) (fds : Bool := false) :
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

/-- Budget-threaded `remove_pre_key` shim contract parameterized by
    `kit : PreKeyStoreSpec A.repAlloc b`. -/
def kitPreKeyRemoveShimSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : PreKeyStoreSpec A.repAlloc b) (fds : Bool := false) :
    Spec (PreKeyShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜match fds with
     | false =>
       (b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
         FitsEnv M lim st (BoxAllocEnv kit.removeBoxSize)
     | true =>
       (b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧
         FitsEnv M lim st (BoxAllocEnv kit.removeBoxSize) ∧ kit.fdsOk s.fs⌝ ∗
      A.pool lim st s ∗ stackAt s.sp kit.removeShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         sf.readReg64 .x1 = b + kit.removeFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.removeBoxSize evs
       | true =>
         sf.readReg64 .x1 = b + kit.removeFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
           (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
           BoxAllocEnv kit.removeBoxSize evs ∧ kit.fdsOk sf.fs⌝ ∗
      A.live (sf.readReg64 .x0) kit.removeBoxSize 8 ∗
      kit.removeBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.removeShimStack

/-- Budget-threaded `get_pre_key` poll contract parameterized by
    `kit : PreKeyStoreSpec A.repAlloc b` and `kitEnv : PreKeyStoreBudgetEnv kit`. -/
def kitPreKeyGetPollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : PreKeyStoreSpec A.repAlloc b)
    (kitEnv : PreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (PreKeyPollCall × kit.PkState × M.σ) where
  pre := fun (x, st0, st) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.getIdOk x.id ∧ FitsEnv M lim st (kitEnv.getPollEnv st0 x.id)⌝ ∗
      kit.getBoxAt x.fut x.self x.id 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 56 ∗
      A.pool lim st s ∗ stackAt s.sp kit.getPollStack
  post := fun (x, st0, st) s0 sf =>
    ∃∗ ans : Except kit.GetErr PreKeyRecord, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans ∧
           kitEnv.getPollEnv st0 x.id evs
       | true =>
         kit.getRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.getEvs x.id ans ∧
           kitEnv.getPollEnv st0 x.id evs ∧ kit.fdsOk sf.fs⌝ ∗
      kit.getBoxAt x.fut x.self x.id 1#8 ∗
      kit.storeAt x.self (kit.getUpdate st0 x.id ans) ∗
      preKeyGetPollOutAt kit x.out ans ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.getPollStack

/-- Budget-threaded `remove_pre_key` poll contract parameterized by
    `kit : PreKeyStoreSpec A.repAlloc b` and `kitEnv : PreKeyStoreBudgetEnv kit`. -/
def kitPreKeyRemovePollSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : PreKeyStoreSpec A.repAlloc b)
    (kitEnv : PreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (PreKeyPollCall × kit.PkState × M.σ) where
  pre := fun (x, st0, st) s =>
    ⌜(b &&& 0xfff#64) = 0#64 ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      kit.removeIdOk x.id ∧ FitsEnv M lim st (kitEnv.removePollEnv st0 x.id)⌝ ∗
      kit.removeBoxAt x.fut x.self x.id 0#8 ∗
      kit.storeAt x.self st0 ∗ memRegion x.out 48 ∗
      A.pool lim st s ∗ stackAt s.sp kit.removePollStack
  post := fun (x, st0, st) s0 sf =>
    ∃∗ ans : Except kit.RemoveErr Unit, ∃∗ evs : List AllocEvent,
      ⌜match fds with
       | false =>
         kit.removeRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.removeEvs x.id ans ∧
           kitEnv.removePollEnv st0 x.id evs
       | true =>
         kit.removeRel st0 x.id ans ∧ sf.trace = s0.trace ++ kit.removeEvs x.id ans ∧
           kitEnv.removePollEnv st0 x.id evs ∧ kit.fdsOk sf.fs⌝ ∗
      kit.removeBoxAt x.fut x.self x.id 1#8 ∗
      kit.storeAt x.self (kit.removeUpdate st0 x.id ans) ∗
      preKeyRemovePollOutAt kit x.out ans ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.removePollStack

/-- `get_pre_key` budget poll contract with `kit.envOk` (and `kit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitPreKeyGetPollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : PreKeyStoreSpec A.repAlloc b)
    (kitEnv : PreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (PreKeyPollCall × kit.PkState × M.σ) :=
  withEnvPre (kitPreKeyGetPollSpec M A lim kit kitEnv fds)
    (match fds with
     | false => fun s => kit.envOk s.fs.files
     | true => fun s => kit.envOk s.fs.files ∧ kit.fdsOk s.fs)

/-- `remove_pre_key` budget poll contract with `kit.envOk` (and `kit.fdsOk` when `fds = true`)
    on the entry state. -/
abbrev kitPreKeyRemovePollSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : PreKeyStoreSpec A.repAlloc b)
    (kitEnv : PreKeyStoreBudgetEnv kit) (fds : Bool := false) :
    Spec (PreKeyPollCall × kit.PkState × M.σ) :=
  withEnvPre (kitPreKeyRemovePollSpec M A lim kit kitEnv fds)
    (match fds with
     | false => fun s => kit.envOk s.fs.files
     | true => fun s => kit.envOk s.fs.files ∧ kit.fdsOk s.fs)

end LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
