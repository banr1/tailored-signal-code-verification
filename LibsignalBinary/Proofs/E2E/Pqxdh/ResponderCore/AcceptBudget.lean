/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.Accept
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecBudget
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Heap.IfaceBudgetBase
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `Pqxdh::accept` Helpers and Placed Contracts

Provides `RustCliAllocBudget M` allocator split combinators (`SepWPp.split_alloc`,
`SepWPp.split_alloc_noOom`), `VmPreserved`-strengthened callee contracts, and relocatable
`[LibsignalPlacement]` budget contracts for `PrivateKey::calculate_agreement` (Block `207`) and
`Pqxdh::accept` (Block `79`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalFrozen LibsignalPlacement libsignalFrozen_of_keepsFrozen
  libsignalSessionCode lsLogFilterAddr lsmpl
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded
  subroutine_ok_kit_of_trTrap trTrapProgAt trTrapProgAt_fnAddr_eq
  tripleRatchetProgAt tripleRatchetProgAtExt
  withLsCodeRoLoaded withLsFrozen extract_withLsFrozen
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes KeyCanonicalGhost Primitives StructuralPrims WellSizedAcceptKeysInput
  bv_sub_add_lit' bytesToBv8 handshakeKeysResultOk104 pqxdhEntryStack
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  AcceptFieldsCallGhost boxSliceU8_32_entails_at_sub4912
  calcErr_entails_at_sub4912 calculateAgreementStack
  pqxdhAcceptErrStrong2At pqxdhAcceptOptFieldsAt
  pqxdhCalculateAgreementResultAt spAligned_sub_4944
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  NullAllowed RustCliAllocBudget VmPreserved rustAllocEvents rustDeallocEvents
  rustCliAllocBudgetSpecBase rustCliAllocNoOomSpecBase
  rustCliDeallocBudgetSpecBase subroutine_ok_allocNoOom_of_budgetBase
)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase withVmPreserved)

/-! ## 1. Budget-Threaded `SepWPp` Allocator Split Combinators -/

/-- Split the postcondition of `rustCliAllocBudgetSpec M A lim false` in a `SepWPp` goal into its
`x0 = 0` (`NullAllowed size align`) and `x0 ≠ 0` (`M.stepEvents (rustAllocEvents size align) st`)
branches. -/
theorem SepWPp.split_alloc {M : AllocCostModel} {prog : Program} {ret : BitVec 64}
    {s0 s : State} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {sp sp' : BitVec 64} {size align : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hsp : sp = sp')
    (hnull : s.readReg64 (.gpr 0#5) = 0#64 → NullAllowed size align → AllocCallPreserved s0 s →
      SepWPp prog ret s (A.pool lim st s ∗ stackAt sp' allocHookStack ∗ F) Q Qp)
    (hok : s.readReg64 (.gpr 0#5) ≠ 0#64 → (s.readReg64 (.gpr 0#5)).toNat % align = 0 →
      AllocCallPreserved s0 s →
      SepWPp prog ret s
        (A.pool lim (M.stepEvents (rustAllocEvents size align) st) s ∗
          stackAt sp' allocHookStack ∗
          A.live (s.readReg64 (.gpr 0#5)) size align ∗
          memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) Q Qp) :
    SepWPp prog ret s
      (⌜AllocCallPreserved s0 s⌝ ∗
        A.pool lim (if s.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st) s ∗
        stackAt sp allocHookStack ∗
        (if s.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
         else ⌜(s.readReg64 .x0).toNat % align = 0⌝ ∗
           A.live (s.readReg64 .x0) size align ∗
           memRegion (s.readReg64 .x0) size) ∗ F) Q Qp := by
  subst hsp
  change SepWPp prog ret s
    (⌜AllocCallPreserved s0 s⌝ ∗
      A.pool lim (if s.readReg64 (.gpr 0#5) = 0 then st else M.stepEvents (rustAllocEvents size align) st) s ∗
      stackAt sp allocHookStack ∗
      (if s.readReg64 (.gpr 0#5) = 0 then ⌜NullAllowed size align⌝
       else ⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0⌝ ∗
         A.live (s.readReg64 (.gpr 0#5)) size align ∗
         memRegion (s.readReg64 (.gpr 0#5)) size) ∗ F) Q Qp
  by_cases h0 : s.readReg64 (.gpr 0#5) = 0
  · simp only [h0, ↓reduceIte]
    intro R hm
    have heq :
        ((⌜AllocCallPreserved s0 s⌝ ∗ A.pool lim st s ∗ stackAt sp allocHookStack ∗
          ⌜NullAllowed size align⌝ ∗ F) ∗ R) =
        (⌜AllocCallPreserved s0 s⌝ ∗ (⌜NullAllowed size align⌝ ∗
          ((A.pool lim st s ∗ stackAt sp allocHookStack ∗ F) ∗ R))) := by
      sep_ac_rfl
    rw [heq, satisfies_pure_sepConj, satisfies_pure_sepConj] at hm
    exact hnull h0 hm.2.1 hm.1 R hm.2.2
  · simp only [h0, ↓reduceIte]
    intro R hm
    let st' := M.stepEvents (rustAllocEvents size align) st
    have heq :
        ((⌜AllocCallPreserved s0 s⌝ ∗ A.pool lim st' s ∗ stackAt sp allocHookStack ∗
          (⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0⌝ ∗
            A.live (s.readReg64 (.gpr 0#5)) size align ∗
            memRegion (s.readReg64 (.gpr 0#5)) size) ∗ F) ∗ R) =
        (⌜AllocCallPreserved s0 s⌝ ∗ (⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0⌝ ∗
          ((A.pool lim st' s ∗ stackAt sp allocHookStack ∗
            A.live (s.readReg64 (.gpr 0#5)) size align ∗
            memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) ∗ R))) := by
      sep_ac_rfl
    rw [heq, satisfies_pure_sepConj, satisfies_pure_sepConj] at hm
    exact hok h0 hm.2.1 hm.1 R hm.2.2

/-- Total-correctness (`NoOom`, `FitsEvents`) counterpart of `SepWPp.split_alloc` for
`rustCliAllocNoOomSpec M A lim false`, where `x0 ≠ 0` is guaranteed unconditionally. -/
theorem SepWPp.split_alloc_noOom {M : AllocCostModel} {prog : Program} {ret : BitVec 64}
    {s0 s : State} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {sp sp' : BitVec 64} {size align : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hsp : sp = sp')
    (hok : s.readReg64 (.gpr 0#5) ≠ 0#64 → (s.readReg64 (.gpr 0#5)).toNat % align = 0 →
      AllocCallPreserved s0 s →
      SepWPp prog ret s
        (A.pool lim (M.stepEvents (rustAllocEvents size align) st) s ∗
          stackAt sp' allocHookStack ∗
          A.live (s.readReg64 (.gpr 0#5)) size align ∗
          memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) Q Qp) :
    SepWPp prog ret s
      (⌜AllocCallPreserved s0 s ∧ s.readReg64 .x0 ≠ 0#64 ∧
          (s.readReg64 .x0).toNat % align = 0⌝ ∗
        A.pool lim (M.stepEvents (rustAllocEvents size align) st) s ∗
        stackAt sp allocHookStack ∗
        A.live (s.readReg64 .x0) size align ∗
        memRegion (s.readReg64 .x0) size ∗ F) Q Qp := by
  subst hsp
  intro R hm
  let st' := M.stepEvents (rustAllocEvents size align) st
  have heq :
      ((⌜AllocCallPreserved s0 s ∧ s.readReg64 .x0 ≠ 0#64 ∧
          (s.readReg64 .x0).toNat % align = 0⌝ ∗
        A.pool lim st' s ∗
        stackAt sp allocHookStack ∗
        A.live (s.readReg64 .x0) size align ∗
        memRegion (s.readReg64 .x0) size ∗ F) ∗ R) =
      (⌜AllocCallPreserved s0 s ∧ s.readReg64 (.gpr 0#5) ≠ 0#64 ∧
          (s.readReg64 (.gpr 0#5)).toNat % align = 0⌝ ∗
        ((A.pool lim st' s ∗ stackAt sp allocHookStack ∗
          A.live (s.readReg64 (.gpr 0#5)) size align ∗
          memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) ∗ R)) := by
    change _ = _
    sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact hok hm.1.2.1 hm.1.2.2 hm.1.1 R hm.2

/-! ## 2. Budget-Threaded `pqxdh_*_ok_at` Hook Resolution & `VmPreserved` Callee Specs -/

section HookAt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

ls_attribute [local simp, local arm64_norm ↓]
  (ls_stub% "__rustc::__rust_alloc") (ls_stub% "__rustc::__rust_dealloc")

theorem pqxdh_alloc_ok_at_trap {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) :=
  hook_ok_at (P := libsignalSessionCode) (hname := "__rustc::__rust_alloc") rfl hk
    (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
    (by simp [Rust.isPanicSymbol])
    (by unfold HookSat at *; exact hA.alloc)

theorem pqxdh_alloc_ok_at {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdh_alloc_ok_at_trap hA hk)

theorem pqxdh_allocNoOom_ok_at_trap {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomSpecBase M A lim false) :=
  subroutine_ok_allocNoOom_of_budgetBase (pqxdh_alloc_ok_at_trap hA hk)

theorem pqxdh_allocNoOom_ok_at {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomSpecBase M A lim false) :=
  subroutine_ok_allocNoOom_of_budgetBase (pqxdh_alloc_ok_at hA hk)

theorem pqxdh_dealloc_ok_at_trap {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) :=
  hook_ok_at (P := libsignalSessionCode) (hname := "__rustc::__rust_dealloc") rfl hk
    (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
    (by simp [Rust.isPanicSymbol])
    (by unfold HookSat at *; exact hA.dealloc)

theorem pqxdh_dealloc_ok_at {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdh_dealloc_ok_at_trap hA hk)

theorem pqxdh_alloc_ok_at_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) :=
  hook_ok_at (P := libsignalSessionCode) (hname := "__rustc::__rust_alloc") rfl hk
    (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
    (by simp [Rust.isPanicSymbol]) hA.alloc

theorem pqxdh_allocNoOom_ok_at_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomSpecBase M A lim false) :=
  subroutine_ok_allocNoOom_of_budgetBase (pqxdh_alloc_ok_at_ext hA hk)

theorem pqxdh_dealloc_ok_at_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) :=
  hook_ok_at (P := libsignalSessionCode) (hname := "__rustc::__rust_dealloc") rfl hk
    (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
    (by simp [Rust.isPanicSymbol]) hA.dealloc

end HookAt

/-- `VmPreserved`-strengthened `ecPubKeyIsCanonicalCallSpec`. -/
def ecPubKeyIsCanonicalCallSpec (P : Primitives) :
    Spec KeyCanonicalGhost :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.ResponderCore.ecPubKeyIsCanonicalCallSpec P)

/-- `VmPreserved`-strengthened `ecPubKeyIsCanonicalCallSpecExt`. -/
def ecPubKeyIsCanonicalCallSpecExt (P : Primitives) :
    Spec KeyCanonicalGhost :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.ResponderCore.ecPubKeyIsCanonicalCallSpecExt P)

/-- `VmPreserved`-strengthened `pqxdhVecAppendElementsFastSpecExt`. -/
def pqxdhVecAppendElementsFastSpecExt :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.ResponderCore.pqxdhVecAppendElementsFastSpecExt

/-! ## 3. Relocatable `[LibsignalPlacement]` `calculate_agreement` & `Pqxdh::accept` Contracts -/

/-- Deterministic `AllocEvent` list emitted by `PrivateKey::calculate_agreement` (Block `207`):
`[]` when the X25519 shared secret is all-zero, and `rustAllocEvents 32 1` otherwise. -/
def calculateAgreementEvents (P : Primitives) (ourSk32 theirPk32 : Bytes) : List AllocEvent :=
  if P.x25519 ourSk32 theirPk32 = List.replicate 32 0 then [] else rustAllocEvents 32 1

/-- Allocation envelope for `PrivateKey::calculate_agreement`. -/
def CalculateAgreementEnv (P : Primitives) (ourSk32 theirPk32 : Bytes)
    (evs : List AllocEvent) : Prop :=
  evs = calculateAgreementEvents P ourSk32 theirPk32

/-- Budget-threaded relocatable base specification for `PrivateKey::calculate_agreement`
(Block `207`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEvents`). -/
def acceptCalculateAgreementPlacedBaseSpec (M : AllocCostModel) (P : Primitives)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × Bytes × BitVec 64 × Bytes × BitVec 64 × BitVec 64) × M.σ) where
  pre := fun ((ourA, ourSk32, theirA, theirPk32, ret, sp), st) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32 ∧
      FitsEvents M lim st (calculateAgreementEvents P ourSk32 theirPk32)⌝ ∗
    (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
    memRegion ret 24 ∗ A.pool lim st s ∗ stackAt sp calculateAgreementStack
  post := fun ((ourA, ourSk32, theirA, theirPk32, ret, sp), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
    pqxdhCalculateAgreementResultAt P A.repAlloc ret ourSk32 theirPk32 ∗
    A.pool lim (M.stepEvents (calculateAgreementEvents P ourSk32 theirPk32) st) sf ∗
    stackAt sp calculateAgreementStack

/-- Deterministic `AllocEvent` list emitted on the accepting (`acceptKeys P inp = some _`) path of
`Pqxdh::accept` (Block `79`): `192`-byte `secrets` buffer + `3` (or `4`, when `inp.opkBSk?.isSome`)
`32`-byte X25519 `Box<[u8]>` allocations/deallocations + `192`-byte `secrets` deallocation. -/
def acceptSuccessEvents (inp : AcceptKeysInput) : List AllocEvent :=
  let dhCycle := rustAllocEvents 32 1 ++ rustDeallocEvents 32 1
  rustAllocEvents 192 1 ++
    dhCycle ++ dhCycle ++ dhCycle ++
    (if inp.opkBSk?.isSome then dhCycle else []) ++
    rustDeallocEvents 192 1

private theorem call_lscro_from_frozen {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LibsignalFrozen pl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic x s sf ∗ R') → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalFrozen pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [withLsCodeRoLoaded]) :
    SepWPp prog ret s P Q Qp := by
  have hcall' : subroutine_ok prog entry
      { withLsFrozen pl spec with
        post := fun x' s0' sf => ⌜LibsignalFrozen pl sf.mem⌝ ∗ spec.post x' s0' sf } := by
    refine Arm64.subroutine_ok.of_codeLoaded fun x' R' s0' hpc0 hrun0 hpre0 hsp0 hL0 => ?_
    have ⟨hfr0, hpre_spec⟩ := extract_withLsFrozen hpre0
    have hpre_cro : s0'.mem ⊨ (withLsCodeRoLoaded pl spec).pre x' s0' ∗ R' := by
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨LibsignalCodeRoLoaded.of_libsignalFrozen hfr0, hpre_spec⟩
    obtain ⟨sf, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x' R' s0' hpc0 hrun0 hpre_cro hsp0 hL0
    refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨libsignalFrozen_of_keepsFrozen hfr0 hsteps.keepsFrozen, hpost⟩
    · exact Or.inr hrest
  refine SepWPp.call_wpp (x := x) (F := F) hcall' hpc hrun hsp hlr
    (fun R hm => by
      dsimp only [withLsFrozen]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hF, ?_⟩
      rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hm⟩)
    (fun sm code R' hex hpost => by
      dsimp only [withLsFrozen] at hpost
      exact hexit sm code R' hex hpost)
    (fun sm hpan hpost => by
      dsimp only [withLsFrozen] at hpost ⊢
      exact hpanic sm hpan hpost)
    (fun sm hpcm hrunm hspm hcsm => ?_)
    (fun sm R' _ hoom_post => by
      dsimp only [withLsFrozen] at hoom_post
      rw [hoom sm] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim)
  have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
  dsimp only
  exact SepWPp.congr_pre (sepConj_assoc _ _ _)
    (SepWPp.pure_left fun hFm => hnext sm hpcm hrunm hspm hsp_alm hcsm hFm)

/-- Budget-threaded relocatable call combinator for `PrivateKey::calculate_agreement` at
`lsmpl.base 207` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEvents`). -/
theorem SepWPp_call_hag_placed [LibsignalPlacement] {M : AllocCostModel} {prog : Program}
    {ret : BitVec 64} {s : State} {P_pre : SepProp} {Q Qp : State → SepProp → Prop}
    {s0 : State} {F : SepProp} {ret_pc : BitVec 64}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (hWF : StructuralPrims P)
    (hag : subroutine_ok prog (lsmpl.base 207)
      (withLsCodeRoLoaded lsmpl (acceptCalculateAgreementPlacedBaseSpec M P A lim)))
    (hF : LibsignalFrozen lsmpl s.mem)
    (ourA : BitVec 64) (our : Bytes) (theirA : BitVec 64) (their : Bytes)
    (hpc : s.pc = lsmpl.base 207) (hrun : s.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : s.sp = s0.sp - 4944#64) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx : s.readReg64 Reg.x0 = ourA ∧ s.readReg64 Reg.x1 = theirA ∧
      s.readReg64 Reg.x8 = s0.sp - 4912#64 ∧ s.sp = s0.sp - 4944#64 ∧
      our.length = 32 ∧ their.length = 32 ∧
      FitsEvents M lim st (calculateAgreementEvents P our their))
    (hP : P_pre = ((ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
      memRegion (s0.sp - 4912#64) 24 ∗ A.pool lim st s ∗
      stackAt (s0.sp - 4944#64) calculateAgreementStack) ∗ F)
    (herr : P.x25519 our their = List.replicate 32 0 →
      ∀ (sf : State) (hi : BitVec 56) (u2 : BitVec 64), sf.pc = ret_pc → sf.status = .Running →
        sf.sp = s0.sp - 4944#64 → CalleeSavedPreserved s sf →
        sf.trace = s0.trace → LibsignalFrozen lsmpl sf.mem →
        SepWPp prog ret sf (((s0.sp - 4912#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 4904#64) ↦₆₄ (hi ++ 3#8)) ∗ ((s0.sp - 4896#64) ↦₆₄ u2) ∗
          (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
          A.pool lim st sf ∗ stackAt (s0.sp - 4944#64) calculateAgreementStack ∗ F) Q Qp)
    (hok : P.x25519 our their ≠ List.replicate 32 0 →
      ∀ (sf : State) (dh_ptr : BitVec 64), sf.pc = ret_pc → sf.status = .Running →
        sf.sp = s0.sp - 4944#64 → CalleeSavedPreserved s sf →
        sf.trace = s0.trace → LibsignalFrozen lsmpl sf.mem →
        SepWPp prog ret sf (((s0.sp - 4912#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 4904#64) ↦₆₄ dh_ptr) ∗ ((s0.sp - 4896#64) ↦₆₄ 32#64) ∗
          (dh_ptr ↦ₛ bytesToBv8 (P.x25519 our their)) ∗ A.live dh_ptr 32 1 ∗
          (ourA ↦ₛ bytesToBv8 our) ∗ (theirA ↦ₛ bytesToBv8 their) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) sf ∗
          stackAt (s0.sp - 4944#64) calculateAgreementStack ∗ F) Q Qp) :
    SepWPp prog ret s P_pre Q Qp := by
  refine call_lscro_from_frozen
    (spec := acceptCalculateAgreementPlacedBaseSpec M P A lim)
    (x := ((ourA, our, theirA, their, s0.sp - 4912#64, s0.sp - 4944#64), st))
    hF hag hpc hrun (spAligned_sub_4944 hsp_align hsp_eq) hlr rfl hx hP
    (fun _ _ _ _ hm => (not_satisfies_false_sepConj hm).elim)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    (fun sf hpc_f hrun_f hsp_f _hsp_al_f hcs_f hF_f => ?_)
  dsimp only [acceptCalculateAgreementPlacedBaseSpec, pqxdhCalculateAgreementResultAt]
  rw [htr, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_
  by_cases hdh : P.x25519 our their = List.replicate 32 0
  · have hevs0 : calculateAgreementEvents P our their = [] := by
      simp only [calculateAgreementEvents, hdh, ↓reduceIte]
    simp only [hdh, hevs0, M.stepEvents_nil, ↓reduceIte, bv_sub_add_lit', BitVec.reduceSub,
      sepConj_assoc]
    refine SepWPp.fold (calcErr_entails_at_sub4912 s0.sp) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun u2 => ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun hi => ?_
    simp only [sepConj_assoc]
    exact herr hdh sf hi u2 hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf hF_f
  · have hevs32 : calculateAgreementEvents P our their = rustAllocEvents 32 1 := by
      simp only [calculateAgreementEvents, hdh, ↓reduceIte]
    have hdh_bv_len : (bytesToBv8 (P.x25519 our their)).length = 32 := by
      simp [bytesToBv8, hWF.x25519_len our their]
    simp only [hdh, hevs32, ↓reduceIte, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    refine SepWPp.fold (boxSliceU8_32_entails_at_sub4912 A.repAlloc s0.sp hdh_bv_len) (by sep_focus) ?_
    rw [sepExists_sepConj_left]; refine SepWPp.exists_elim fun dh_ptr => ?_
    simp only [sepConj_assoc]
    exact hok hdh sf dh_ptr hpc_f hrun_f (hsp_f.trans hsp_eq) hcs_f htr_sf hF_f

/-- Budget-threaded relocatable inner contract for `Pqxdh::accept` (Block `79`), parameterized by
allocator event envelope `AcceptEnv : AcceptKeysInput → List AllocEvent → Prop` (`onPanic = ⌜False⌝`,
`onOom = ⌜False⌝` under `FitsEnv M lim st (AcceptEnv g.inp)`). -/
def pqxdhAcceptOptFieldsInnerPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (AcceptFieldsCallGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.argPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inp.trustedPeer = true ∧
      g.inp.replayOk = true ∧ g.inp.hdr.opkId?.isSome = g.inp.opkBSk?.isSome ∧
      WellSizedAcceptKeysInput g.inp ∧
      FitsEnv M lim st (AcceptEnv g.inp)⌝ ∗
    pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
    memRegion g.outPtr 104 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
    stackAt s.sp pqxdhEntryStack ∗ A.pool lim st s
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AcceptEnv g.inp evs⌝ ∗
      pqxdhAcceptOptFieldsAt g.argPtr g.pqskPtr g.ctSlicePtr g.ctBufPtr g.inp ∗
      (match acceptKeys P g.inp with
       | some drKey =>
         g.outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 drKey)
       | none =>
         pqxdhAcceptErrStrong2At g.outPtr ∗ anyHeap) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s0.sp pqxdhEntryStack ∗
      A.pool lim (M.stepEvents evs st) sf

/-- Budget-threaded `withLsCodeRoLoaded` contract for `Pqxdh::accept` (Block `79`). -/
def pqxdhAcceptOptFieldsPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (AcceptFieldsCallGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv)

/-- Budget-threaded `withLsFrozen` contract for `Pqxdh::accept` (Block `79`). -/
def pqxdhAcceptOptFieldsFrozenPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (AcceptEnv : AcceptKeysInput → List AllocEvent → Prop) :
    Spec (AcceptFieldsCallGhost × M.σ) :=
  withLsFrozen lsmpl (pqxdhAcceptOptFieldsInnerPlacedSpec P A lim AcceptEnv)

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
