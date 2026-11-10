/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OptImageHelper
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# Budget-Threaded Allocation Helper and Small Serializer Specifications

Defines `RustCliAllocBudget M` and `VmPreserved` separation-logic contracts, deterministic
allocator event envelopes, and `AllocContractsBudget{,X}` hypothesis bundles for `finish_grow`,
`do_reserve_and_handle`, `Vec<u8>::into_boxed_slice`, `Box<[u8]>::try_clone_from_ref_in`,
`ChainKey::to_pb`, `PublicKey::serialize`, and `PrivateKey::derive_public_key_bytes`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ChainKey Crypto PublicKey PubKeyFn)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes optChainKeyAt)
open CryptoVerification.InImageLift (subroutine_ok_inImage_of_subroutine_ok)
open CryptoVerification.LibsignalTripleRatchet (
  VecArg allocName deallocName extHookStack
  hookMemcpy_region_trace_ok hookMemcpy_trace_ok hookMemmove_trace_ok
  hookMemset_region_trace_ok hookMemset_trace_ok
  memcpyName memmoveName memsetName pubFromSecretHook pubFromSecretName
  reallocName sessionShim_hookOk shimName sub_ok_at_of_fnAddr subroutine_ok_kit_of_trTrap
  trTrapExterns trTrapProgAt trapsOnly_trTrap_kit tripleRatchetExterns
  tripleRatchetExterns_abs tripleRatchetProgAt tripleRatchetProgAtExt
  withPanics_trTrap_ne withStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  VmPreserved rustAllocEvents rustCliAllocBudgetSpecBase rustCliAllocNoOomSpecBase
  rustCliDeallocBudgetSpecBase rustCliDeallocNoOomSpecBase rustCliReallocBudgetSpecBase
  rustCliReallocNoOomSpecBase rustDeallocEvents rustReallocEvents
  subroutine_ok_allocNoOom_of_budgetBase subroutine_ok_reallocNoOom_of_budgetBase
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetExternSpecWithStackBase rustCliAllocBudgetSpecWithStackBase
  rustCliAllocNoOomExternSpecWithStackBase rustCliAllocNoOomSpecWithStackBase
  rustCliDeallocBudgetExternSpecWithStackBase rustCliDeallocBudgetSpecWithStackBase
  rustCliDeallocNoOomExternSpecWithStackBase rustCliDeallocNoOomSpecWithStackBase
  rustCliReallocBudgetExternSpecWithStackBase rustCliReallocBudgetSpecWithStackBase
  rustCliReallocNoOomExternSpecWithStackBase rustCliReallocNoOomSpecWithStackBase
  subroutine_ok_rustCliAllocBudget_withStackBase
  subroutine_ok_rustCliDeallocBudget_externWithStackBase
  subroutine_ok_rustCliReallocBudget_externWithStackBase
)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC vmPreserved_writeReg64
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec sessionMemmoveBudgetSpec
  sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec
)

/-! ## Re-Exports from `Alloc.Defs` (Symbol Names, Stack Constants, Ghost Structs, Memory Helpers) -/

abbrev finishGrowName : String := CryptoVerification.LibsignalTripleRatchet.finishGrowName
abbrev doReserveName : String := CryptoVerification.LibsignalTripleRatchet.doReserveName
abbrev intoBoxedSliceName : String := CryptoVerification.LibsignalTripleRatchet.intoBoxedSliceName
abbrev tryCloneFromRefName : String := CryptoVerification.LibsignalTripleRatchet.tryCloneFromRefName
abbrev chainKeyToPbName : String := CryptoVerification.LibsignalTripleRatchet.chainKeyToPbName
abbrev publicKeySerializeName : String :=
  CryptoVerification.LibsignalTripleRatchet.publicKeySerializeName
abbrev derivePublicKeyBytesName : String :=
  CryptoVerification.LibsignalTripleRatchet.derivePublicKeyBytesName

abbrev finishGrowStack : Nat := CryptoVerification.LibsignalTripleRatchet.finishGrowStack
abbrev finishGrowStackX : Nat := CryptoVerification.LibsignalTripleRatchet.finishGrowStackX
abbrev doReserveStack : Nat := CryptoVerification.LibsignalTripleRatchet.doReserveStack
abbrev doReserveStackX : Nat := CryptoVerification.LibsignalTripleRatchet.doReserveStackX
abbrev intoBoxedSliceStack : Nat := CryptoVerification.LibsignalTripleRatchet.intoBoxedSliceStack
abbrev intoBoxedSliceStackX : Nat := CryptoVerification.LibsignalTripleRatchet.intoBoxedSliceStackX
abbrev tryCloneFromRefStack : Nat := CryptoVerification.LibsignalTripleRatchet.tryCloneFromRefStack
abbrev tryCloneFromRefStackX : Nat :=
  CryptoVerification.LibsignalTripleRatchet.tryCloneFromRefStackX
abbrev chainKeyToPbStack : Nat := CryptoVerification.LibsignalTripleRatchet.chainKeyToPbStack
abbrev chainKeyToPbStackX : Nat := CryptoVerification.LibsignalTripleRatchet.chainKeyToPbStackX
abbrev publicKeySerializeStack : Nat :=
  CryptoVerification.LibsignalTripleRatchet.publicKeySerializeStack
abbrev publicKeySerializeStackX : Nat :=
  CryptoVerification.LibsignalTripleRatchet.publicKeySerializeStackX

abbrev FinishGrowCall := CryptoVerification.LibsignalTripleRatchet.FinishGrowCall
abbrev reserveCap := CryptoVerification.LibsignalTripleRatchet.reserveCap
abbrev DoReserveCall := CryptoVerification.LibsignalTripleRatchet.DoReserveCall
abbrev boxU8Buf := CryptoVerification.LibsignalTripleRatchet.boxU8Buf
abbrev boxU8At_eq_boxU8Buf := @CryptoVerification.LibsignalTripleRatchet.boxU8At_eq_boxU8Buf
abbrev TryCloneSliceCall := CryptoVerification.LibsignalTripleRatchet.TryCloneSliceCall
abbrev ChainKeyToPbCall := CryptoVerification.LibsignalTripleRatchet.ChainKeyToPbCall
abbrev PublicKeySerializeCall := CryptoVerification.LibsignalTripleRatchet.PublicKeySerializeCall
abbrev DerivePublicKeyBytesCall :=
  CryptoVerification.LibsignalTripleRatchet.DerivePublicKeyBytesCall

abbrev memRegion_eight := @CryptoVerification.LibsignalTripleRatchet.memRegion_eight
abbrev memRegion_cells := @CryptoVerification.LibsignalTripleRatchet.memRegion_cells
abbrev stackAt_split_cells := @CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells
abbrev ImgCallInv := CryptoVerification.LibsignalTripleRatchet.ImgCallInv
abbrev panic_at_handle_error_norm_ext :=
  @CryptoVerification.LibsignalTripleRatchet.panic_at_handle_error_norm_ext
abbrev panic_at_handle_error_norm_trap :=
  @CryptoVerification.LibsignalTripleRatchet.panic_at_handle_error_norm_trap
abbrev panic_at_handle_error_norm :=
  @CryptoVerification.LibsignalTripleRatchet.panic_at_handle_error_norm

/-! ## Allocator Event Lists & Envelopes -/

/-- Exact allocator event list of `RawVecInner::finish_grow`:
`rustAllocEvents (new * stride) align` when `cap = 0`, else
`rustReallocEvents (cap * stride) (new * stride) align`. -/
def finishGrowEvents (cap new align stride : Nat) : List AllocEvent :=
  if cap = 0 then rustAllocEvents (new * stride) align
  else rustReallocEvents (cap * stride) (new * stride) align

def FinishGrowEnv (x : FinishGrowCall) (evs : List AllocEvent) : Prop :=
  evs = finishGrowEvents x.cap.toNat x.new.toNat x.align.toNat x.stride.toNat

theorem fitsEnv_finishGrow_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : FinishGrowCall) :
    FitsEnv M lim st (FinishGrowEnv x) ↔
      FitsEvents M lim st (finishGrowEvents x.cap.toNat x.new.toNat x.align.toNat x.stride.toNat) :=
  FitsEnv.eq_iff

/-- Exact allocator event list of `RawVecInner::reserve::do_reserve_and_handle` on a `Vec<u8>`. -/
def doReserveEvents (x : DoReserveCall) : List AllocEvent :=
  let newCap := reserveCap x.cap.toNat x.bs.length x.additional
  if x.cap = 0#64 then rustAllocEvents newCap 1
  else rustReallocEvents x.cap.toNat newCap 1

def DoReserveEnv (x : DoReserveCall) (evs : List AllocEvent) : Prop :=
  evs = doReserveEvents x

theorem fitsEnv_doReserve_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : DoReserveCall) :
    FitsEnv M lim st (DoReserveEnv x) ↔ FitsEvents M lim st (doReserveEvents x) :=
  FitsEnv.eq_iff

theorem finishGrowEvents_doReserve_eq (x : DoReserveCall)
    (hbound : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64) :
    finishGrowEvents x.cap.toNat
        (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat
        (1#64).toNat (1#64).toNat =
      doReserveEvents x := by
  have hnew :
      (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  unfold finishGrowEvents doReserveEvents
  rw [hnew, h1, Nat.mul_one, Nat.mul_one]
  by_cases hcap : x.cap = 0#64
  · rw [hcap]; rfl
  · have hcap_nat : x.cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    simp only [hcap, hcap_nat, ↓reduceIte]

/-- Exact allocator event list of `<Vec<u8>>::into_boxed_slice`:
`[]` when `cap ≤ bytes.length`, `rustDeallocEvents cap 1` when `cap > bytes.length` and `bytes = []`,
else `rustReallocEvents cap bytes.length 1`. -/
def intoBoxedSliceEvents (x : VecArg) : List AllocEvent :=
  if x.cap.toNat ≤ x.bytes.length then []
  else if x.bytes = [] then rustDeallocEvents x.cap.toNat 1
  else rustReallocEvents x.cap.toNat x.bytes.length 1

def IntoBoxedSliceEnv (x : VecArg) (evs : List AllocEvent) : Prop :=
  evs = intoBoxedSliceEvents x

theorem fitsEnv_intoBoxedSlice_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : VecArg) :
    FitsEnv M lim st (IntoBoxedSliceEnv x) ↔ FitsEvents M lim st (intoBoxedSliceEvents x) :=
  FitsEnv.eq_iff

/-- Exact allocator event list of `<Box<[u8]>>::try_clone_from_ref_in`:
`[]` when `bs = []`, else `rustAllocEvents bs.length 1`. -/
def tryCloneFromRefEvents (x : TryCloneSliceCall) : List AllocEvent :=
  if x.bs = [] then [] else rustAllocEvents x.bs.length 1

def TryCloneFromRefEnv (x : TryCloneSliceCall) (evs : List AllocEvent) : Prop :=
  evs = tryCloneFromRefEvents x

theorem fitsEnv_tryCloneFromRef_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : TryCloneSliceCall) :
    FitsEnv M lim st (TryCloneFromRefEnv x) ↔ FitsEvents M lim st (tryCloneFromRefEvents x) :=
  FitsEnv.eq_iff

/-- Exact allocator event list of `ChainKey::to_pb` (`__rust_alloc(32, 1)`). -/
def chainKeyToPbEvents : List AllocEvent :=
  rustAllocEvents 32 1

def ChainKeyToPbEnv (evs : List AllocEvent) : Prop :=
  evs = chainKeyToPbEvents

theorem fitsEnv_chainKeyToPb_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st ChainKeyToPbEnv ↔ FitsEvents M lim st chainKeyToPbEvents :=
  FitsEnv.eq_iff

/-- Exact allocator event list of `PublicKey::serialize` (`__rust_alloc(33, 1)`). -/
def publicKeySerializeEvents : List AllocEvent :=
  rustAllocEvents 33 1

def PublicKeySerializeEnv (evs : List AllocEvent) : Prop :=
  evs = publicKeySerializeEvents

theorem fitsEnv_publicKeySerialize_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st PublicKeySerializeEnv ↔ FitsEvents M lim st publicKeySerializeEvents :=
  FitsEnv.eq_iff

/-! ## 1. `RawVecInner::finish_grow` (`0x15de4`) Budget Contracts -/

/-- Stack-parameterized budget contract of `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]`
(`= finishGrowSpec M A lim` at `allocHookStack`, `= finishGrowSpecX M A lim` at `extHookStack`).
Under `FitsEnv M lim st (FinishGrowEnv x)`, `__rust_alloc` / `__rust_realloc` succeeds with a
non-null pointer (`tag = 0#64`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def finishGrowSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrowCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEnv M lim st (FinishGrowEnv x)⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 48)
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
      A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (x.new.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool lim
        (M.stepEvents (finishGrowEvents x.cap.toNat x.new.toNat x.align.toNat x.stride.toNat) st)
        sf ∗
      stackAt s0.sp (hookStack + 48)

abbrev finishGrowSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrowCall × M.σ) :=
  finishGrowSpecWithStack M A lim allocHookStack

abbrev finishGrowSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrowCall × M.σ) :=
  finishGrowSpecWithStack M A lim extHookStack

abbrev finishGrowBudgetSpecWithStack := @finishGrowSpecWithStack
abbrev finishGrowBudgetSpec := @finishGrowSpec
abbrev finishGrowBudgetSpecX := @finishGrowSpecX

/-! ## 2. `RawVecInner::reserve::do_reserve_and_handle` (`0x4cac`) Budget Contracts -/

/-- Stack-parameterized budget contract of `do_reserve_and_handle` on a 16-byte `RawVecInner`
(`= doReserveRawSpec M A lim` at `finishGrowStack`, `= doReserveRawSpecX M A lim` at
`finishGrowStackX`). `onPanic = ⌜False⌝` and `onOom = ⌜False⌝` under
`FitsEnv M lim st (DoReserveEnv x)`. -/
def doReserveRawSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (fgStack : Nat) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp (fgStack + 64)
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0.sp (fgStack + 64)

/-- Stack-parameterized budget contract of `do_reserve_and_handle` on a `Vec<u8>` (`vecU8At`)
(`= doReserveSpec M A lim` at `finishGrowStack`, `= doReserveSpecX M A lim` at `finishGrowStackX`). -/
def doReserveSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (fgStack : Nat) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63 ∧ FitsEnv M lim st (DoReserveEnv x)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp (fgStack + 64)
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A.repAlloc x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0.sp (fgStack + 64)

abbrev doReserveRawSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserveRawSpecWithStack M A lim finishGrowStack

abbrev doReserveRawSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserveRawSpecWithStack M A lim finishGrowStackX

abbrev doReserveSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserveSpecWithStack M A lim finishGrowStack

abbrev doReserveSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveCall × M.σ) :=
  doReserveSpecWithStack M A lim finishGrowStackX

abbrev doReserveRawBudgetSpecWithStack := @doReserveRawSpecWithStack
abbrev doReserveRawBudgetSpec := @doReserveRawSpec
abbrev doReserveRawBudgetSpecX := @doReserveRawSpecX
abbrev doReserveBudgetSpecWithStack := @doReserveSpecWithStack
abbrev doReserveBudgetSpec := @doReserveSpec
abbrev doReserveBudgetSpecX := @doReserveSpecX

/-! ## 3. `<alloc::vec::Vec<u8>>::into_boxed_slice` (`0x1afd4`) Budget Contracts -/

/-- Stack-parameterized budget contract of `<alloc::vec::Vec<u8>>::into_boxed_slice`
(`= intoBoxedSliceSpec M A lim` at `allocHookStack`, `= intoBoxedSliceSpecX M A lim` at
`extHookStack`). `onPanic = ⌜False⌝` and `onOom = ⌜False⌝` under
`FitsEnv M lim st (IntoBoxedSliceEnv x)`. -/
def intoBoxedSliceSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (VecArg × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ FitsEnv M lim st (IntoBoxedSliceEnv x)⌝ ∗
    x.at A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 32)
  post := fun (x, st) s0 sf =>
    ⌜sf.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length ∧ sf.trace = s0.trace⌝ ∗
    vecHeader x.v x.cap x.ptr (BitVec.ofNat 64 x.bytes.length) ∗
    boxU8Buf A.repAlloc (sf.readReg64 .x0) x.bytes ∗
    A.pool lim (M.stepEvents (intoBoxedSliceEvents x) st) sf ∗ stackAt s0.sp (hookStack + 32)

abbrev intoBoxedSliceSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (VecArg × M.σ) :=
  intoBoxedSliceSpecWithStack M A lim allocHookStack

abbrev intoBoxedSliceSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (VecArg × M.σ) :=
  intoBoxedSliceSpecWithStack M A lim extHookStack

abbrev intoBoxedSliceBudgetSpecWithStack := @intoBoxedSliceSpecWithStack
abbrev intoBoxedSliceBudgetSpec := @intoBoxedSliceSpec
abbrev intoBoxedSliceBudgetSpecX := @intoBoxedSliceSpecX

/-! ## 4. `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (`0xd0a0`) Budget Contracts -/

/-- Stack-parameterized budget contract of `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in`
(`= tryCloneFromRefSpec M A lim` at `allocHookStack`, `= tryCloneFromRefSpecX M A lim` at
`extHookStack`). Under `FitsEnv M lim st (TryCloneFromRefEnv x)`, returns a non-null `Box<[u8]>`
in `(x0, x1)` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def tryCloneFromRefSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (TryCloneSliceCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.src ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      x.bs.length + 1 ≤ 2 ^ 63 ∧ FitsEnv M lim st (TryCloneFromRefEnv x)⌝ ∗
    (x.src ↦ₛ x.bs) ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 48)
  post := fun (x, st) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 x.bs.length ∧
      sf.trace = s0.trace⌝ ∗
    (x.src ↦ₛ x.bs) ∗ boxU8Buf A.repAlloc (sf.readReg64 .x0) x.bs ∗
    A.pool lim (M.stepEvents (tryCloneFromRefEvents x) st) sf ∗ stackAt s0.sp (hookStack + 48)

abbrev tryCloneFromRefSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryCloneSliceCall × M.σ) :=
  tryCloneFromRefSpecWithStack M A lim allocHookStack

abbrev tryCloneFromRefSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryCloneSliceCall × M.σ) :=
  tryCloneFromRefSpecWithStack M A lim extHookStack

abbrev tryCloneFromRefBudgetSpecWithStack := @tryCloneFromRefSpecWithStack
abbrev tryCloneFromRefBudgetSpec := @tryCloneFromRefSpec
abbrev tryCloneFromRefBudgetSpecX := @tryCloneFromRefSpecX

/-! ## 5. `<libsignal_protocol::ratchet::keys::ChainKey>::to_pb` (`0xcf68`) Budget Contracts -/

/-- Stack-parameterized budget contract of `ChainKey::to_pb`
(`= chainKeyToPbSpec M A lim` at `allocHookStack`, `= chainKeyToPbSpecX M A lim` at
`extHookStack`). `onPanic = ⌜False⌝` and `onOom = ⌜False⌝` under `FitsEnv M lim st ChainKeyToPbEnv`. -/
def chainKeyToPbSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (ChainKeyToPbCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.ret ∧
      FitsEnv M lim st ChainKeyToPbEnv⌝ ∗
    (x.self ↦ₛ chainKeyBytes x.ck) ∗ memRegion x.ret 32 ∗ A.pool lim st s ∗
    stackAt s.sp (hookStack + 48)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.self ↦ₛ chainKeyBytes x.ck) ∗
    (∃∗ p' : BitVec 64, optChainKeyAt A.repAlloc ⟨32#64, p'⟩ (some x.ck) x.ret) ∗
    A.pool lim (M.stepEvents chainKeyToPbEvents st) sf ∗ stackAt s0.sp (hookStack + 48)

abbrev chainKeyToPbSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainKeyToPbCall × M.σ) :=
  chainKeyToPbSpecWithStack M A lim allocHookStack

abbrev chainKeyToPbSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainKeyToPbCall × M.σ) :=
  chainKeyToPbSpecWithStack M A lim extHookStack

abbrev chainKeyToPbBudgetSpecWithStack := @chainKeyToPbSpecWithStack
abbrev chainKeyToPbBudgetSpec := @chainKeyToPbSpec
abbrev chainKeyToPbBudgetSpecX := @chainKeyToPbSpecX

/-! ## 6. `<libsignal_core::curve::PublicKey>::serialize` (`0x3e1e0`) Budget Contracts -/

/-- Stack-parameterized budget contract of `PublicKey::serialize`
(`= publicKeySerializeSpec M A lim` at `allocHookStack`, `= publicKeySerializeSpecX M A lim` at
`extHookStack`). `onPanic = ⌜False⌝` and `onOom = ⌜False⌝` under
`FitsEnv M lim st PublicKeySerializeEnv`. -/
def publicKeySerializeSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (PublicKeySerializeCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ FitsEnv M lim st PublicKeySerializeEnv⌝ ∗
    (x.self ↦ₛ x.pk.bytes.toList) ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 32)
  post := fun (x, st) s0 sf =>
    ⌜sf.readReg64 .x1 = 33#64 ∧ sf.trace = s0.trace⌝ ∗
    (x.self ↦ₛ x.pk.bytes.toList) ∗ boxU8Buf A.repAlloc (sf.readReg64 .x0) x.pk.serialize ∗
    A.pool lim (M.stepEvents publicKeySerializeEvents st) sf ∗ stackAt s0.sp (hookStack + 32)

abbrev publicKeySerializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (PublicKeySerializeCall × M.σ) :=
  publicKeySerializeSpecWithStack M A lim allocHookStack

abbrev publicKeySerializeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (PublicKeySerializeCall × M.σ) :=
  publicKeySerializeSpecWithStack M A lim extHookStack

abbrev publicKeySerializeBudgetSpecWithStack := @publicKeySerializeSpecWithStack
abbrev publicKeySerializeBudgetSpec := @publicKeySerializeSpec
abbrev publicKeySerializeBudgetSpecX := @publicKeySerializeSpecX

/-! ## 7. `PrivateKey::derive_public_key_bytes` (`0x3db4c`) `VmPreserved`-Strengthened Contracts -/

/-- `VmPreserved`-strengthened counterpart of `derivePublicKeyBytesSpec` (single pure conjunct in
`post` so `wp_call` extracts both `sf.trace = s0.trace` and `VmPreserved s0 sf`). -/
def derivePublicKeyBytesBudgetSpec (pubKey : PubKeyFn) : Spec DerivePublicKeyBytesCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.secret ∧ s.readReg64 .x8 = x.out⌝ ∗
    (x.secret ↦ₛ x.sec.toList) ∗ memRegion x.out 32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
    (x.secret ↦ₛ x.sec.toList) ∗ (x.out ↦ₛ (pubKey x.sec).toList)

/-- Stack-parameterized `VmPreserved`-strengthened counterpart of `derivePublicKeyBytesStackSpec`. -/
def derivePublicKeyBytesStackBudgetSpec (pubKey : PubKeyFn) (hookStack : Nat := 0) :
    Spec DerivePublicKeyBytesCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.secret ∧ s.readReg64 .x8 = x.out⌝ ∗
    (x.secret ↦ₛ x.sec.toList) ∗ memRegion x.out 32 ∗ stackAt s.sp hookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
    (x.secret ↦ₛ x.sec.toList) ∗ (x.out ↦ₛ (pubKey x.sec).toList) ∗ stackAt s0.sp hookStack

abbrev derivePublicKeyBytesSpec := @derivePublicKeyBytesBudgetSpec
abbrev derivePublicKeyBytesStackSpec := @derivePublicKeyBytesStackBudgetSpec

/-! ## `VmPreserved` Hook Specs (`noAllocShimSpec`, `framelessMemcpySpec`, `session2*SpecX`) & `HookOk` -/

/-- Lift a `HookOk f spec` witness to `HookOk f (withVmPreserved spec)` whenever `f` preserves
`VmPreserved`. -/
theorem hookOk_withVmPreserved {α : Type} {f : State → State} {spec : Spec α}
    (h : HookOk f spec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved spec) := by
  rcases hookSat_withVmPreserved (hooks := fun _ => some f) (name := "")
      ⟨f, rfl, h⟩ (fun _ hf s => by cases hf; exact hvm s) with ⟨_, hf, hok⟩
  cases hf
  exact hok

theorem vmPreserved_hookNoop (s : State) : VmPreserved s (hookNoop s) := by
  simp only [hookNoop, retHook, id_eq, vmPreserved_setPC, vmPreserved_refl_iff]

theorem vmPreserved_hookMemcpy (s : State) : VmPreserved s (hookMemcpy s) := by
  dsimp only [hookMemcpy, retHook]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

theorem vmPreserved_hookMemmove (s : State) : VmPreserved s (hookMemmove s) :=
  vmPreserved_hookMemcpy s

theorem vmPreserved_hookMemset (s : State) : VmPreserved s (hookMemset s) := by
  dsimp only [hookMemset, retHook]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

theorem vmPreserved_pubFromSecretHook (pubKey : PubKeyFn) (s : State) :
    VmPreserved s (pubFromSecretHook pubKey s) := by
  dsimp only [pubFromSecretHook, retHook]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

theorem sessionShimBudget_hookOk : HookOk hookNoop sessionShimBudgetSpec :=
  hookOk_withVmPreserved sessionShim_hookOk vmPreserved_hookNoop

theorem sessionMemcpyRegionBudget_hookOk : HookOk hookMemcpy sessionMemcpyRegionBudgetSpec :=
  hookOk_withVmPreserved hookMemcpy_region_trace_ok vmPreserved_hookMemcpy

theorem sessionMemcpyBudget_hookOk (hookStack : Nat := 4096) :
    HookOk hookMemcpy (sessionMemcpyBudgetSpec hookStack) :=
  hookOk_withVmPreserved (hookMemcpy_trace_ok hookStack) vmPreserved_hookMemcpy

theorem sessionMemmoveBudget_hookOk (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveBudgetSpec hookStack) :=
  hookOk_withVmPreserved (hookMemmove_trace_ok hookStack) vmPreserved_hookMemmove

theorem sessionMemsetRegionBudget_hookOk : HookOk hookMemset sessionMemsetRegionBudgetSpec :=
  hookOk_withVmPreserved hookMemset_region_trace_ok vmPreserved_hookMemset

theorem sessionMemsetBudget_hookOk (hookStack : Nat := 4096) (hstack : 0 < hookStack := by decide) :
    HookOk hookMemset (sessionMemsetBudgetSpec hookStack) :=
  hookOk_withVmPreserved (hookMemset_trace_ok hookStack hstack) vmPreserved_hookMemset

/-- `VmPreserved`-strengthened no-op shim spec (`wp_call`-friendly single `⌜...⌝` postcondition). -/
def noAllocShimBudgetSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝

abbrev noAllocShimSpec : Spec Unit := noAllocShimBudgetSpec

theorem noAllocShim_hookOk : HookOk hookNoop noAllocShimBudgetSpec := by
  have h := hookOk_withVmPreserved
    CryptoVerification.LibsignalTripleRatchet.noAllocShim_hookOk vmPreserved_hookNoop
  intro x R s0 hrun hpre hsp
  rcases h x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec,
      noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- `VmPreserved`-strengthened frameless `memcpy` spec (`wp_call`-friendly single `⌜...⌝`
postcondition). -/
def framelessMemcpyBudgetSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

abbrev framelessMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  framelessMemcpyBudgetSpec

theorem framelessMemcpy_hookOk : HookOk hookMemcpy framelessMemcpyBudgetSpec := by
  have h := hookOk_withVmPreserved
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpy_hookOk vmPreserved_hookMemcpy
  intro x R s0 hrun hpre hsp
  rcases h x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

theorem pubFromSecret_hookOk (pubKey : PubKeyFn) :
    HookOk (pubFromSecretHook pubKey) (derivePublicKeyBytesBudgetSpec pubKey) := by
  have h := hookOk_withVmPreserved
    (CryptoVerification.LibsignalTripleRatchet.pubFromSecret_hookOk pubKey)
    (vmPreserved_pubFromSecretHook pubKey)
  intro x R s0 hrun hpre hsp
  rcases h x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.derivePublicKeyBytesSpec,
      derivePublicKeyBytesBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

theorem subroutine_ok_derivePublicKeyBytes_of_withVmPreserved {P : Program} {addr : BitVec 64}
    {pubKey : PubKeyFn}
    (h : subroutine_ok P addr
      (withVmPreserved (CryptoVerification.LibsignalTripleRatchet.derivePublicKeyBytesSpec pubKey))) :
    subroutine_ok P addr (derivePublicKeyBytesBudgetSpec pubKey) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved,
    CryptoVerification.LibsignalTripleRatchet.derivePublicKeyBytesSpec,
    derivePublicKeyBytesBudgetSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
    satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hq.2.1, hq.1⟩, hq.2.2⟩

theorem subroutine_ok_withVmPreserved_of_derivePublicKeyBytes {P : Program} {addr : BitVec 64}
    {pubKey : PubKeyFn}
    (h : subroutine_ok P addr (derivePublicKeyBytesBudgetSpec pubKey)) :
    subroutine_ok P addr
      (withVmPreserved (CryptoVerification.LibsignalTripleRatchet.derivePublicKeyBytesSpec pubKey)) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved,
    CryptoVerification.LibsignalTripleRatchet.derivePublicKeyBytesSpec,
    derivePublicKeyBytesBudgetSpec] at hq ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hq.1.2, hq.1.1, hq.2⟩

theorem subroutine_ok_noAllocShim_of_sessionShimBudget {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr sessionShimBudgetSpec) :
    subroutine_ok P addr noAllocShimBudgetSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
    noAllocShimBudgetSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hq
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hq.2.1, hq.1⟩, hq.2.2⟩

theorem subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr sessionMemcpyRegionBudgetSpec) :
    subroutine_ok P addr framelessMemcpyBudgetSpec := by
  refine subroutine_ok_mono h (fun ⟨dst, src, bs⟩ R s0 hp => ?_) (fun ⟨dst, src, bs⟩ R s0 sf hq => ?_)
  · dsimp only [framelessMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hp ⊢
    simpa only [sepConj_assoc] using hp
  · dsimp only [framelessMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩

/-- Stack-equipped `VmPreserved` no-op shim spec at `extHookStack`. -/
def session2ShimBudgetSpecX : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp extHookStack

abbrev session2ShimSpecX : Spec Unit := session2ShimBudgetSpecX

/-- Stack-equipped `VmPreserved` `memcpy` spec at `extHookStack`. -/
def session2MemcpyBudgetSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp extHookStack

abbrev session2MemcpySpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  session2MemcpyBudgetSpecX

/-! ## `AllocContractsBudget` & `AllocContractsXBudget` -/

/-- Budget-threaded hypothesis bundle for the Rust allocator (`alloc`, `dealloc`, `realloc`),
no-alloc shim (`shim`), and `memcpy` / `memmove` / `memset` on `tripleRatchetProgAtExt b ext`. -/
structure AllocContractsBudget (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop where
  alloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustCliAllocBudgetSpecBase M A lim false)
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustCliDeallocBudgetSpecBase M A lim)
  realloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustCliReallocBudgetSpecBase M A lim)
  shim :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimBudgetSpec
  session_memcpy : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpyBudgetSpec hookStack)
  session_memcpy_region :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionBudgetSpec
  session_memmove : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (sessionMemmoveBudgetSpec hookStack)
  session_memset : ∀ (hookStack : Nat), 0 < hookStack →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (sessionMemsetBudgetSpec hookStack)
  session_memset_region :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) sessionMemsetRegionBudgetSpec

abbrev AllocContracts := @AllocContractsBudget

/-- `AllocHooksBudget` lifts through `Rust.withPanics (trTrapExterns C abs)`. -/
theorem allocHooksBudget_tripleRatchetExterns_trap (C : Crypto) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    (hA : AllocHooksBudgetBase M A lim abs) :
    AllocHooksBudgetBase M A lim (Rust.withPanics (trTrapExterns C abs)) := by
  have h8 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_alloc" =
      abs "__rustc::__rust_alloc" := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact Option.some.inj (congrArg (·[4]?) (tripleRatchetExterns_abs C 0#64 abs))
  have h9 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_dealloc" =
      abs "__rustc::__rust_dealloc" := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact Option.some.inj (congrArg (·[5]?) (tripleRatchetExterns_abs C 0#64 abs))
  have h10 : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_realloc" =
      abs "__rustc::__rust_realloc" := by
    rw [withPanics_trTrap_ne C abs (by decide)]
    exact Option.some.inj (congrArg (·[6]?) (tripleRatchetExterns_abs C 0#64 abs))
  exact ⟨by simpa [HookSat, h8] using hA.alloc,
    by simpa [HookSat, h9] using hA.dealloc,
    by simpa [HookSat, h10] using hA.realloc⟩

/-- `AllocHooksBudget` lifts through `Rust.withPanics (tripleRatchetExterns C ctl abs)`. -/
theorem allocHooksBudget_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    (hA : AllocHooksBudgetBase M A lim abs) :
    AllocHooksBudgetBase M A lim (Rust.withPanics (tripleRatchetExterns C ctl abs)) := by
  have habs := tripleRatchetExterns_abs C ctl abs
  have h8 : Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_alloc" =
      abs "__rustc::__rust_alloc" := Option.some.inj (congrArg (·[4]?) habs)
  have h9 : Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_dealloc" =
      abs "__rustc::__rust_dealloc" := Option.some.inj (congrArg (·[5]?) habs)
  have h10 : Rust.withPanics (tripleRatchetExterns C ctl abs) "__rustc::__rust_realloc" =
      abs "__rustc::__rust_realloc" := Option.some.inj (congrArg (·[6]?) habs)
  exact ⟨by simpa [HookSat, h8] using hA.alloc,
    by simpa [HookSat, h9] using hA.dealloc,
    by simpa [HookSat, h10] using hA.realloc⟩

namespace AllocContractsBudget

variable {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {ext : String → Option (State → State)}

theorem allocNoOom (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustCliAllocNoOomSpecBase M A lim false) :=
  subroutine_ok_allocNoOom_of_budgetBase hA.alloc

theorem deallocNoOom (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustCliDeallocNoOomSpecBase M A lim) :=
  hA.dealloc

theorem reallocNoOom (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustCliReallocNoOomSpecBase M A lim) :=
  subroutine_ok_reallocNoOom_of_budgetBase hA.realloc

theorem alloc_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem allocNoOom_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomSpecBase M A lim false) :=
  sub_ok_at_of_fnAddr hA.allocNoOom name k hk

theorem dealloc_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocBudgetSpecBase M A lim) :=
  sub_ok_at_of_fnAddr hA.realloc name k hk

theorem reallocNoOom_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocNoOomSpecBase M A lim) :=
  sub_ok_at_of_fnAddr hA.reallocNoOom name k hk

theorem shim_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      noAllocShimBudgetSpec :=
  sub_ok_at_of_fnAddr (subroutine_ok_noAllocShim_of_sessionShimBudget hA.shim) name k hk

theorem session_shim_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      sessionShimBudgetSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem session_memcpy_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpyBudgetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy hookStack) name k hk

theorem session_memcpy_region_ok_at (hA : AllocContractsBudget b M A lim ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      framelessMemcpyBudgetSpec :=
  sub_ok_at_of_fnAddr
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget hA.session_memcpy_region) name k hk

theorem session_memmove_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemmoveBudgetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memmove hookStack) name k hk

theorem session_memset_ok_at (hA : AllocContractsBudget b M A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096) (hstack : 0 < hookStack := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemsetBudgetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memset hookStack hstack) name k hk

theorem session_memset_region_ok_at (hA : AllocContractsBudget b M A lim ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      sessionMemsetRegionBudgetSpec :=
  sub_ok_at_of_fnAddr hA.session_memset_region name k hk

theorem of_tripleRatchetProgAt_trap (b : BitVec 64) (C : Crypto) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    (hA : AllocHooksBudgetBase M A lim abs) :
    AllocContractsBudget b M A lim (trTrapExterns C abs) := by
  have hAt := allocHooksBudget_tripleRatchetExterns_trap C M A lim abs hA
  have hzero : ∀ sym,
      (trTrapProgAt b C abs).fnAddr sym + BitVec.ofNat 64 0 =
        (trTrapProgAt b C abs).fnAddr sym := fun _ => by simp
  refine
    { alloc := ?_
      dealloc := ?_
      realloc := ?_
      shim := ?_
      session_memcpy := fun hookStack => ?_
      session_memcpy_region := ?_
      session_memmove := fun hookStack => ?_
      session_memset := fun hookStack hstack => ?_
      session_memset_region := ?_ }
  · rw [← hzero allocName]
    exact hook_ok_at (name := allocName) (hname := allocName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [allocName]; simp [Rust.isPanicSymbol])
      (by simpa [HookSat, allocName, Rust.withPanics, Rust.isPanicSymbol] using hAt.alloc)
  · rw [← hzero deallocName]
    exact hook_ok_at (name := deallocName) (hname := deallocName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [deallocName]; simp [Rust.isPanicSymbol])
      (by simpa [HookSat, deallocName, Rust.withPanics, Rust.isPanicSymbol] using hAt.dealloc)
  · rw [← hzero reallocName]
    exact hook_ok_at (name := reallocName) (hname := reallocName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [reallocName]; simp [Rust.isPanicSymbol])
      (by simpa [HookSat, reallocName, Rust.withPanics, Rust.isPanicSymbol] using hAt.realloc)
  · rw [← hzero shimName]
    exact hook_ok_at (name := shimName) (hname := shimName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [shimName]; simp [Rust.isPanicSymbol]) ⟨hookNoop, rfl, sessionShimBudget_hookOk⟩
  · rw [← hzero memcpyName]
    exact hook_ok_at (name := memcpyName) (hname := memcpyName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [memcpyName]; simp [Rust.isPanicSymbol])
      ⟨hookMemcpy, rfl, sessionMemcpyBudget_hookOk hookStack⟩
  · rw [← hzero memcpyName]
    exact hook_ok_at (name := memcpyName) (hname := memcpyName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [memcpyName]; simp [Rust.isPanicSymbol])
      ⟨hookMemcpy, rfl, sessionMemcpyRegionBudget_hookOk⟩
  · rw [← hzero memmoveName]
    exact hook_ok_at (name := memmoveName) (hname := memmoveName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [memmoveName]; simp [Rust.isPanicSymbol])
      ⟨hookMemmove, rfl, sessionMemmoveBudget_hookOk hookStack⟩
  · rw [← hzero memsetName]
    exact hook_ok_at (name := memsetName) (hname := memsetName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [memsetName]; simp [Rust.isPanicSymbol])
      ⟨hookMemset, rfl, sessionMemsetBudget_hookOk hookStack hstack⟩
  · rw [← hzero memsetName]
    exact hook_ok_at (name := memsetName) (hname := memsetName)
      rfl (Nat.add_zero _) (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by dsimp [memsetName]; simp [Rust.isPanicSymbol])
      ⟨hookMemset, rfl, sessionMemsetRegionBudget_hookOk⟩

theorem of_tripleRatchetProgAt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State)) (hA : AllocHooksBudgetBase M A lim abs) :
    AllocContractsBudget b M A lim (tripleRatchetExterns C ctl abs) := by
  have hT := of_tripleRatchetProgAt_trap b C M A lim abs hA
  have hkit := trapsOnly_trTrap_kit b C ctl abs
  exact
    { alloc := hkit.fnAddr allocName ▸ subroutine_ok_kit_of_trTrap hT.alloc
      dealloc := hkit.fnAddr deallocName ▸ subroutine_ok_kit_of_trTrap hT.dealloc
      realloc := hkit.fnAddr reallocName ▸ subroutine_ok_kit_of_trTrap hT.realloc
      shim := hkit.fnAddr shimName ▸ subroutine_ok_kit_of_trTrap hT.shim
      session_memcpy := fun hs =>
        hkit.fnAddr memcpyName ▸ subroutine_ok_kit_of_trTrap (hT.session_memcpy hs)
      session_memcpy_region :=
        hkit.fnAddr memcpyName ▸ subroutine_ok_kit_of_trTrap hT.session_memcpy_region
      session_memmove := fun hs =>
        hkit.fnAddr memmoveName ▸ subroutine_ok_kit_of_trTrap (hT.session_memmove hs)
      session_memset := fun hs hpos =>
        hkit.fnAddr memsetName ▸ subroutine_ok_kit_of_trTrap (hT.session_memset hs hpos)
      session_memset_region :=
        hkit.fnAddr memsetName ▸ subroutine_ok_kit_of_trTrap hT.session_memset_region }

end AllocContractsBudget

/-- Refinement-compatible budget-threaded allocator + `mem*` + `shim` contract bundle on
`tripleRatchetProgAtExt img.base ext`: all fields carry `.inImage img` and `extHookStack`. -/
structure AllocContractsXBudget (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop where
  alloc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocName)
      ((rustCliAllocBudgetSpecWithStackBase M A lim false extHookStack).inImage img)
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName)
      ((rustCliDeallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img)
  realloc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr reallocName)
      ((rustCliReallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img)
  shim : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr shimName)
      ((withStack sessionShimBudgetSpec hookStack).inImage img)
  session_memcpy : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((sessionMemcpyBudgetSpec hookStack).inImage img)
  session_memcpy_region : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((withStack sessionMemcpyRegionBudgetSpec hookStack).inImage img)
  session_memmove : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memmoveName)
      ((sessionMemmoveBudgetSpec hookStack).inImage img)
  session_memset : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memsetName)
      ((sessionMemsetBudgetSpec hookStack).inImage img)
  session_memset_region : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memsetName)
      ((withStack sessionMemsetRegionBudgetSpec hookStack).inImage img)

abbrev AllocContractsX := @AllocContractsXBudget

namespace AllocContractsXBudget

variable {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {ext : String → Option (State → State)}

theorem alloc_ok_at (hA : AllocContractsXBudget img M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustCliAllocBudgetSpecWithStackBase M A lim false extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem dealloc_ok_at (hA : AllocContractsXBudget img M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustCliDeallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContractsXBudget img M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustCliReallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hA.realloc name k hk

theorem shim_ok_at (hA : AllocContractsXBudget img M A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionShimBudgetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.shim hookStack hstack hstack_le) name k hk

theorem session_shim_ok_at (hA : AllocContractsXBudget img M A lim ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionShimBudgetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.shim hookStack hstack hstack_le) name k hk

theorem session_memcpy_ok_at (hA : AllocContractsXBudget img M A lim ext)
    (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemcpyBudgetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy hookStack hstack hstack_le) name k hk

theorem session_memcpy_region_ok_at (hA : AllocContractsXBudget img M A lim ext)
    (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionMemcpyRegionBudgetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region hookStack hstack hstack_le) name k hk

theorem session_memmove_ok_at (hA : AllocContractsXBudget img M A lim ext)
    (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemmoveBudgetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memmove hookStack hstack hstack_le) name k hk

theorem session_memset_ok_at (hA : AllocContractsXBudget img M A lim ext)
    (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemsetBudgetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memset hookStack hstack hstack_le) name k hk

theorem session_memset_region_ok_at (hA : AllocContractsXBudget img M A lim ext)
    (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionMemsetRegionBudgetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memset_region hookStack hstack hstack_le) name k hk

theorem of_AllocContracts (img : Obj.Image)
    (hA : AllocContractsBudget img.base M A lim ext) :
    AllocContractsXBudget img M A lim ext where
  alloc := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_rustCliAllocBudget_withStackBase (by decide) (by decide) hA.alloc)
  dealloc := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_rustCliDeallocBudget_externWithStackBase (by decide) (by decide) hA.dealloc)
  realloc := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_rustCliReallocBudget_externWithStackBase (by decide) (by decide) hA.realloc)
  shim := fun hs _ _ => subroutine_ok_inImage_of_subroutine_ok img
    (CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok hA.shim hs)
  session_memcpy := fun hs _ _ => subroutine_ok_inImage_of_subroutine_ok img (hA.session_memcpy hs)
  session_memcpy_region := fun hs _ _ => subroutine_ok_inImage_of_subroutine_ok img
    (CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok
      hA.session_memcpy_region hs)
  session_memmove := fun hs _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (hA.session_memmove hs)
  session_memset := fun hs hge _ =>
    subroutine_ok_inImage_of_subroutine_ok img
      (hA.session_memset hs (Nat.lt_of_lt_of_le (by decide : 0 < extHookStack) hge))
  session_memset_region := fun hs _ _ => subroutine_ok_inImage_of_subroutine_ok img
    (CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok
      hA.session_memset_region hs)

end AllocContractsXBudget

/-! ## Call-Site `_ok_at` Helpers Mirroring `Alloc.Defs` -/

theorem shim_ok_at2_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) noAllocShimBudgetSpec :=
  hA.shim_ok_at name k hk

theorem noAllocShim_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) noAllocShimBudgetSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl hk
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, noAllocShim_hookOk⟩

theorem noAllocShim_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) noAllocShimBudgetSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (noAllocShim_ok_at_trap (b := b) (C := C) (abs := abs) hk)

theorem memcpy_ok_at2_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) framelessMemcpyBudgetSpec :=
  hA.session_memcpy_region_ok_at name k hk

theorem framelessMemcpy_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) framelessMemcpyBudgetSpec :=
  hook_ok_at (hname := "memcpy") rfl hk
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    ⟨hookMemcpy, rfl, framelessMemcpy_hookOk⟩

theorem framelessMemcpy_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      framelessMemcpyBudgetSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (framelessMemcpy_ok_at_trap (b := b) (C := C) (abs := abs) hk)

theorem alloc_ok_at_norm_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) :=
  hA.alloc_ok_at name k hk

theorem allocNoOom_ok_at_norm_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomSpecBase M A lim false) :=
  hA.allocNoOom_ok_at name k hk

theorem alloc_ok_at_norm_trap {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) :=
  alloc_ok_at_norm_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA) hk

theorem alloc_ok_at_norm {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (alloc_ok_at_norm_trap (b := b) (C := C) hA hk)

theorem dealloc_ok_at_norm_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) :=
  hA.dealloc_ok_at name k hk

theorem dealloc_ok_at_norm_trap {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) :=
  dealloc_ok_at_norm_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA) hk

theorem dealloc_ok_at_norm {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (dealloc_ok_at_norm_trap (b := b) (C := C) hA hk)

theorem realloc_ok_at_norm_ext {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocBudgetSpecBase M A lim) :=
  hA.realloc_ok_at name k hk

theorem reallocNoOom_ok_at_norm_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocNoOomSpecBase M A lim) :=
  hA.reallocNoOom_ok_at name k hk

theorem realloc_ok_at_norm_trap {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocBudgetSpecBase M A lim) :=
  realloc_ok_at_norm_ext (AllocContractsBudget.of_tripleRatchetProgAt_trap b C M A lim abs hA) hk

theorem realloc_ok_at_norm {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooksBudgetBase M A lim abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocBudgetSpecBase M A lim) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (realloc_ok_at_norm_trap (b := b) (C := C) hA hk)

theorem shim_ok_at2_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (session2ShimBudgetSpecX.inImage img) := by
  have h := hA.shim_ok_at name k extHookStack (by decide) (by decide) hk
  refine subroutine_ok_mono h (fun _ R s0 hpre => ?_) (fun _ R s0 sf hpost => ?_)
  · dsimp only [Spec.inImage, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, session2ShimBudgetSpecX] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  · dsimp only [Spec.inImage, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, session2ShimBudgetSpecX] at hpost ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩

theorem memcpy_ok_at2_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (session2MemcpyBudgetSpecX.inImage img) := by
  have h := hA.session_memcpy_region_ok_at name k extHookStack (by decide) (by decide) hk
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · dsimp only [Spec.inImage, withStack, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec,
      session2MemcpyBudgetSpecX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · rcases x with ⟨dst, src, bs⟩
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec,
      session2MemcpyBudgetSpecX] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩

theorem alloc_ok_at_norm_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustCliAllocBudgetSpecWithStackBase M A lim false extHookStack).inImage img) :=
  hA.alloc_ok_at name k hk

theorem dealloc_ok_at_norm_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustCliDeallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img) :=
  hA.dealloc_ok_at name k hk

theorem realloc_ok_at_norm_ext_x {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustCliReallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img) :=
  hA.realloc_ok_at name k hk

theorem pubFromSecret_ok_at_of_contract {α : Type} {b : BitVec 64}
    {H : String → Option (State → State)} {spec : Spec α}
    (hpub : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr pubFromSecretName) spec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff pubFromSecretName := by simp only [arm64_norm]) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k) spec :=
  CryptoVerification.LibsignalTripleRatchet.pubFromSecret_ok_at_of_contract hpub hk

theorem pubFromSecret_ok_at_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff pubFromSecretName := by simp only [arm64_norm]) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      (derivePublicKeyBytesBudgetSpec C.pubKey) :=
  hook_ok_at (hname := pubFromSecretName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by dsimp [pubFromSecretName]; simp [Rust.isPanicSymbol])
    ⟨pubFromSecretHook C.pubKey, rfl, pubFromSecret_hookOk C.pubKey⟩

theorem pubFromSecret_ok_at {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff pubFromSecretName := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (derivePublicKeyBytesBudgetSpec C.pubKey) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (pubFromSecret_ok_at_trap (b := b) (C := C) (abs := abs) hk)

theorem derivePublicKeyBytesStack_of_spec {P : Program} {addr : BitVec 64}
    {pubKey : PubKeyFn} (hookStack : Nat)
    (h : subroutine_ok P addr (derivePublicKeyBytesBudgetSpec pubKey)) :
    subroutine_ok P addr (derivePublicKeyBytesStackBudgetSpec pubKey hookStack) := by
  refine subroutine_ok_refine_frame h fun x R s0 hpre =>
    ⟨x, stackAt s0.sp hookStack, ?_, fun sf hpost => ?_⟩
  · simp only [derivePublicKeyBytesStackBudgetSpec, derivePublicKeyBytesBudgetSpec,
      sepConj_assoc] at hpre ⊢
    exact hpre
  · simp only [derivePublicKeyBytesStackBudgetSpec, derivePublicKeyBytesBudgetSpec,
      sepConj_assoc] at hpost ⊢
    exact hpost

end LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
