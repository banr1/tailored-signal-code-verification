/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `RawVecInner::reserve::do_reserve_and_handle` (`0x4cac`)

Verifies `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle` against
`doReserveRawSpecX` and `doReserveSpecX` at `doReserveStackX = 16496` bytes for an arbitrary
`A : RustAlloc`, on `SP2Ext` and under relocatable `[LibsignalPlacement]` (Block `13`, calling
`finish_grow` in Block `45`). Also lifts 4 KiB-framed allocator and `memmove` stub contracts to
`extHookStack = 16384`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.DoReserveFacts
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E CryptoVerification.E2E.HooksE
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_DoReserveExt : True := trivial

/-! ## Allocator contract adapters to `Stage1X.AllocContractsX` -/

/-- Bridges 4 KiB-framed allocator contracts (`withExternStackFromAlloc'`) together with `shim`
and `memmove` at `extHookStack = 16384` to `Stage1X.AllocContractsX img A ext`. -/
theorem allocContractsX_of_stage2Stubs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff allocName)
      (((rustAllocSpec A).withExternStackFromAlloc').inImage img))
    (hdealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff deallocName)
      (((rustDeallocLayoutSpec' A).withExternStackFromAlloc').inImage img))
    (hrealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff reallocName)
      (((rustReallocSpec A).withExternStackFromAlloc').inImage img))
    (hshim : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff shimName)
      ((sessionShimSpec.withHookStack CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img))
    (hmemmove : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memmoveName)
      ((sessionMemmoveSpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext where
  alloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' halloc (fun ⟨size, align⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc', rustAllocSpec,
        Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc', rustAllocSpec,
        Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' hdealloc (fun ⟨p, size, align⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustDeallocLayoutSpec', rustDeallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hlay⟩, hmem⟩ := hpre
      refine ⟨hlay, ⟨hx0, hx1, hx2⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustDeallocLayoutSpec', rustDeallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  realloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' hrealloc (fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustReallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, _hlay_old, hlay_new⟩, hmem⟩ := hpre
      refine ⟨⟨hx0, hx1, hx2, hx3, hlay_new, hbs1, hbs2⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, Proofs.libsignal.Stage1X.rustReallocSpecWithStack,
        Spec.withExternStackFromAlloc', rustReallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := by
    rw [SP2Ext_fnAddr]
    exact hshim
  session_memmove := by
    rw [SP2Ext_fnAddr]
    exact hmemmove

theorem allocContractsX_of_stage2ContractsA0 {img : Obj.Image} {ext : String → Option (State → State)}
    (hC : Stage2ContractsA0 img ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img HooksE.A0 ext :=
  allocContractsX_of_stage2Stubs hC.alloc_A0 hC.deallocLayout_A0 hC.realloc_A0 hC.shim hC.memmove

/-- Frames `sessionMemmoveSpec stk` up to `extHookStack = 16384` on `SP2Ext` when `stk ≤ extHookStack`. -/
theorem sessionMemmove_extHookStack_of_le {img : Obj.Image}
    {ext : String → Option (State → State)} {entry : BitVec 64} {stk : Nat}
    (hle : stk ≤ CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (h : subroutine_ok (SP2Ext img.base ext) entry ((sessionMemmoveSpec stk).inImage img)) :
    subroutine_ok (SP2Ext img.base ext) entry
      ((sessionMemmoveSpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) := by
  have hmax : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ 2 ^ 64 := by decide
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp CryptoVerification.LibsignalTripleRatchet.extHookStack =
        stackAt sp stk ∗
          memRegion (sp - BitVec.ofNat 64 CryptoVerification.LibsignalTripleRatchet.extHookStack)
            (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk) := by
    intro sp
    have hs := ProofLib.stackAt_split_bottom sp stk
      (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk)
      (by omega)
    rw [Nat.add_sub_of_le hle, sepConj_comm] at hs
    exact hs
  refine subroutine_ok_inImage_map' h (fun x R s0 hpre => ?_)
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
  refine ⟨x,
    memRegion (s0.sp - BitVec.ofNat 64 CryptoVerification.LibsignalTripleRatchet.extHookStack)
      (CryptoVerification.LibsignalTripleRatchet.extHookStack - stk) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · simp only [sessionMemmoveSpec, libcMemmoveSpec, hsplit s0.sp] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · simp only [sessionMemmoveSpec, libcMemmoveSpec, hsplit s0.sp] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost

theorem allocContractsX_of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext where
  alloc := by
    refine subroutine_ok_inImage_map' hA.alloc (fun ⟨size, align⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpre ⊢
      exact hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := by
    refine subroutine_ok_inImage_map' hA.dealloc (fun ⟨p, size, align⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpost ⊢
      exact hpost
  realloc := by
    refine subroutine_ok_inImage_map' hA.realloc
      (fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, hlay_old, hlay_new⟩, hmem⟩ := hpre
      exact ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2⟩,
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := hA.shim CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide)
  session_memmove :=
    hA.session_memmove CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide)

/-- Builds `Stage1X.AllocContractsX img A ext` from 4 KiB-framed allocator contracts, `shim` at
`extHookStack`, and `sessionMemmoveSpec` at any stack budget `stk ≤ extHookStack`. -/
theorem allocContractsX_of_memHookStubs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hle : stk ≤ CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (halloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff allocName)
      (((rustAllocSpec A).withExternStackFromAlloc').inImage img))
    (hdealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff deallocName)
      (((rustDeallocLayoutSpec' A).withExternStackFromAlloc').inImage img))
    (hrealloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff reallocName)
      (((rustReallocSpec A).withExternStackFromAlloc').inImage img))
    (hshim : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff shimName)
      ((sessionShimSpec.withHookStack CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img))
    (hmemmove : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memmoveName)
      ((sessionMemmoveSpec stk).inImage img)) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext :=
  allocContractsX_of_stage2Stubs halloc hdealloc hrealloc hshim
    (sessionMemmove_extHookStack_of_le hle hmemmove)

/-! ## Stack budget and specifications at `doReserveStackX` -/

/-- Stack budget for `do_reserve_and_handle` (`finishGrowStackX + 64 = 16496` bytes). -/
abbrev doReserveStackX : Nat := Proofs.libsignal.Stage1X.finishGrowStackX + 64

/-- Raw specification of `do_reserve_and_handle` at `doReserveStackX`. -/
def doReserveRawSpecX (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      x.bs.length ≤ x.cap.toNat ∧ x.ptr ≠ 0#64 ∧ newCap + 1 ≤ 2 ^ 63⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp Proofs.libsignal.Hooks2.doReserveStackX
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp Proofs.libsignal.Hooks2.doReserveStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- High-level `Vec<u8>` specification of `do_reserve_and_handle` at `doReserveStackX`. -/
def doReserveSpecX (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp Proofs.libsignal.Hooks2.doReserveStackX
  post := fun x s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool ∗ stackAt s0.sp Proofs.libsignal.Hooks2.doReserveStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Arithmetic and stack helpers -/

private theorem adds_cs_eq_false_x {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_eq_x {cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : reserveCap cap.toNat len additional + 1 ≤ 2 ^ 63) :
    (if (8#64).ult (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else 8#64) =
      BitVec.ofNat 64 (reserveCap cap.toNat len additional) := by
  have hmax : max (max (len + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [reserveCap]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : (8#64).ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change 8 < max (len + additional) (2 * cap.toNat) at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change ¬ 8 < max (len + additional) (2 * cap.toNat) at hc2
    change 8 = max (max (len + additional) (2 * cap.toNat)) 8
    omega

private theorem memRegion_24_cells_x (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_doReserveX (sp : BitVec 64) :
    stackAt sp Proofs.libsignal.Hooks2.doReserveStackX =
      stackAt (sp - 64#64) Proofs.libsignal.Stage1X.finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp 16432 8 (by decide)
  change stackAt sp Proofs.libsignal.Hooks2.doReserveStackX =
    stackAt (sp - 64#64) Proofs.libsignal.Stage1X.finishGrowStackX ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

/-! ## Cell-unfolded `finish_grow` specs (`stride = 1, align = 1`) -/

private abbrev FG1GhostX :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def finishGrow1ZeroSpecX (A : RustAlloc) : Spec FG1GhostX where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' new.toNat 1 ∗ memRegion p' new.toNat)) ∗
      A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_1_zero_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName) ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName)
      ((finishGrow1ZeroSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, finishGrow1ZeroSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 1#64, 1#64, []⟩
  have hlay : LayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img).pre hcall s0 ∗ R := by
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells_x, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine subroutine_ok.mono_outcome hfg hcall R s0 hpc hrun hpre' hsp fun _ hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow1ZeroSpecX, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * (1#64 : BitVec 64).toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      have hm1 : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
      have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [hm1] at hq ⊢
      rw [ha1] at hq
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact False.elim (not_satisfies_false_sepConj hq)

private def finishGrow1NeSpecX (A : RustAlloc) : Spec FG1GhostX where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX
  post := fun (out, cap, ptr, new, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
          (A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length))) ∗
      A.pool ∗ stackAt fsp Proofs.libsignal.Stage1X.finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_1_ne_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfg : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName) ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr finishGrowName)
      ((finishGrow1NeSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, finishGrow1NeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 1#64, 1#64, bs⟩
  have hlay : LayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  have hpre' : s0.mem ⊨ ((Proofs.libsignal.Stage1X.finishGrowSpecX A).inImage img).pre hcall s0 ∗ R := by
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells_x, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_cap, ha1, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine subroutine_ok.mono_outcome hfg hcall R s0 hpc hrun hpre' hsp fun _ hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow1NeSpecX, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm_new : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_new, hm_cap, ha1] at hq
    refine ⟨tag, p', BitVec.ofNat 64 new.toNat, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hq.1.2, ?_⟩
      simpa only [sepConj_assoc] using hq.2
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, ?_⟩
      simpa only [sepConj_assoc] using hq.2
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact False.elim (not_satisfies_false_sepConj hq)

/-! ## Verification on `SP2Ext` -/

private theorem SepWPp.ite_elim_pure1_x {prog : Program} {ret : BitVec 64} {s : State}
    {c : Prop} [Decidable c] {φ ψ : Prop} {R2 F : SepProp} {Q Qp : State → SepProp → Prop}
    (hthen : c → φ → SepWPp prog ret s F Q Qp)
    (helse : ¬ c → ψ → SepWPp prog ret s (R2 ∗ F) Q Qp) :
    SepWPp prog ret s ((if c then ⌜φ⌝ else ⌜ψ⌝ ∗ R2) ∗ F) Q Qp := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact SepWPp.pure_elim (hthen hc)
  · simp only [hc, ite_false, sepConj_assoc]; exact SepWPp.pure_elim (helse hc)

private theorem SepWPp.ite_elim_pure2_x {prog : Program} {ret : BitVec 64} {s : State}
    {c : Prop} [Decidable c] {φ ψ : Prop} {R1 R2 F : SepProp} {Q Qp : State → SepProp → Prop}
    (hthen : c → φ → SepWPp prog ret s (R1 ∗ F) Q Qp)
    (helse : ¬ c → ψ → SepWPp prog ret s (R2 ∗ F) Q Qp) :
    SepWPp prog ret s ((if c then ⌜φ⌝ ∗ R1 else ⌜ψ⌝ ∗ R2) ∗ F) Q Qp := by
  by_cases hc : c
  · simp only [hc, ite_true, sepConj_assoc]; exact SepWPp.pure_elim (hthen hc)
  · simp only [hc, ite_false, sepConj_assoc]; exact SepWPp.pure_elim (helse hc)

set_option maxHeartbeats 800000 in
/-- `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle` (`0x4cac`) satisfies
`(doReserveRawSpecX A).inImage img` on `SP2Ext img.base ext` under `Stage1X.AllocContractsX`. -/
theorem do_reserve_raw_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr doReserveName)
      ((Proofs.libsignal.Hooks2.doReserveRawSpecX A).inImage img) := by
  have hfg := finish_grow_ok_ext_x hA
  unfold Spec.inImage Proofs.libsignal.Hooks2.doReserveRawSpecX
  simp only [stackAt_doReserveX, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff doReserveName = num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") :=
    doReserve_fnOff
  have hpanic := panic_at_handle_error_ext (b := img.base) (ext := ext)
    hfn (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) (by simp only [arm64_norm])
  have hfg0 := finish_grow_1_zero_ok_x hfg
  have hfg1 := finish_grow_1_ne_ok_x hfg
  rw [Program.fnAddr_rel (name := doReserveName)
    hfn finishGrow_fnOff (k := num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) 140
  wpp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hinv0 : CryptoVerification.LibsignalTripleRatchet.ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at h ⊢; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false_x (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [h_5, h_4]; omega)
  have hnew_eq := reserve_new_cap_eq_x (cap := cap) h_4 h_5 hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h_8)
    subst hbs
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := by
      exact hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := entry + bv% (88))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by first | rfl | assumption) (by first | rfl | assumption)
    refine SepWPp.ite_elim_pure1_x (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := entry + bv% (88))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.seq_inImage (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done hpc_sf hrun_sf
    refine SepWPp.ite_elim_pure2_x (fun htag htrace => ?_) (fun _ ⟨hw0, hp', htrace⟩ => ?_)
    · subst htag
      rw [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]"))
      wp_steps
      apply SepWP.done (by rfl) (by exact hrun_sf)
      refine SepWPp.panic (by exact hrun_sf) hpanic fun hm => ?_
      rw [← sepConj_assoc]
      exact allowPanic_panicked
        (allocFailedIn_of_eq (htrace : (Rust.panicked _).trace = s0.trace ++ [allocFailedEvent])) hm
    · subst hw0
      rw [sepConj_assoc, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

private theorem vecU8At_eq_x (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

/-- `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle` (`0x4cac`) satisfies
`(doReserveSpecX A).inImage img` on `SP2Ext img.base ext` under `Stage1X.AllocContractsX`. -/
theorem do_reserve_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr doReserveName)
      ((Proofs.libsignal.Hooks2.doReserveSpecX A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, Proofs.libsignal.Hooks2.doReserveSpecX, vecU8At_eq_x, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((Proofs.libsignal.Hooks2.doReserveRawSpecX A).inImage img).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [Spec.inImage, Proofs.libsignal.Hooks2.doReserveRawSpecX, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine subroutine_ok.mono_outcome (do_reserve_raw_ok_ext_x hA) x
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, Proofs.libsignal.Hooks2.doReserveRawSpecX, Proofs.libsignal.Hooks2.doReserveSpecX, vecU8At_eq_x] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rwa [doReserve_post_repack]
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, Proofs.libsignal.Hooks2.doReserveRawSpecX, Proofs.libsignal.Hooks2.doReserveSpecX] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact False.elim (not_satisfies_false_sepConj hq)

theorem do_reserve_raw_ok_of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName)
      ((Proofs.libsignal.Hooks2.doReserveRawSpecX A).inImage img) :=
  do_reserve_raw_ok_ext_x (allocContractsX_of_trAllocContractsX hA)

theorem do_reserve_ok_of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName)
      ((Proofs.libsignal.Hooks2.doReserveSpecX A).inImage img) :=
  do_reserve_ok_ext_x (allocContractsX_of_trAllocContractsX hA)

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `13`) -/

section Placed

theorem allocContractsPlaced_of_stage2ContractsA0Placed [LibsignalPlacement] {H : LibsignalHooks}
    (hC : Stage2ContractsA0Placed H) :
    Proofs.libsignal.Stage1X.AllocContractsPlaced HooksE.A0 H where
  alloc := fun {callerProg callerBlk _} => by
    refine subroutine_ok_withLsCl_map' (hC.alloc_A0 (callerProg := callerProg))
      (fun ⟨size, align⟩ R s0 hpre => ⟨(size, align), R, ?_, fun sf hpost => ?_⟩)
    · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc',
        rustAllocSpec, Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc',
        rustAllocSpec, Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := fun {callerProg callerBlk _} => by
    refine subroutine_ok_withLsCl_map' (hC.deallocLayout_A0 (callerProg := callerProg))
      (fun ⟨p, size, align⟩ R s0 hpre => ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩)
    · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustDeallocLayoutSpec', rustDeallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hlay⟩, hmem⟩ := hpre
      exact ⟨hlay, ⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustDeallocLayoutSpec', rustDeallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  realloc := fun {callerProg callerBlk _} => by
    refine subroutine_ok_withLsCl_map' (hC.realloc_A0 (callerProg := callerProg))
      (fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre =>
        ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩)
    · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustReallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, _hlay_old, hlay_new⟩, hmem⟩ := hpre
      exact ⟨⟨hx0, hx1, hx2, hx3, hlay_new, hbs1, hbs2⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack,
        Spec.withExternStackFromAlloc', rustReallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := hC.shim
  session_memmove := hC.memmove
  panic_handle_error := hC.panic_handle_error
  panic_handle_alloc_error := hC.panic_handle_alloc_error

private theorem finish_grow_1_zero_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.finishGrowSpecX A))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow1ZeroSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg (fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpre => ?_)
  simp only [finishGrow1ZeroSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 1#64, 1#64, []⟩
  have hlay : LayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  refine ⟨hcall, R, ?_, fun sf hq => ?_⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_cells_x, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow1ZeroSpecX, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * (1#64 : BitVec 64).toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      have hm1 : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
      have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [hm1] at hq ⊢; rw [ha1] at hq
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, by simpa only [sepConj_assoc] using hq.2⟩

private theorem finish_grow_1_ne_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Stage1X.finishGrowSpecX A))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow1NeSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg (fun ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ R s0 hpre => ?_)
  simp only [finishGrow1NeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 1#64, 1#64, bs⟩
  have hlay : LayoutOk (new.toNat * (1#64 : BitVec 64).toNat) (1#64 : BitVec 64).toNat := by
    refine ⟨by change 0 < new.toNat * 1; omega, ⟨0, rfl⟩, ?_⟩
    change new.toNat * 1 + 1 ≤ 2 ^ 63; omega
  refine ⟨hcall, R, ?_, fun sf hq => ?_⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_cells_x, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_cap, ha1, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, by decide, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  · simp only [Proofs.libsignal.Stage1X.finishGrowSpecX, finishGrow1NeSpecX, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    have hm_new : new.toNat * (1#64 : BitVec 64).toNat = new.toNat := Nat.mul_one _
    have hm_cap : cap.toNat * (1#64 : BitVec 64).toNat = cap.toNat := Nat.mul_one _
    have ha1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [hm_new, hm_cap, ha1] at hq
    refine ⟨tag, p', BitVec.ofNat 64 new.toNat, ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq.1.1, hq.1.2.1, hq.1.2.2.2⟩, by simpa only [sepConj_assoc] using hq.2⟩

/-- Relocatable `RawVecInner::reserve::do_reserve_and_handle` (Block `13`) satisfies
`withLsCodeLoaded lsmpl (doReserveRawSpecX A)` under `Stage1X.AllocContractsPlaced`. -/
theorem do_reserve_raw_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.doReserveRawSpecX A)) := by
  have hfg := finish_grow_placed_ok_ext_x hA
  have hpanic := hA.externAt_handle_error (callerProg := (blkPC_13).rebase (blkPl_13).base H)
  have hfg0 := ls_subroutine_ok_of_callee (callerProg := (blkPC_13).rebase (blkPl_13).base H)
    (finish_grow_1_zero_placed_ok_x hfg)
  have hfg1 := ls_subroutine_ok_of_callee (callerProg := (blkPC_13).rebase (blkPl_13).base H)
    (finish_grow_1_ne_placed_ok_x hfg)
  change subroutine_ok _ (lsmpl.base 45) _ at hfg0 hfg1
  dsimp only [withLsCodeLoaded, finishGrow1ZeroSpecX, finishGrow1NeSpecX] at hfg0 hfg1
  clear hfg
  unfold withLsCodeLoaded Proofs.libsignal.Hooks2.doReserveRawSpecX
  simp only [stackAt_doReserveX, sepExists_sepConj_right]
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, additional⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by
    dsimp only [reserveCap] at *; omega
  have hmax : max (max (bs.length + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := hbound
  have hcs := adds_cs_eq_false_x (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq_x (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero]
    apply SepWPp.of_sepWP (mid := (blkPl_13).base + bv% (88))
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl1
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ CryptoVerification.lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) hpanic fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    apply SepWPp.of_sepWP (mid := (blkPl_13).base + bv% (88))
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl1
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ CryptoVerification.lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) hpanic fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

/-- Relocatable `RawVecInner::reserve::do_reserve_and_handle` (Block `13`) satisfies
`withLsCodeLoaded lsmpl (doReserveSpecX A)` under `Stage1X.AllocContractsPlaced`. -/
theorem do_reserve_placed_ok_ext_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H)
      (blkPl_13).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.doReserveSpecX A)) :=
  CryptoVerification.LibsignalTripleRatchet.do_reserve_placed_ok_of_raw_opt
    (fgStack := CryptoVerification.LibsignalTripleRatchet.extHookStack + 48)
    (do_reserve_raw_placed_ok_ext_x hA)

theorem do_reserve_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok callerProg (lsmpl.base 13)
      (withLsCl lsmpl (Proofs.libsignal.Hooks2.doReserveSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (do_reserve_placed_ok_ext_x hA)

end Placed

end Proofs.libsignal.Hooks2
