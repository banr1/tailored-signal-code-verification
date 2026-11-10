/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Outer
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder>::into_pb`: Placed Outer Loops (Block `375`)

Relocatable `[LibsignalPlacement]` verification of the `.polys` and `.points` outer serialization
loops for `<spqr::encoding::polynomial::PolyEncoder>::into_pb`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.EncoderIntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop (vecGF16Of vecGF16ListOf
  pointListOf_eq_vecGF16ListOf polyListOf_eq_vecGF16ListOf
  dropGluePoly16Stack DropGluePoly16Ghost dropGluePoly16Spec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  fp_sub_48 fp_sub_32 fp_sub_24 fp_sub_16 fp_sub_8 fp_sub_40
  fp_sub_48_int fp_sub_32_int fp_sub_24_int fp_sub_16_int fp_sub_8_int fp_sub_40_int
  sp_add_56_add_8 sp_add_80_add_8 sp_add_104_add_8
  ofNat_add_one madd_24_eq

variable [LibsignalPlacement]

/-- Finish one iteration of the `.polys` outer loop (`+352 -> +144 -> +188 / +616`) in `[LibsignalPlacement]`. -/
theorem polys_outer_finish_iter_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 : State) (fsp ptr_polys : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j remLen : Nat) (htot : j + (remLen + 1) = 16)
    (bs : List (BitVec 8)) (cap_c ptr_c s80 s88 s96 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 352#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x19 + 8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 j)
    (hx24 : s.readReg64 .x24 = fsp)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = 1#64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 j)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (if j + 1 = 16 then
        (blkPl_375).base + 616#64
       else
        (blkPl_375).base + 188#64)
      s
      (((fsp + 24#64) ↦₆₄ 16#64) ∗
        ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 80#64) ↦₆₄ s80) ∗
        ((fsp + 88#64) ↦₆₄ s88) ∗
        ((fsp + 96#64) ↦₆₄ s96) ∗
        ((fsp + 104#64) ↦₆₄ cap_c) ∗
        ((fsp + 112#64) ↦₆₄ ptr_c) ∗
        ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        memRegion (ptr_polys + BitVec.ofNat 64 (24 * j)) (24 * (remLen + 1)) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 24#64) ↦₆₄ 16#64) ∗
          ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 80#64) ↦₆₄ cap_c) ∗
          ((fsp + 88#64) ↦₆₄ ptr_c) ∗
          ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((fsp + 104#64) ↦₆₄ cap_c) ∗
          ((fsp + 112#64) ↦₆₄ ptr_c) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_polys + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x24 = fsp ∧
        sm.readReg64 .x25 = 24#64 ∧
        sm.readReg64 .x26 = 1#64 ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 (j + 1) ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hj_lt : j < 16 := by omega
  have hne16 : (BitVec.ofNat 64 j != 16#64) = true := ofNat_ne_16 hj_lt
  have hbeq16 : (BitVec.ofNat 64 j == 16#64) = false := ofNat_beq_16_false hj_lt
  rw [memRegion_24_cons ptr_polys j remLen (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro d0
  apply SepWP.exists_left; intro d1
  apply SepWP.exists_left; intro d2
  have hslot := vecU8_slot_intro A (ptr_polys + BitVec.ofNat 64 (24 * j)) cap_c ptr_c bs
  have hent :
      (((fsp + 24#64) ↦₆₄ 16#64) ∗
        ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 80#64) ↦₆₄ cap_c) ∗
        ((fsp + 88#64) ↦₆₄ ptr_c) ∗
        ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((fsp + 104#64) ↦₆₄ cap_c) ∗
        ((fsp + 112#64) ↦₆₄ ptr_c) ∗
        ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        ((ptr_polys + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) ⊢
      (((fsp + 24#64) ↦₆₄ 16#64) ∗
        ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 80#64) ↦₆₄ cap_c) ∗
        ((fsp + 88#64) ↦₆₄ ptr_c) ∗
        ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((fsp + 104#64) ↦₆₄ cap_c) ∗
        ((fsp + 112#64) ↦₆₄ ptr_c) ∗
        ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8 A (ptr_polys + BitVec.ofNat 64 (24 * j)) bs ∗
        memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) := by
    refine Entails.trans (Entails.of_eq (Q :=
      ((((ptr_polys + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_polys + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs) ∗
        (((fsp + 24#64) ↦₆₄ 16#64) ∗
          ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 80#64) ↦₆₄ cap_c) ∗
          ((fsp + 88#64) ↦₆₄ ptr_c) ∗
          ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((fsp + 104#64) ↦₆₄ cap_c) ∗
          ((fsp + 112#64) ↦₆₄ ptr_c) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame))) (by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hslot) (Entails.of_eq (by ac_rfl))
  by_cases hdone : j + 1 = 16
  · have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = true := by simp [hdone]
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = false := by simp [hdone]
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)
  · have hj1_lt : j + 1 < 16 := by omega
    have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := ofNat_beq_16_false hj1_lt
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := ofNat_ne_16 hj1_lt
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)

/-- Finish one iteration of the `.points` outer loop (`+588 -> +408 -> +452 / +616`) in `[LibsignalPlacement]`. -/
theorem points_outer_finish_iter_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 : State) (fsp ptr_points : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j remLen : Nat) (htot : j + (remLen + 1) = 16)
    (bs : List (BitVec 8)) (cap_c ptr_c : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x19 + 8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 j)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = 1#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (if j + 1 = 16 then
        (blkPl_375).base + 616#64
       else
        (blkPl_375).base + 452#64)
      s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_points) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 56#64) ↦₆₄ cap_c) ∗
        ((fsp + 64#64) ↦₆₄ ptr_c) ∗
        ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        memRegion (ptr_points + BitVec.ofNat 64 (24 * j)) (24 * (remLen + 1)) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_points) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 56#64) ↦₆₄ cap_c) ∗
          ((fsp + 64#64) ↦₆₄ ptr_c) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_points + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = 1#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hj_lt : j < 16 := by omega
  have hne16 : (BitVec.ofNat 64 j != 16#64) = true := ofNat_ne_16 hj_lt
  have hbeq16 : (BitVec.ofNat 64 j == 16#64) = false := ofNat_beq_16_false hj_lt
  rw [memRegion_24_cons ptr_points j remLen (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro d0
  apply SepWP.exists_left; intro d1
  apply SepWP.exists_left; intro d2
  have hslot := vecU8_slot_intro A (ptr_points + BitVec.ofNat 64 (24 * j)) cap_c ptr_c bs
  have hent :
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_points) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 56#64) ↦₆₄ cap_c) ∗
        ((fsp + 64#64) ↦₆₄ ptr_c) ∗
        ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        ((ptr_points + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_points + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_points + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) ⊢
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_points) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 56#64) ↦₆₄ cap_c) ∗
        ((fsp + 64#64) ↦₆₄ ptr_c) ∗
        ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8 A (ptr_points + BitVec.ofNat 64 (24 * j)) bs ∗
        memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) := by
    refine Entails.trans (Entails.of_eq (Q :=
      ((((ptr_points + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_points + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_points + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs) ∗
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_points) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 56#64) ↦₆₄ cap_c) ∗
          ((fsp + 64#64) ↦₆₄ ptr_c) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame))) (by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hslot) (Entails.of_eq (by ac_rfl))
  by_cases hdone : j + 1 = 16
  · have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = true := by simp [hdone]
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = false := by simp [hdone]
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)
  · have hj1_lt : j + 1 < 16 := by omega
    have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := ofNat_beq_16_false hj1_lt
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := ofNat_ne_16 hj1_lt
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)

/-- Allocate and serialize one `Poly` element (`+188 -> +352`, or OOM panic via `+680`) in `[LibsignalPlacement]`. -/
theorem polys_outer_alloc_and_copy_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym)
      sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym)
      (rustAllocSpec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (cs : List GF16)
    (v104 v112 v120 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 188#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x19 + 8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 j)
    (hx24 : s.readReg64 .x24 = fsp)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = 1#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (cap_c ptr_c : BitVec 64),
      sm.pc = (blkPl_375).base + 352#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 128#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 →
      sm.readReg64 .x23 = BitVec.ofNat 64 j →
      sm.readReg64 .x28 = BitVec.ofNat 64 j →
      sm.readReg64 .x24 = fsp →
      sm.readReg64 .x25 = 24#64 →
      sm.readReg64 .x26 = 1#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
          ((fsp + 104#64) ↦₆₄ cap_c) ∗
          ((fsp + 112#64) ↦₆₄ ptr_c) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (serializeGF16List cs).length) ∗
          vecU8Buf A cap_c ptr_c (serializeGF16List cs) ∗
          vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 104#64) ↦₆₄ v104) ∗
        ((fsp + 112#64) ↦₆₄ v112) ∗
        ((fsp + 120#64) ↦₆₄ v120) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre
    (sepConj_mono_left (vecGF16Of_expose A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_cs
  apply SepWPp.exists_elim; intro ptr_cs
  apply SepWPp.pure_elim; rintro ⟨hmax, hptr_cs⟩
  cases cs with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, serializeGF16List_nil, BitVec.ofNat_eq_ofNat] at hmax hnext
    conv => arg 4; simp only [List.length_nil, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
    refine SepWPp.seq_clean (mid := (blkPl_375).base + 352#64)
      (P_mid :=
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
          ((fsp + 104#64) ↦₆₄ 0#64) ∗
          ((fsp + 112#64) ↦₆₄ 1#64) ∗
          ((fsp + 120#64) ↦₆₄ 0#64) ∗
          vecU8Buf A 0#64 1#64 [] ∗
          vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) [] ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x24 = fsp ∧
        sm.readReg64 .x25 = 24#64 ∧
        sm.readReg64 .x26 = 1#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      have hfold_gf := vecGF16Of_intro A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cap_cs ptr_cs []
      simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hfold_gf
      have hbuf := vecU8Buf_nil_intro A
        (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) [] ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
          ((fsp + 104#64) ↦₆₄ 0#64) ∗
          ((fsp + 112#64) ↦₆₄ 1#64) ∗
          ((fsp + 120#64) ↦₆₄ 0#64) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      have hent :
          ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
            arrayAt gf16At 2 ptr_cs [] ∗
            vecGF16Tail A cap_cs ptr_cs 0 ∗
            ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
            ((fsp + 104#64) ↦₆₄ 0#64) ∗
            ((fsp + 112#64) ↦₆₄ 1#64) ∗
            ((fsp + 120#64) ↦₆₄ 0#64) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
          (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
            ((fsp + 104#64) ↦₆₄ 0#64) ∗
            ((fsp + 112#64) ↦₆₄ 1#64) ∗
            ((fsp + 120#64) ↦₆₄ 0#64) ∗
            vecU8Buf A 0#64 1#64 [] ∗
            vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) [] ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
        refine Entails.trans (Entails.of_eq (Q :=
          (((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
            arrayAt gf16At 2 ptr_cs [] ∗
            vecGF16Tail A cap_cs ptr_cs 0) ∗
            (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
              ((fsp + 104#64) ↦₆₄ 0#64) ∗
              ((fsp + 112#64) ↦₆₄ 1#64) ∗
              ((fsp + 120#64) ↦₆₄ 0#64) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) (by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hfold_gf) (Entails.trans hbuf (Entails.of_eq (by ac_rfl)))
      exact SepWP.weaken_pre hent (by wp_done)
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx28m, hx24m, hx25m, hx26m, htrm, hvregsm⟩
      exact hnext sm 0#64 1#64 hpcm hrunm hspm hx29m hx19m hx20m hx22m hx23m hx28m hx24m hx25m hx26m htrm hvregsm
  | cons g cs' =>
    have hcs_pos : 0 < (g :: cs').length := by simp
    have hbeq0 : (BitVec.ofNat 64 (g :: cs').length == 0#64) = false :=
      ofNat_beq_zero_false hcs_pos (by omega)
    have hlsl : (BitVec.ofNat 64 (g :: cs').length) <<< 1 = BitVec.ofNat 64 (2 * (g :: cs').length) :=
      shiftLeft_one_eq_mul_two hmax
    have htoNat_len : (BitVec.ofNat 64 (2 * (g :: cs').length)).toNat = 2 * (g :: cs').length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk (2 * (g :: cs').length) 1 := ⟨by omega, hpow2, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_375).base + 224#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      refine sepWPp_pure_mid fun htr_oom => ?_
      refine SepWPp.seq_clean (mid := (blkPl_375).base + 680#64)
        (P_mid :=
          A.pool ∗
          stackAt sf.sp allocHookStack ∗
          (((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
          ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
          ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
          arrayAt gf16At 2 ptr_cs (g :: cs') ∗
          vecGF16Tail A cap_cs ptr_cs (g :: cs').length ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
          ((fsp + 104#64) ↦₆₄ v104) ∗ ((fsp + 112#64) ↦₆₄ v112) ∗ ((fsp + 120#64) ↦₆₄ v120) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro sm hpcm hrunm htrm
        exact into_pb_panic_680_placed h_panic s0 sm _ R hpcm hrunm htrm
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom64
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.seq_clean (mid := (blkPl_375).base + 240#64)
        (P_mid :=
          arrayAt gf16At 2 ptr_cs (g :: cs') ∗
            memRegion (ptr_c + BitVec.ofNat 64 (2 * 0)) (2 * (g :: cs').length) ∗
            ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
            ((fsp + 120#64) ↦₆₄ 0#64) ∗
            ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
            ((fsp + 112#64) ↦₆₄ ptr_c) ∗
            (((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
            vecGF16Tail A cap_cs ptr_cs (g :: cs').length ∗
            A.live ptr_c (2 * (g :: cs').length) 1 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q_mid := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x29 = fsp + 128#64 ∧
          sm.readReg64 .x0 = ptr_c ∧
          sm.readReg64 .x1 = BitVec.ofNat 64 (2 * 0) ∧
          sm.readReg64 .x27 = BitVec.ofNat 64 (g :: cs').length ∧
          sm.readReg64 .x28 = ptr_cs ∧
          sm.readReg64 .x19 = s0.readReg64 .x19 ∧
          sm.readReg64 .x20 = s0.readReg64 .x20 ∧
          sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 j ∧
          sm.readReg64 .x24 = fsp ∧
          sm.readReg64 .x25 = 24#64 ∧
          sm.readReg64 .x26 = 1#64 ∧
          sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        ?_ ?_
      · wp_steps
        have hz : ptr_c + BitVec.ofNat 64 (2 * 0) = ptr_c := by simp
        rw [hz]
        wp_done
      · intro s_in hpc_in hrun_in ⟨hsp_in, hx29_in, hx0_in, hx1_in, hx27_in, hx28_in,
          hx19_in, hx20_in, hx22_in, hx23_in, hx24_in, hx25_in, hx26_in, htr_in, hvregs_in⟩
        have hloop := polys_inner_loop_placed (ext := ext) s_in fsp ptr_c
          (g :: cs').length hmax (g :: cs') (List.cons_ne_nil g cs') 0 (by omega)
          s_in ptr_cs 0#64
          (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
            ((fsp + 112#64) ↦₆₄ ptr_c) ∗
            (((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
            vecGF16Tail A cap_cs ptr_cs (g :: cs').length ∗
            A.live ptr_c (2 * (g :: cs').length) 1 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc_in hrun_in hsp_in hx29_in hx0_in hx1_in hx27_in hx28_in
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
        refine SepWPp.seq_clean hloop ?_
        intro s_out hpc_out hrun_out ⟨hsp_out, hx29_out, hx19_out, hx20_out,
          hx22_out, hx23_out, hx24_out, hx25_out, hx26_out, htr_out, hvregs_out⟩
        rw [hx19_in] at hx19_out
        rw [hx20_in] at hx20_out
        rw [hx22_in] at hx22_out
        rw [hx23_in] at hx23_out
        rw [hx24_in] at hx24_out
        rw [hx25_in] at hx25_out
        rw [hx26_in] at hx26_out
        rw [htr_in] at htr_out
        rw [hvregs_in] at hvregs_out
        refine SepWPp.seq_clean (mid := (blkPl_375).base + 352#64)
          (P_mid :=
            ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
              ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
              ((fsp + 112#64) ↦₆₄ ptr_c) ∗
              ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (serializeGF16List (g :: cs')).length) ∗
              vecU8Buf A (BitVec.ofNat 64 (2 * (g :: cs').length)) ptr_c (serializeGF16List (g :: cs')) ∗
              vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) (g :: cs') ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (Q_mid := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 128#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
            sm.readReg64 .x23 = BitVec.ofNat 64 j ∧
            sm.readReg64 .x28 = BitVec.ofNat 64 j ∧
            sm.readReg64 .x24 = fsp ∧
            sm.readReg64 .x25 = 24#64 ∧
            sm.readReg64 .x26 = 1#64 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · wp_steps
          have hz : ptr_c + BitVec.ofNat 64 (2 * 0) = ptr_c := by simp
          rw [hz]
          have hser_len : (serializeGF16List (g :: cs')).length = 2 * (g :: cs').length :=
            length_serializeGF16List (g :: cs')
          have hbuf := vecU8Buf_of_exact_alloc A ptr_c (serializeGF16List (g :: cs'))
            (by rw [hser_len]; omega) (by rw [hser_len]; omega) hoom
          rw [hser_len] at hbuf ⊢
          have hfold_gf := vecGF16Of_intro A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cap_cs ptr_cs (g :: cs')
          have hent :
              (arrayAt gf16At 2 ptr_cs (g :: cs') ∗
                (ptr_c ↦ₛ serializeGF16List (g :: cs')) ∗
                ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
                ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
                ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
                ((fsp + 112#64) ↦₆₄ ptr_c) ∗
                (((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
                ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
                ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
                vecGF16Tail A cap_cs ptr_cs (g :: cs').length ∗
                A.live ptr_c (2 * (g :: cs').length) 1 ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
              (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
                ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
                ((fsp + 112#64) ↦₆₄ ptr_c) ∗
                ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
                vecU8Buf A (BitVec.ofNat 64 (2 * (g :: cs').length)) ptr_c (serializeGF16List (g :: cs')) ∗
                vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) (g :: cs') ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
            refine Entails.trans (Entails.of_eq (Q :=
              (((ptr_c ↦ₛ serializeGF16List (g :: cs')) ∗
                A.live ptr_c (2 * (g :: cs').length) 1) ∗
                (((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
                  ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
                  ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
                  arrayAt gf16At 2 ptr_cs (g :: cs') ∗
                  vecGF16Tail A cap_cs ptr_cs (g :: cs').length) ∗
                  (((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
                    ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
                    ((fsp + 112#64) ↦₆₄ ptr_c) ∗
                    ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
                    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))) (by ac_rfl)) ?_
            exact Entails.trans (sepConj_mono hbuf (sepConj_mono_left hfold_gf)) (Entails.of_eq (by ac_rfl))
          exact SepWP.weaken_pre hent (by wp_done)
        · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx28m, hx24m, hx25m, hx26m, htrm, hvregsm⟩
          exact hnext sm (BitVec.ofNat 64 (2 * (g :: cs').length)) ptr_c
            hpcm hrunm hspm hx29m hx19m hx20m hx22m hx23m hx28m hx24m hx25m hx26m htrm hvregsm

/-- Full `.polys` outer loop (`+188 -> +616`, or OOM panic) in `[LibsignalPlacement]`. -/
theorem polys_outer_loop_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym)
      sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym)
      (rustAllocSpec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptr_polys : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List GF16)) (hne : rem ≠ [])
    (j : Nat) (htot : j + rem.length = 16)
    (v80 v88 v96 v104 v112 v120 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 188#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x19 + 8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 j)
    (hx24 : s.readReg64 .x24 = fsp)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = 1#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (w80 w88 w96 w104 w112 w120 : BitVec 64),
      sm.pc = (blkPl_375).base + 616#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 128#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 24#64) ↦₆₄ 16#64) ∗
          ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 40#64) ↦₆₄ 16#64) ∗
          ((fsp + 80#64) ↦₆₄ w80) ∗
          ((fsp + 88#64) ↦₆₄ w88) ∗
          ((fsp + 96#64) ↦₆₄ w96) ∗
          ((fsp + 104#64) ↦₆₄ w104) ∗
          ((fsp + 112#64) ↦₆₄ w112) ∗
          ((fsp + 120#64) ↦₆₄ w120) ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) rem ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptr_polys + BitVec.ofNat 64 (24 * j)) (rem.map serializeGF16List) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (((fsp + 24#64) ↦₆₄ 16#64) ∗
        ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 80#64) ↦₆₄ v80) ∗
        ((fsp + 88#64) ↦₆₄ v88) ∗
        ((fsp + 96#64) ↦₆₄ v96) ∗
        ((fsp + 104#64) ↦₆₄ v104) ∗
        ((fsp + 112#64) ↦₆₄ v112) ∗
        ((fsp + 120#64) ↦₆₄ v120) ∗
        arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) rem ∗
        memRegion (ptr_polys + BitVec.ofNat 64 (24 * j)) (24 * rem.length) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  induction rem generalizing j v80 v88 v96 v104 v112 v120 s Frame with
  | nil => exact (hne rfl).elim
  | cons cs rem' ih =>
    have htot' : j + (rem'.length + 1) = 16 := by
      simpa [List.length_cons] using htot
    rw [arrayAt_24_off_cons]
    conv => arg 4; rw [List.length_cons]
    refine SepWPp.weaken_pre (P' :=
      vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 104#64) ↦₆₄ v104) ∗
        ((fsp + 112#64) ↦₆₄ v112) ∗
        ((fsp + 120#64) ↦₆₄ v120) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 24#64) ↦₆₄ 16#64) ∗
          ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 80#64) ↦₆₄ v80) ∗
          ((fsp + 88#64) ↦₆₄ v88) ∗
          ((fsp + 96#64) ↦₆₄ v96) ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          memRegion (ptr_polys + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
          Frame))
      (Entails.of_eq (by ac_rfl)) ?_
    refine polys_outer_alloc_and_copy_placed hshim halloc h_panic s0 fsp hfsp_align j cs v104 v112 v120 s _
      hpc hrun hsp hx29 hx19 hx20 hx22 hx23 hx28 hx24 hx25 hx26 htrace hvregs ?_
    intro sm1 cap_c ptr_c hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx28_1 hx24_1 hx25_1 hx26_1 htr1 hvregs1
    refine SepWPp.weaken_pre (P' :=
      ((fsp + 24#64) ↦₆₄ 16#64) ∗
        ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 80#64) ↦₆₄ v80) ∗
        ((fsp + 88#64) ↦₆₄ v88) ∗
        ((fsp + 96#64) ↦₆₄ v96) ∗
        ((fsp + 104#64) ↦₆₄ cap_c) ∗
        ((fsp + 112#64) ↦₆₄ ptr_c) ∗
        ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (serializeGF16List cs).length) ∗
        vecU8Buf A cap_c ptr_c (serializeGF16List cs) ∗
        memRegion (ptr_polys + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
        (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (Entails.of_eq (by ac_rfl)) ?_
    have hfin := polys_outer_finish_iter_placed (A := A) (ext := ext)
      s0 fsp ptr_polys hfsp_align j rem'.length htot'
      (serializeGF16List cs) cap_c ptr_c v80 v88 v96 sm1
      (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
        arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1 hvregs1
    refine SepWPp.seq_clean hfin ?_
    intro sm2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2, hvregs2⟩
    cases rem' with
    | nil =>
      have hj1 : j + 1 = 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      have h16 : BitVec.ofNat 64 (j + 1) = 16#64 := by rw [hj1]
      refine SepWPp.weaken_pre ?_ (hnext sm2 cap_c ptr_c (BitVec.ofNat 64 (serializeGF16List cs).length)
        cap_c ptr_c (BitVec.ofNat 64 (serializeGF16List cs).length)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 htr2 hvregs2)
      simp only [List.length_nil, List.map_cons, List.map_nil, arrayAt_nil, arrayAt_24_off_singleton,
        Nat.mul_zero, memRegion_zero, sepConj_emp, h16]
      exact Entails.of_eq (by ac_rfl)
    | cons cs2 rem'' =>
      have hj1 : j + 1 ≠ 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      refine SepWPp.weaken_pre (P' :=
        ((fsp + 24#64) ↦₆₄ 16#64) ∗
          ((fsp + 32#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 80#64) ↦₆₄ cap_c) ∗
          ((fsp + 88#64) ↦₆₄ ptr_c) ∗
          ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 (serializeGF16List cs).length) ∗
          ((fsp + 104#64) ↦₆₄ cap_c) ∗
          ((fsp + 112#64) ↦₆₄ ptr_c) ∗
          ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 (serializeGF16List cs).length) ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * (j + 1))) (cs2 :: rem'') ∗
          memRegion (ptr_polys + BitVec.ofNat 64 (24 * (j + 1))) (24 * (cs2 :: rem'').length) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
            vecU8 A (ptr_polys + BitVec.ofNat 64 (24 * j)) (serializeGF16List cs) ∗
            Frame))
        (Entails.of_eq (by ac_rfl)) ?_
      refine ih (List.cons_ne_nil cs2 rem'') (j + 1) (by simp at htot' ⊢; omega)
        cap_c ptr_c (BitVec.ofNat 64 (serializeGF16List cs).length)
        cap_c ptr_c (BitVec.ofNat 64 (serializeGF16List cs).length)
        sm2
        (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
          vecU8 A (ptr_polys + BitVec.ofNat 64 (24 * j)) (serializeGF16List cs) ∗
          Frame)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx22_2 hx23_2 hx28_2 hx24_2 hx25_2 hx26_2 htr2 hvregs2 ?_
      intro sm3 w80 w88 w96 w104 w112 w120 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3
      refine SepWPp.weaken_pre ?_
        (hnext sm3 w80 w88 w96 w104 w112 w120 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3)
      simp only [List.map_cons, arrayAt_24_off_cons]
      exact Entails.of_eq (by ac_rfl)

/-- Allocate and serialize one `Poly` element in `.points` branch (`+452 -> +588`, or OOM panic via `+680`) in `[LibsignalPlacement]`. -/
theorem points_outer_alloc_and_copy_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym)
      sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym)
      (rustAllocSpec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (cs : List GF16)
    (v56 v64 v72 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 452#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x19 + 8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 j)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = 1#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (cap_c ptr_c : BitVec 64),
      sm.pc = (blkPl_375).base + 588#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 128#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 →
      sm.readReg64 .x23 = BitVec.ofNat 64 j →
      sm.readReg64 .x24 = 24#64 →
      sm.readReg64 .x25 = 1#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 56#64) ↦₆₄ cap_c) ∗
          ((fsp + 64#64) ↦₆₄ ptr_c) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (serializeGF16List cs).length) ∗
          vecU8Buf A cap_c ptr_c (serializeGF16List cs) ∗
          vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        ((fsp + 72#64) ↦₆₄ v72) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre
    (sepConj_mono_left (vecGF16Of_expose A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap_cs
  apply SepWPp.exists_elim; intro ptr_cs
  apply SepWPp.pure_elim; rintro ⟨hmax, hptr_cs⟩
  cases cs with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, serializeGF16List_nil, BitVec.ofNat_eq_ofNat] at hmax hnext
    conv => arg 4; simp only [List.length_nil, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
    refine SepWPp.seq_clean (mid := (blkPl_375).base + 588#64)
      (P_mid :=
        ((fsp + 56#64) ↦₆₄ 0#64) ∗
          ((fsp + 64#64) ↦₆₄ 1#64) ∗
          ((fsp + 72#64) ↦₆₄ 0#64) ∗
          vecU8Buf A 0#64 1#64 [] ∗
          vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) [] ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q_mid := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 j ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = 1#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      have hfold_gf := vecGF16Of_intro A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cap_cs ptr_cs []
      simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hfold_gf
      have hbuf := vecU8Buf_nil_intro A
        (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) [] ∗
          ((fsp + 56#64) ↦₆₄ 0#64) ∗
          ((fsp + 64#64) ↦₆₄ 1#64) ∗
          ((fsp + 72#64) ↦₆₄ 0#64) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      have hent :
          ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
            arrayAt gf16At 2 ptr_cs [] ∗
            vecGF16Tail A cap_cs ptr_cs 0 ∗
            ((fsp + 56#64) ↦₆₄ 0#64) ∗
            ((fsp + 64#64) ↦₆₄ 1#64) ∗
            ((fsp + 72#64) ↦₆₄ 0#64) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ⊢
          (((fsp + 56#64) ↦₆₄ 0#64) ∗
            ((fsp + 64#64) ↦₆₄ 1#64) ∗
            ((fsp + 72#64) ↦₆₄ 0#64) ∗
            vecU8Buf A 0#64 1#64 [] ∗
            vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) [] ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) := by
        refine Entails.trans (Entails.of_eq (Q :=
          (((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
            arrayAt gf16At 2 ptr_cs [] ∗
            vecGF16Tail A cap_cs ptr_cs 0) ∗
            (((fsp + 56#64) ↦₆₄ 0#64) ∗
              ((fsp + 64#64) ↦₆₄ 1#64) ∗
              ((fsp + 72#64) ↦₆₄ 0#64) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) (by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hfold_gf) (Entails.trans hbuf (Entails.of_eq (by ac_rfl)))
      exact SepWP.weaken_pre hent (by wp_done)
    · intro sm hpcm hrunm ⟨hspm, hx29m, hx19m, hx20m, hx22m, hx23m, hx24m, hx25m, htrm, hvregsm⟩
      exact hnext sm 0#64 1#64 hpcm hrunm hspm hx29m hx19m hx20m hx22m hx23m hx24m hx25m htrm hvregsm
  | cons g cs' =>
    have hcs_pos : 0 < (g :: cs').length := by simp
    have hbeq0 : (BitVec.ofNat 64 (g :: cs').length == 0#64) = false :=
      ofNat_beq_zero_false hcs_pos (by omega)
    have hlsl : (BitVec.ofNat 64 (g :: cs').length) <<< 1 = BitVec.ofNat 64 (2 * (g :: cs').length) :=
      shiftLeft_one_eq_mul_two hmax
    have htoNat_len : (BitVec.ofNat 64 (2 * (g :: cs').length)).toNat = 2 * (g :: cs').length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk (2 * (g :: cs').length) 1 := ⟨by omega, hpow2, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_375).base + 484#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      refine sepWPp_pure_mid fun htr_oom => ?_
      refine SepWPp.seq_clean (mid := (blkPl_375).base + 680#64)
        (P_mid :=
          A.pool ∗
          stackAt sf.sp allocHookStack ∗
          (((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
          ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
          ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
          arrayAt gf16At 2 ptr_cs (g :: cs') ∗
          vecGF16Tail A cap_cs ptr_cs (g :: cs').length ∗
          ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 64#64) ↦₆₄ v64) ∗ ((fsp + 72#64) ↦₆₄ v72) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        ?_ ?_
      · wp_steps
        wp_done
      · intro sm hpcm hrunm htrm
        exact into_pb_panic_680_placed h_panic s0 sm _ R hpcm hrunm htrm
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom64
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine SepWPp.seq_clean (mid := (blkPl_375).base + 504#64)
        (P_mid :=
          arrayAt gf16At 2 ptr_cs (g :: cs') ∗
            memRegion (ptr_c + BitVec.ofNat 64 (2 * 0)) (2 * (g :: cs').length) ∗
            ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
            ((fsp + 72#64) ↦₆₄ 0#64) ∗
            ((fsp + 64#64) ↦₆₄ ptr_c) ∗
            (((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
            vecGF16Tail A cap_cs ptr_cs (g :: cs').length ∗
            A.live ptr_c (2 * (g :: cs').length) 1 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q_mid := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x29 = fsp + 128#64 ∧
          sm.readReg64 .x0 = ptr_c ∧
          sm.readReg64 .x1 = BitVec.ofNat 64 (2 * 0) ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 (g :: cs').length ∧
          sm.readReg64 .x21 = ptr_cs ∧
          sm.readReg64 .x19 = s0.readReg64 .x19 ∧
          sm.readReg64 .x20 = s0.readReg64 .x20 ∧
          sm.readReg64 .x22 = s0.readReg64 .x19 + 8#64 ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 j ∧
          sm.readReg64 .x24 = 24#64 ∧
          sm.readReg64 .x25 = 1#64 ∧
          sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        ?_ ?_
      · wp_steps
        have hz : ptr_c + BitVec.ofNat 64 (2 * 0) = ptr_c := by simp
        rw [hz]
        wp_done
      · intro s_in hpc_in hrun_in ⟨hsp_in, hx29_in, hx0_in, hx1_in, hx26_in, hx21_in,
          hx19_in, hx20_in, hx22_in, hx23_in, hx24_in, hx25_in, htr_in, hvregs_in⟩
        have hloop := points_inner_loop_placed (ext := ext) s_in fsp ptr_c hfsp_align
          (g :: cs').length hmax (g :: cs') (List.cons_ne_nil g cs') 0 (by omega)
          s_in ptr_cs 0#64
          (((fsp + 64#64) ↦₆₄ ptr_c) ∗
            (((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
            ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
            vecGF16Tail A cap_cs ptr_cs (g :: cs').length ∗
            A.live ptr_c (2 * (g :: cs').length) 1 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hpc_in hrun_in hsp_in hx29_in hx0_in hx1_in hx26_in hx21_in
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
        refine SepWPp.seq_clean hloop ?_
        intro s_out hpc_out hrun_out ⟨hsp_out, hx29_out, hx19_out, hx20_out,
          hx22_out, hx23_out, hx24_out, hx25_out, _, htr_out, hvregs_out⟩
        rw [hx19_in] at hx19_out
        rw [hx20_in] at hx20_out
        rw [hx22_in] at hx22_out
        rw [hx23_in] at hx23_out
        rw [hx24_in] at hx24_out
        rw [hx25_in] at hx25_out
        rw [htr_in] at htr_out
        rw [hvregs_in] at hvregs_out
        have hz : ptr_c + BitVec.ofNat 64 (2 * 0) = ptr_c := by simp
        rw [hz]
        have hser_len : (serializeGF16List (g :: cs')).length = 2 * (g :: cs').length :=
          length_serializeGF16List (g :: cs')
        have hbuf := vecU8Buf_of_exact_alloc A ptr_c (serializeGF16List (g :: cs'))
          (by rw [hser_len]; omega) (by rw [hser_len]; omega) hoom
        rw [hser_len] at hbuf
        have hfold_gf := vecGF16Of_intro A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cap_cs ptr_cs (g :: cs')
        refine SepWPp.weaken_pre ?_
          (hnext s_out (BitVec.ofNat 64 (2 * (g :: cs').length)) ptr_c
            hpc_out hrun_out hsp_out hx29_out hx19_out hx20_out hx22_out hx23_out hx24_out hx25_out htr_out hvregs_out)
        rw [hser_len]
        refine Entails.trans (Entails.of_eq (Q :=
          (((ptr_c ↦ₛ serializeGF16List (g :: cs')) ∗
            A.live ptr_c (2 * (g :: cs').length) 1) ∗
            (((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_cs) ∗
              ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_cs) ∗
              ((((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 (g :: cs').length) ∗
              arrayAt gf16At 2 ptr_cs (g :: cs') ∗
              vecGF16Tail A cap_cs ptr_cs (g :: cs').length) ∗
              (((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
                ((fsp + 64#64) ↦₆₄ ptr_c) ∗
                ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (2 * (g :: cs').length)) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame)))) (by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hbuf (sepConj_mono_left hfold_gf)) (Entails.of_eq (by ac_rfl))

/-- Full `.points` outer loop (`+452 -> +616`, or OOM panic) in `[LibsignalPlacement]`. -/
theorem points_outer_loop_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym)
      sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym)
      (rustAllocSpec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp ptr_points : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (rem : List (List GF16)) (hne : rem ≠ [])
    (j : Nat) (htot : j + rem.length = 16)
    (v56 v64 v72 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 452#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x19 + 8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 j)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = 1#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (sm : State) (w56 w64 w72 : BitVec 64),
      sm.pc = (blkPl_375).base + 616#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 128#64 →
      sm.readReg64 .x19 = s0.readReg64 .x19 →
      sm.readReg64 .x20 = s0.readReg64 .x20 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_points) ∗
          ((fsp + 16#64) ↦₆₄ 16#64) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗
          ((fsp + 64#64) ↦₆₄ w64) ∗
          ((fsp + 72#64) ↦₆₄ w72) ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) rem ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (ptr_points + BitVec.ofNat 64 (24 * j)) (rem.map serializeGF16List) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_points) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        ((fsp + 72#64) ↦₆₄ v72) ∗
        arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) rem ∗
        memRegion (ptr_points + BitVec.ofNat 64 (24 * j)) (24 * rem.length) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  induction rem generalizing j v56 v64 v72 s Frame with
  | nil => exact (hne rfl).elim
  | cons cs rem' ih =>
    have htot' : j + (rem'.length + 1) = 16 := by
      simpa [List.length_cons] using htot
    rw [arrayAt_24_off_cons]
    conv => arg 4; rw [List.length_cons]
    refine SepWPp.weaken_pre (P' :=
      vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
        ((fsp + 56#64) ↦₆₄ v56) ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        ((fsp + 72#64) ↦₆₄ v72) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_points) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          memRegion (ptr_points + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
          Frame))
      (Entails.of_eq (by ac_rfl)) ?_
    refine points_outer_alloc_and_copy_placed hshim halloc h_panic s0 fsp hfsp_align j cs v56 v64 v72 s _
      hpc hrun hsp hx29 hx19 hx20 hx22 hx23 hx24 hx25 htrace hvregs ?_
    intro sm1 cap_c ptr_c hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 htr1 hvregs1
    refine SepWPp.weaken_pre (P' :=
      (fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_points) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 56#64) ↦₆₄ cap_c) ∗
        ((fsp + 64#64) ↦₆₄ ptr_c) ∗
        ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (serializeGF16List cs).length) ∗
        vecU8Buf A cap_c ptr_c (serializeGF16List cs) ∗
        memRegion (ptr_points + BitVec.ofNat 64 (24 * j)) (24 * (rem'.length + 1)) ∗
        (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame))
      (Entails.of_eq (by ac_rfl)) ?_
    have hfin := points_outer_finish_iter_placed (A := A) (ext := ext)
      s0 fsp ptr_points hfsp_align j rem'.length htot'
      (serializeGF16List cs) cap_c ptr_c sm1
      (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
        arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * (j + 1))) rem' ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 htr1 hvregs1
    refine SepWPp.seq_clean hfin ?_
    intro sm2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, htr2, hvregs2⟩
    cases rem' with
    | nil =>
      have hj1 : j + 1 = 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      have h16 : BitVec.ofNat 64 (j + 1) = 16#64 := by rw [hj1]
      refine SepWPp.weaken_pre ?_ (hnext sm2 cap_c ptr_c (BitVec.ofNat 64 (serializeGF16List cs).length)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 htr2 hvregs2)
      simp only [List.length_nil, List.map_cons, List.map_nil, arrayAt_nil, arrayAt_24_off_singleton,
        Nat.mul_zero, memRegion_zero, sepConj_emp, h16]
      exact Entails.of_eq (by ac_rfl)
    | cons cs2 rem'' =>
      have hj1 : j + 1 ≠ 16 := by simp at htot'; omega
      simp only [hj1, ↓reduceIte] at hpc2
      refine SepWPp.weaken_pre (P' :=
        (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_points) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 56#64) ↦₆₄ cap_c) ∗
          ((fsp + 64#64) ↦₆₄ ptr_c) ∗
          ((fsp + 72#64) ↦₆₄ BitVec.ofNat 64 (serializeGF16List cs).length) ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * (j + 1))) (cs2 :: rem'') ∗
          memRegion (ptr_points + BitVec.ofNat 64 (24 * (j + 1))) (24 * (cs2 :: rem'').length) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
            vecU8 A (ptr_points + BitVec.ofNat 64 (24 * j)) (serializeGF16List cs) ∗
            Frame))
        (Entails.of_eq (by ac_rfl)) ?_
      refine ih (List.cons_ne_nil cs2 rem'') (j + 1) (by simp at htot' ⊢; omega)
        cap_c ptr_c (BitVec.ofNat 64 (serializeGF16List cs).length)
        sm2
        (vecGF16Of A ((s0.readReg64 .x19 + 8#64) + BitVec.ofNat 64 (24 * j)) cs ∗
          vecU8 A (ptr_points + BitVec.ofNat 64 (24 * j)) (serializeGF16List cs) ∗
          Frame)
        hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 htr2 hvregs2 ?_
      intro sm3 w56 w64 w72 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3
      refine SepWPp.weaken_pre ?_
        (hnext sm3 w56 w64 w72 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3)
      simp only [List.map_cons, arrayAt_24_off_cons]
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.EncoderIntoPb
