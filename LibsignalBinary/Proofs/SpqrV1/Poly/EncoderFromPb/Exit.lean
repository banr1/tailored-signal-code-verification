/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPoly
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: Epilogue and Exit Blocks

**Checked by Lean.**

Proves `protoPolynomialEncoderAt` open/close bridges, the shared `drop_glue::<ProtoPolynomialEncoder>`
tail-call epilogue (`+1460`), error exits (`+1448`, `+1496`, `+1612`), and shared success header copy
(`+1572 → s0.lr`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit

@[local arm64_norm, local wp_norm] theorem bv384_toNat : (384#64 : BitVec 64).toNat = 384 := rfl
@[local arm64_norm, local wp_norm] theorem bv8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl

/-! ## Address Normalization and Stack / Memory Splitting Lemmas -/

@[local arm64_norm, local wp_norm] theorem sp_sub_1024_add_928 (sp : BitVec 64) :
    (sp - 1024#64) + 928#64 = sp - 96#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_16 (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_32 (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_48 (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_64 (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_80 (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_96_add_96 (sp : BitVec 64) : (sp - 96#64) + 96#64 = sp := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_88_add_8 (sp : BitVec 64) : (sp - 88#64) + 8#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_8 (sp : BitVec 64) : (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_72_add_8 (sp : BitVec 64) : (sp - 72#64) + 8#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_64_add_8 (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_56_add_8 (sp : BitVec 64) : (sp - 56#64) + 8#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_48_add_8 (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_40_add_8 (sp : BitVec 64) : (sp - 40#64) + 8#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_32_add_8 (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_24_add_8 (sp : BitVec 64) : (sp - 24#64) + 8#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_16_add_8 (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega

/-- The 12 saved register cells at `s0.sp - 96#64 .. s0.sp - 8#64`. -/
def savedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem stackAt_encoderFromPb_split_96 (sp : BitVec 64) :
    stackAt sp encoderFromPbStack =
      stackAt (sp - 96#64) (dropGluePoly16Stack + 928) ∗ cells (sp - 96#64) 12 := by
  have hEq : encoderFromPbStack = (dropGluePoly16Stack + 928) + 8 * 12 := rfl
  rw [hEq]
  exact ProofLib.stackAt_split_cells sp (dropGluePoly16Stack + 928) 12 (by decide)

theorem stackAt_96_split_928 (sp : BitVec 64) :
    stackAt (sp - 96#64) (dropGluePoly16Stack + 928) =
      stackAt (sp - 1024#64) dropGluePoly16Stack ∗ memRegion (sp - 1024#64) 928 := by
  simp only [stackAt]
  rw [memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (dropGluePoly16Stack + 928))
    dropGluePoly16Stack 928 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (dropGluePoly16Stack + 928) =
      (sp - 1024#64) - BitVec.ofNat 64 dropGluePoly16Stack := by
    change (sp - 96#64) - 5056#64 = (sp - 1024#64) - 4128#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (dropGluePoly16Stack + 928) +
      BitVec.ofNat 64 dropGluePoly16Stack = sp - 1024#64 := by
    change (sp - 96#64) - 5056#64 + 4128#64 = sp - 1024#64
    bv_omega
  rw [h2, h1]

theorem stackAt_dropGluePoly16_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropGluePoly16Stack =
      memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 32 (by decide)

theorem stackAt_encoderFromPb_split_dropStack48 (sp : BitVec 64) :
    stackAt sp encoderFromPbStack =
      memRegion (sp - 5152#64) 1008 ∗ stackAt sp dropStack48 :=
  stackAt_split_bottom sp dropStack48 1008 (by decide)

theorem savedCells_entails_cells12 (s0 : State) :
    savedCells s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold savedCells
  refine cells_sub_succ_entails 96 12 ?_
  refine cells_sub_succ_entails 88 11 ?_
  refine cells_sub_succ_entails 80 10 ?_
  refine cells_sub_succ_entails 72 9 ?_
  refine cells_sub_succ_entails 64 8 ?_
  refine cells_sub_succ_entails 56 7 ?_
  refine cells_sub_succ_entails 48 6 ?_
  refine cells_sub_succ_entails 40 5 ?_
  refine cells_sub_succ_entails 32 4 ?_
  refine cells_sub_succ_entails 24 3 ?_
  refine cells_sub_succ_entails 16 2 ?_
  rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide), cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _)

theorem savedCells_restore_stack (s0 : State) (R : SepProp) :
    savedCells s0 ∗ stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗ R ⊢
      R ∗ stackAt s0.sp encoderFromPbStack := by
  rw [stackAt_encoderFromPb_split_96 s0.sp]
  refine Entails.trans (sepConj_mono_left (savedCells_entails_cells12 s0)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_928_split (fsp : BitVec 64) :
    memRegion fsp 928 =
      cells fsp 9 ∗
      memRegion (fsp + 72#64) 384 ∗
      cells (fsp + 456#64) 3 ∗
      memRegion (fsp + 480#64) 384 ∗
      cells (fsp + 864#64) 4 ∗
      cells (fsp + 896#64) 3 ∗
      memRegion (fsp + 920#64) 8 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 72) (k := 856)
        (b' := fsp + 72#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 72#64) (n := 384) (k := 472)
        (b' := fsp + 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 456#64) (n := 24) (k := 448)
        (b' := fsp + 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 480#64) (n := 384) (k := 64)
        (b' := fsp + 864#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 864#64) (n := 32) (k := 32)
        (b' := fsp + 896#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 896#64) (n := 24) (k := 8)
        (b' := fsp + 920#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells fsp 9 (by decide),
      ProofLib.memRegion_cells (fsp + 456#64) 3 (by decide),
      ProofLib.memRegion_cells (fsp + 864#64) 4 (by decide),
      ProofLib.memRegion_cells (fsp + 896#64) 3 (by decide)]

theorem frame_928_rejoin (sp : BitVec 64) :
    cells (sp - 1024#64) 9 ∗
    memRegion ((sp - 1024#64) + 72#64) 384 ∗
    cells ((sp - 1024#64) + 456#64) 3 ∗
    memRegion ((sp - 1024#64) + 480#64) 384 ∗
    cells ((sp - 1024#64) + 864#64) 4 ∗
    cells ((sp - 1024#64) + 896#64) 3 ∗
    memRegion ((sp - 1024#64) + 920#64) 8 ∗
    memRegion ((sp - 1024#64) - 4128#64) 32 ∗
    stackAt (sp - 1024#64) allocHookStack ⊢
      stackAt (sp - 96#64) (dropGluePoly16Stack + 928) := by
  rw [stackAt_96_split_928 sp, stackAt_dropGluePoly16_split_bottom (sp - 1024#64),
      memRegion_928_split (sp - 1024#64)]
  exact Entails.of_eq (by ac_rfl)

theorem frame_928_rejoin_dropGlue (sp : BitVec 64) :
    cells (sp - 1024#64) 9 ∗
    memRegion ((sp - 1024#64) + 72#64) 384 ∗
    cells ((sp - 1024#64) + 456#64) 3 ∗
    memRegion ((sp - 1024#64) + 480#64) 384 ∗
    cells ((sp - 1024#64) + 864#64) 4 ∗
    cells ((sp - 1024#64) + 896#64) 3 ∗
    memRegion ((sp - 1024#64) + 920#64) 8 ∗
    stackAt (sp - 1024#64) dropGluePoly16Stack ⊢
      stackAt (sp - 96#64) (dropGluePoly16Stack + 928) := by
  rw [stackAt_96_split_928 sp, memRegion_928_split (sp - 1024#64)]
  exact Entails.of_eq (by ac_rfl)

theorem cells9_split_4_5 (fsp : BitVec 64) :
    cells fsp 9 = cells fsp 4 ∗ cells (fsp + 32#64) 5 := by
  rw [← ProofLib.memRegion_cells fsp 9 (by decide),
      ProofLib.memRegion_split' (b := fsp) (n := 32) (k := 40)
        (b' := fsp + 32#64) rfl rfl (by decide),
      ProofLib.memRegion_cells fsp 4 (by decide),
      ProofLib.memRegion_cells (fsp + 32#64) 5 (by decide)]

theorem cells9_split_7_1_1 (fsp : BitVec 64) :
    cells fsp 9 =
      cells fsp 7 ∗
      (∃∗ v56 : BitVec 64, (fsp + 56#64) ↦₆₄ v56) ∗
      (∃∗ v64 : BitVec 64, (fsp + 64#64) ↦₆₄ v64) := by
  rw [← ProofLib.memRegion_cells fsp 9 (by decide),
      ProofLib.memRegion_split' (b := fsp) (n := 56) (k := 16)
        (b' := fsp + 56#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 56#64) (n := 8) (k := 8)
        (b' := fsp + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells fsp 7 (by decide),
      ProofLib.memRegion_eight (fsp + 56#64),
      ProofLib.memRegion_eight (fsp + 64#64)]

theorem cells7_56_64_entails_cells9 (fsp v56 v64 : BitVec 64) :
    cells fsp 7 ∗ ((fsp + 56#64) ↦₆₄ v56) ∗ ((fsp + 64#64) ↦₆₄ v64) ⊢
      cells fsp 9 := by
  rw [cells9_split_7_1_1 fsp]
  exact sepConj_mono_right
    (sepConj_mono (Entails.sepExists_right v56 (Entails.refl _))
      (Entails.sepExists_right v64 (Entails.refl _)))

theorem memRegion_out_err_open (out : BitVec 64) :
    memRegion out polyEncoderSize ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d8 : BitVec 8,
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₈ d8) ∗ memRegion (out + 9#64) 391 := by
  change memRegion out 400 ⊢ _
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 392)
        (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 391)
        (b' := out + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, ProofLib.memRegion_one (out + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d8
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d8 ?_)
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_out_ok_open (out : BitVec 64) :
    memRegion out polyEncoderSize ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d392 : BitVec 32,
        (out ↦₆₄ d0) ∗ memRegion (out + 8#64) 384 ∗
          ((out + 392#64) ↦₃₂ d392) ∗ memRegion (out + 396#64) 4 := by
  change memRegion out 400 ⊢ _
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 392)
        (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 384) (k := 8)
        (b' := out + 392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 392#64) (n := 4) (k := 4)
        (b' := out + 396#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, ProofLib.memRegion_four (out + 392#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d392
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d392 ?_)
  exact Entails.of_eq (by ac_rfl)

/-! ## `protoPolynomialEncoderAt` Open / Close Helpers and Subroutine Contracts -/

/-- Remaining parts of `protoPolynomialEncoderAt A pbA pb` after exposing `pbA + 8`, `pbA + 16`,
    `pbA + 32`, `pbA + 40`, `pbA + 48`, and the `pts` and `polys` element arrays. -/
def protoPolyEncoderRest (A : RustAlloc) (pbA ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder) : SepProp :=
  ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0 ∧
    pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
  (pbA ↦₆₄ ptsCap) ∗
  (if ptsCap = 0 then emp
   else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
     memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
       ((ptsCap.toNat - pb.pts.length) * 24)) ∗
  ((pbA + 24#64) ↦₆₄ polysCap) ∗
  (if polysCap = 0 then emp
   else A.live polysPtr (polysCap.toNat * 24) 8 ∗
     memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
       ((polysCap.toNat - pb.polys.length) * 24)) ∗
  memRegion (pbA + 52#64) 4

theorem vecBuf_vecU8_entails_sepConj (A : RustAlloc) (cap ptr : BitVec 64) (bss : List (List (BitVec 8))) :
    vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) cap ptr bss ⊢
      ⌜bss.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr bss ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 24) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (bss.length * 24)) ((cap.toNat - bss.length) * 24)) := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hc : cap = 0
  · subst hc
    have hbss : bss = [] := by
      cases bss with
      | nil => rfl
      | cons _ _ => simp [BitVec.toNat_ofNat] at hle
    subst hbss
    simp [arrayAt]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem sepConj_entails_vecBuf_vecU8 (A : RustAlloc) (cap ptr : BitVec 64) (bss : List (List (BitVec 8))) :
    ⌜bss.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr bss ∗
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * 24) 8 ∗
       memRegion (ptr + BitVec.ofNat 64 (bss.length * 24)) ((cap.toNat - bss.length) * 24)) ⊢
      vecBuf A 24 8 (fun bs addr => vecU8 A addr bs) cap ptr bss := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hc : cap = 0
  · subst hc
    have hbss : bss = [] := by
      cases bss with
      | nil => rfl
      | cons _ _ => simp [BitVec.toNat_ofNat] at hle
    subst hbss
    simp [arrayAt]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem protoPolyEncoder_open (A : RustAlloc) (pbA : BitVec 64) (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderAt A pbA pb ⊢
      ∃∗ ptsCap : BitVec 64, ∃∗ ptsPtr : BitVec 64,
      ∃∗ polysCap : BitVec 64, ∃∗ polysPtr : BitVec 64,
        ⌜pb.pts.length < 2 ^ 63 ∧ pb.polys.length < 2 ^ 63⌝ ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecHeaderBytes
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro polysCap
  apply Entails.sepExists_elim; intro polysPtr
  apply Entails.sepExists_elim; intro ptsCap
  apply Entails.sepExists_elim; intro ptsPtr
  refine Entails.sepExists_right ptsCap (Entails.sepExists_right ptsPtr
    (Entails.sepExists_right polysCap (Entails.sepExists_right polysPtr ?_)))
  unfold vecAt vecHeader protoPolyEncoderRest
  refine Entails.trans (sepConj_mono (sepConj_mono_right (vecBuf_vecU8_entails_sepConj A ptsCap ptsPtr pb.pts))
    (sepConj_mono_left (sepConj_mono_right (vecBuf_vecU8_entails_sepConj A polysCap polysPtr pb.polys)))) ?_
  have ha1 : (pbA + 24#64) + 8#64 = pbA + 32#64 := by bv_omega
  have ha2 : (pbA + 24#64) + 16#64 = pbA + 40#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      ⌜pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       ((pbA ↦₆₄ ptsCap) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((ptsCap.toNat - pb.pts.length) * 24)) ∗
        ((pbA + 24#64) ↦₆₄ polysCap) ∗
        (if polysCap = 0 then emp
         else A.live polysPtr (polysCap.toNat * 24) 8 ∗
           memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((polysCap.toNat - pb.polys.length) * 24)) ∗
        memRegion (pbA + 52#64) 4)) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  apply Entails.pure_left; rintro ⟨h4, h5, h6⟩
  have hlt1 : pb.pts.length < 2 ^ 63 := by omega
  have hlt2 : pb.polys.length < 2 ^ 63 := by omega
  refine Entails.pure_right ⟨hlt1, hlt2⟩ ?_
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0 ∧
        pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       ((pbA ↦₆₄ ptsCap) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
             ((ptsCap.toNat - pb.pts.length) * 24)) ∗
        ((pbA + 24#64) ↦₆₄ polysCap) ∗
        (if polysCap = 0 then emp
         else A.live polysPtr (polysCap.toNat * 24) 8 ∗
           memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((polysCap.toNat - pb.polys.length) * 24)) ∗
        memRegion (pbA + 52#64) 4)) = _ by ac_rfl))
  exact Entails.pure_right ⟨h1, h2, h3, h4, h5, h6⟩ (Entails.refl _)

theorem protoPolyEncoder_close (A : RustAlloc) (pbA ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
    ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
    ((pbA + 32#64) ↦₆₄ polysPtr) ∗
    ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
    ((pbA + 48#64) ↦₃₂ pb.idx) ∗
    arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
    arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
    protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ⊢
      protoPolynomialEncoderAt A pbA pb := by
  unfold protoPolynomialEncoderAt vecVecU8At vecOf vecHeaderBytes
    protoPolynomialEncoderPolysOff protoPolynomialEncoderIdxOff
    protoPolynomialEncoderPadOff protoPolynomialEncoderPadSize
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_right polysCap (Entails.sepExists_right polysPtr
    (Entails.sepExists_right ptsCap (Entails.sepExists_right ptsPtr ?_)))
  unfold vecAt vecHeader protoPolyEncoderRest
  refine Entails.trans ?_
    (sepConj_mono (sepConj_mono_right (sepConj_entails_vecBuf_vecU8 A ptsCap ptsPtr pb.pts))
      (sepConj_mono_left (sepConj_mono_right (sepConj_entails_vecBuf_vecU8 A polysCap polysPtr pb.polys))))
  have ha1 : (pbA + 24#64) + 8#64 = pbA + 32#64 := by bv_omega
  have ha2 : (pbA + 24#64) + 16#64 = pbA + 40#64 := by bv_omega
  rw [ha1, ha2]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0 ∧
        pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      ((pbA ↦₆₄ ptsCap) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
            ((ptsCap.toNat - pb.pts.length) * 24)) ∗
       ((pbA + 24#64) ↦₆₄ polysCap) ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       (if polysCap = 0 then emp
        else A.live polysPtr (polysCap.toNat * 24) 8 ∗
          memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
            ((polysCap.toNat - pb.polys.length) * 24)) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (pbA + 52#64) 4) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨h1, h2, h3, h4, h5, h6⟩
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜pb.pts.length ≤ ptsCap.toNat ∧ ptsCap.toNat * 24 < 2 ^ 63 ∧ ptsPtr ≠ 0⌝ ∗
      ⌜pb.polys.length ≤ polysCap.toNat ∧ polysCap.toNat * 24 < 2 ^ 63 ∧ polysPtr ≠ 0⌝ ∗
      ((pbA ↦₆₄ ptsCap) ∗ ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
       (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pb.pts.length * 24))
            ((ptsCap.toNat - pb.pts.length) * 24)) ∗
       ((pbA + 24#64) ↦₆₄ polysCap) ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
       ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
       arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
       (if polysCap = 0 then emp
        else A.live polysPtr (polysCap.toNat * 24) 8 ∗
          memRegion (polysPtr + BitVec.ofNat 64 (pb.polys.length * 24))
            ((polysCap.toNat - pb.polys.length) * 24)) ∗
       ((pbA + 48#64) ↦₃₂ pb.idx) ∗ memRegion (pbA + 52#64) 4) = _ by ac_rfl))
  exact Entails.pure_right ⟨h1, h2, h3⟩ (Entails.pure_right ⟨h4, h5, h6⟩ (Entails.refl _))

theorem drop_glue_poly16_ok_at_fromPb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName +
        (bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "<spqr::encoding::polynomial::PolyEncoder>::from_pb"))))
      (dropGluePoly16Spec A) := by
  have h := drop_glue_poly16_ok_ext hA.dealloc
  have haddr : (contractProg b ext).fnAddr encoderFromPbName +
      (bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>" "<spqr::encoding::polynomial::PolyEncoder>::from_pb"))) =
      (dropProgAtExt b ext).fnAddr dropPoly16Name := by
    simp only [contractProg, tripleRatchetProgAtExt, dropProgAtExt, Program.fnAddr_rebase,
      encoderFromPbName, dropPoly16Name,
      (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder>::from_pb"), (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>")]
    bv_omega
  rw [haddr]
  exact h

theorem drop_glue_proto_poly_encoder_ok_at_fromPb {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr encoderFromPbName +
        (bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "<spqr::encoding::polynomial::PolyEncoder>::from_pb"))))
      (dropProtoPolyEncoderSpec A) := by
  have h := drop_glue_proto_poly_encoder_ok_ext hA.dealloc
  have haddr : (contractProg b ext).fnAddr encoderFromPbName +
      (bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "<spqr::encoding::polynomial::PolyEncoder>::from_pb"))) =
      (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName := by
    simp only [contractProg, tripleRatchetProgAtExt, dropProgAtExt, Program.fnAddr_rebase,
      encoderFromPbName, dropProtoPolyEncoderName,
      (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder>::from_pb"), (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>")]
    bv_omega
  rw [haddr]
  exact h

/-! ## Shared Epilogue (`+1460 -> s0.lr`) and Exit Blocks (`+1448`, `+1496`, `+1612`, `+1572`, `+1548`, `+1648`) -/

/-- Shared epilogue at `+1460` (`0x6273c..0x6275c`):
    moves `x1` (`pbA`) into `x0`, restores `sp = s0.sp` and `x19..x30 = s0.x19..s0.x30`,
    and tail-calls `drop_glue::<ProtoPolynomialEncoder>` (`0x4c500`), returning at `s0.lr`. -/
theorem from_pb_epilogue {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s : State) (pbA : BitVec 64) (pb : ProtoPolynomialEncoder) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1024#64)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (protoPolynomialEncoderAt A pbA pb ∗
        savedCells s0 ∗
        stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
        A.pool ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack ∗ Frame) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align
  have hdrop_pb := drop_glue_proto_poly_encoder_ok_at_fromPb hA
  simp only [dropProtoPolyEncoderSpec] at hdrop_pb
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 1460 36
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName,
    protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpc hdrop_pb ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
  examples_hide_fetches
  unfold savedCells
  wp_steps
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      savedCells s0 ∗ stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
        (protoPolynomialEncoderAt A pbA pb ∗ A.pool ∗ Frame) by unfold savedCells; ac_rfl))
      (savedCells_restore_stack s0 (protoPolynomialEncoderAt A pbA pb ∗ A.pool ∗ Frame))) ?_
  rw [stackAt_encoderFromPb_split_dropStack48 s0.sp]
  wp_call hdrop_pb (⟨pbA, pb⟩ : DropProtoPolyEncoderGhost)
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Header error exit (`+1448 -> s0.lr`, `0x62730..0x62738 -> +1460`):
    writes `2#8` (`SerializationInvalid`) to `out + 8` and `2#64` (niche tag) to `out`,
    and runs `from_pb_epilogue`. -/
theorem from_pb_err_header {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s : State) (out pbA : BitVec 64) (pb : ProtoPolynomialEncoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1448#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1024#64)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        protoPolynomialEncoderAt A pbA pb ∗
        savedCells s0 ∗
        stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encoderFromPbName + 1460#64)
    (P_mid := protoPolynomialEncoderAt A pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool ∗
      resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
    (Q := fun sm => sm.sp = s0.sp - 1024#64 ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · encoder_from_pb_fetches_range b (Rust.withPanics ext) 1448 12
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine align_pre (by
      dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
        polynomialErrorByte, resultPolyEncoderErrTailSize]
      exact Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hep := from_pb_epilogue hA s0 s1 pbA pb
      (resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hvregs1
    exact SepWP.mono hep fun sf Pf _ _ ⟨hPf, hcs, hspf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hcs, hspf, htrf⟩

/-- `.polys` loop error exit (`+1496 -> s0.lr`, `0x62760..0x6277c -> +1460`):
    writes `SerializationInvalid` (`w19 = 2`) to `out`, calls `drop_glue::<[Poly; 16]>` (`0x4bebc`)
    on `fsp + 480`, loads `pbA` from `[fsp + 64]`, and runs `from_pb_epilogue`. -/
theorem from_pb_err_polys {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (pb : ProtoPolynomialEncoder)
    (errPolys : List (List GF16)) (herr_len : errPolys.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = 2#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        vecGF16ListOf A (fsp + 480#64) errPolys ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ pbA) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        stackAt fsp dropGluePoly16Stack ∗
        protoPolynomialEncoderAt A pbA pb ∗
        savedCells s0 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hdrop16 := drop_glue_poly16_ok_at_fromPb hA
  simp only [dropGluePoly16Spec] at hdrop16
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encoderFromPbName + 1460#64)
    (P_mid := protoPolynomialEncoderAt A pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool ∗
      resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · encoder_from_pb_fetches_range b (Rust.withPanics ext) 1496 32
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName,
      polyArrayBytes, NUM_POLYS, CHUNK_SIZE, BitVec.ofNat_eq_ofNat] at hpc hdrop16 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_call hdrop16 (⟨fsp + 480#64, errPolys⟩ : DropGluePoly16Ghost)
    wp_steps
    refine align_pre ?_ ?_
    · rw [hsp]
      have hfsp := hfsp_fn trivial
      subst hfsp
      have hc9 := cells7_56_64_entails_cells9 (s0.sp - 1024#64) out pbA
      have hfr := frame_928_rejoin_dropGlue s0.sp
      dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
        polynomialErrorByte, resultPolyEncoderErrTailSize]
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((cells (s0.sp - 1024#64) 7 ∗
            (((s0.sp - 1024#64) + 56#64) ↦₆₄ out) ∗
            (((s0.sp - 1024#64) + 64#64) ↦₆₄ pbA)) ∗
           memRegion ((s0.sp - 1024#64) + 72#64) 384 ∗
           cells ((s0.sp - 1024#64) + 456#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 480#64) 384 ∗
           cells ((s0.sp - 1024#64) + 864#64) 4 ∗
           cells ((s0.sp - 1024#64) + 896#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 920#64) 8 ∗
           stackAt (s0.sp - 1024#64) dropGluePoly16Stack) ∗
          (protoPolynomialEncoderAt A pbA pb ∗
           savedCells s0 ∗
           A.pool ∗
           ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391)) by ac_rfl)) ?_
      refine Entails.trans
        (sepConj_mono_left (Entails.trans (sepConj_mono_left hc9) hfr)) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hfsp := hfsp_fn trivial
    subst hfsp
    have hep := from_pb_epilogue hA s0 s1 pbA pb
      (resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hvregs1
    exact SepWP.mono hep fun sf Pf _ _ ⟨hPf, hcs, hspf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hcs, hspf, htrf⟩

/-- `.points` loop error exit (`+1612 -> s0.lr`, `0x627d4..0x627f4 -> +1460`):
    saves `x1` (`pbA`) in `x19`, writes `SerializationInvalid` (`w8 = 2`) to `out`,
    calls `drop_glue::<[Poly; 16]>` (`0x4bebc`) on `fsp + 480`, moves `x19` to `x1`,
    and runs `from_pb_epilogue`. -/
theorem from_pb_err_pts {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out pbA v64 : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (pb : ProtoPolynomialEncoder)
    (errPts : List (List GF16)) (herr_len : errPts.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1612#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        vecGF16ListOf A (fsp + 480#64) errPts ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        stackAt fsp dropGluePoly16Stack ∗
        protoPolynomialEncoderAt A pbA pb ∗
        savedCells s0 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hdrop16 := drop_glue_poly16_ok_at_fromPb hA
  simp only [dropGluePoly16Spec] at hdrop16
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encoderFromPbName + 1460#64)
    (P_mid := protoPolynomialEncoderAt A pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool ∗
      resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · encoder_from_pb_fetches_range b (Rust.withPanics ext) 1612 36
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName,
      polyArrayBytes, NUM_POLYS, CHUNK_SIZE, BitVec.ofNat_eq_ofNat] at hpc hdrop16 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_call hdrop16 (⟨fsp + 480#64, errPts⟩ : DropGluePoly16Ghost)
    wp_steps
    refine align_pre ?_ ?_
    · rw [hsp]
      have hfsp := hfsp_fn trivial
      subst hfsp
      have hc9 := cells7_56_64_entails_cells9 (s0.sp - 1024#64) out v64
      have hfr := frame_928_rejoin_dropGlue s0.sp
      dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
        polynomialErrorByte, resultPolyEncoderErrTailSize]
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((cells (s0.sp - 1024#64) 7 ∗
            (((s0.sp - 1024#64) + 56#64) ↦₆₄ out) ∗
            (((s0.sp - 1024#64) + 64#64) ↦₆₄ v64)) ∗
           memRegion ((s0.sp - 1024#64) + 72#64) 384 ∗
           cells ((s0.sp - 1024#64) + 456#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 480#64) 384 ∗
           cells ((s0.sp - 1024#64) + 864#64) 4 ∗
           cells ((s0.sp - 1024#64) + 896#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 920#64) 8 ∗
           stackAt (s0.sp - 1024#64) dropGluePoly16Stack) ∗
          (protoPolynomialEncoderAt A pbA pb ∗
           savedCells s0 ∗
           A.pool ∗
           ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391)) by ac_rfl)) ?_
      refine Entails.trans
        (sepConj_mono_left (Entails.trans (sepConj_mono_left hc9) hfr)) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hfsp := hfsp_fn trivial
    subst hfsp
    have hep := from_pb_epilogue hA s0 s1 pbA pb
      (resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hvregs1
    exact SepWP.mono hep fun sf Pf _ _ ⟨hPf, hcs, hspf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hcs, hspf, htrf⟩

/-- Shared success tail at `+1572 -> s0.lr` (`0x627ac..0x627d0 -> +1460 -> s0.lr`):
    given `((fsp + 72) ↦ₛ vecHeadersBytesOf pins vecs)` and `vecGF16HeapList A pins vecs`,
    copies the 384-byte headers from `fsp + 72` to `out + 8`, writes `x8 = tag` to `[out]`
    and `pb.idx` (`[pbA + 48]`) to `[out + 392]`, closes `protoPolynomialEncoderAt A pbA pb`
    and the 928-byte frame, and runs `from_pb_epilogue`. -/
theorem from_pb_ok_copy_out {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out pbA v64 tag : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder) (enc : PolyEncoder)
    (pins : List VecPin) (vecs : List (List GF16))
    (hpins_len : pins.length = vecs.length) (hvecs_len : vecs.length = 16)
    (hres :
      (out ↦₆₄ tag) ∗
      vecGF16ListOf A (out + 8#64) vecs ∗
      ((out + 392#64) ↦₃₂ pb.idx) ∗
      memRegion (out + 396#64) 4 ⊢
        resultPolyEncoderFromPbAt A out (.ok enc))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = tag)
    (hx20 : s.readReg64 .x20 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗
        vecGF16HeapList A pins vecs ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        stackAt fsp allocHookStack ∗
        cells fsp 7 ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        cells (fsp + 456#64) 3 ∗
        memRegion (fsp + 480#64) 384 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        memRegion (fsp - 4128#64) 32 ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.ok enc) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hbs_len : (vecHeadersBytesOf pins vecs).length = 384 := by
    rw [length_vecHeadersBytesOf pins vecs hpins_len, hvecs_len]
  have hmemcpy := hA.session_memcpy_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "memcpy"))
  simp only [sessionMemcpySpec] at hmemcpy
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_ok_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d392
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encoderFromPbName + 1460#64)
    (P_mid := protoPolynomialEncoderAt A pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool ∗
      resultPolyEncoderFromPbAt A out (.ok enc))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · encoder_from_pb_fetches_range b (Rust.withPanics ext) 1572 40
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_call hmemcpy (out + 8#64, fsp + 72#64, vecHeadersBytesOf pins vecs)
    wp_steps
    refine align_pre ?_ ?_
    · rw [hsp]
      have hfsp := hfsp_fn trivial
      subst hfsp
      have hvec := headers_heaps_entails_vecGF16ListOf A pins vecs (out + 8#64) hpins_len
      have hsrc : (((s0.sp - 1024#64) + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ⊢
          memRegion ((s0.sp - 1024#64) + 72#64) 384 := by
        rw [← hbs_len]
        exact ProofLib.pointsToBytes_entails_memRegion ((s0.sp - 1024#64) + 72#64) (vecHeadersBytesOf pins vecs)
      have hc9 := cells7_56_64_entails_cells9 (s0.sp - 1024#64) out v64
      have hfr := frame_928_rejoin s0.sp
      have hpb := protoPolyEncoder_close A pbA ptsCap ptsPtr polysCap polysPtr pb
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
           ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗
           ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           ((pbA + 48#64) ↦₃₂ pb.idx) ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
          savedCells s0 ∗
          ((cells (s0.sp - 1024#64) 7 ∗
            (((s0.sp - 1024#64) + 56#64) ↦₆₄ out) ∗
            (((s0.sp - 1024#64) + 64#64) ↦₆₄ v64)) ∗
           (((s0.sp - 1024#64) + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗
           cells ((s0.sp - 1024#64) + 456#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 480#64) 384 ∗
           cells ((s0.sp - 1024#64) + 864#64) 4 ∗
           cells ((s0.sp - 1024#64) + 896#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 920#64) 8 ∗
           memRegion ((s0.sp - 1024#64) - 4128#64) 32 ∗
           stackAt (s0.sp - 1024#64) allocHookStack) ∗
          A.pool ∗
          ((out ↦₆₄ tag) ∗
           (((out + 8#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A pins vecs) ∗
           ((out + 392#64) ↦₃₂ pb.idx) ∗
           memRegion (out + 396#64) 4) by ac_rfl)) ?_
      exact sepConj_mono hpb
        (sepConj_mono_right
          (sepConj_mono
            (Entails.trans (sepConj_mono hc9 (sepConj_mono_left hsrc)) hfr)
            (sepConj_mono_right
              (Entails.trans (sepConj_mono_right (sepConj_mono_left hvec)) hres))))
    · wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hfsp := hfsp_fn trivial
    subst hfsp
    have hep := from_pb_epilogue hA s0 s1 pbA pb
      (resultPolyEncoderFromPbAt A out (.ok enc))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hvregs1
    exact SepWP.mono hep fun sf Pf _ _ ⟨hPf, hcs, hspf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hcs, hspf, htrf⟩

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
