/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsSlow
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedB
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Slow-Path Building Blocks

Relocatable `[LibsignalPlacement]` verification of the slow-path trigger (`+288 -> +436`), Block C
(`+4424 -> +296`), fast-path prefix (`0..i0`), and `blockA_lscl_placed_sepWPp`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv384_toNat
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

attribute [local simp, local arm64_norm, local wp_norm]
  madd_24_eq madd_24_eq' zext16_shl1_bv_eq zext16_shl1_nat_eq
  ofNat_add_one_eq ofNat_two_mul_add_one ofNat_two_mul_add_two
  lsr8_zext16_eq trunc8_zext16_eq

/-! ## 1. Slow-Path Trigger (`+288 -> +436`, 6 insns) -/

theorem pointsSlowTrigger_placed_sepWP [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (i0 : Nat) (hi0 : i0 < 16)
    (hidx_le : (pts[i0]'(by omega)).value.length ≤ (x.enc.idx.setWidth 16).toNat)
    (fsp u104 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) (s : State)
    (hpc : s.pc = (blkPl_416).base + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i0)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_416).base + 436#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        (pointListOf A (x.encA + 8#64) pts ∗
         ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
         Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (pointListOf A (x.encA + 8#64) pts ∗
       ((fsp + 104#64) ↦₆₄ u104) ∗
       Frame) post := by
  have hi0_len : i0 < pts.length := by omega
  rw [pointListOf_split_idx A (x.encA + 8#64) pts i0 hi0_len]
  apply SepWP.fold (pointOf_unfold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) (pts[i0]'hi0_len))
    (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  have hpure_pull : ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
      (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest = ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_pull]
  apply SepWP.pure_elim; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [pointBufBody_eq_slice_rest A cap ptr (pts[i0]'hi0_len) hlen_cap]
  rcases cmp_len_idx_le hidx_le with ⟨hule_len, hcond_eq, hcond_sub⟩
  wp_steps 6
  have hfold_point :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (pts[i0]'hi0_len).value.length) ∗
        gf16SliceAt ptr (pts[i0]'hi0_len).value ∗
        pointBufRest A cap ptr (pts[i0]'hi0_len) ⊢
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) (pts[i0]'hi0_len) :=
    pointOf_fold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) cap ptr (pts[i0]'hi0_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_point (by sep_focus)
  have hfold_list :
      pointListOf A (x.encA + 8#64) (pts.take i0) ∗
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i0)) (pts[i0]'hi0_len) ∗
        pointListOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i0 + 1))) (pts.drop (i0 + 1)) ⊢
        pointListOf A (x.encA + 8#64) pts := by
    rw [← pointListOf_split_idx A (x.encA + 8#64) pts i0 hi0_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, wp_norm, hule_len, hcond_eq, hcond_sub, ↓reduceIte])
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp)
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm])
      (by simpa [arm64_norm, wp_norm] using hx24)
      (by simpa [arm64_norm, wp_norm] using hx27)
      (by simp only [arm64_norm, wp_norm]))

/-! ## 2. Block C (`+4424 -> +296`, 15 instructions) -/

set_option maxHeartbeats 800000 in
theorem blockC_placed_sepWP [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (x : PolyNextChunkGhost)
    (pts : List Point) (hlen_pts : pts.length = 16)
    (polys : List LibsignalSpqrV1.Poly) (hlen_polys : polys.length = 16)
    (i0 : Nat)
    (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_416).base + 4424#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_416).base + 296#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x9 = BitVec.ofNat 64 i0 →
      sf.readReg64 .x19 = x.encA + 8#64 →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x28 = 24#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        (polyListOf A (x.encA + 8#64) polys ∗
         (x.encA ↦₆₄ 1#64) ∗
         memRegion (fsp + 256#64) 384 ∗
         memRegion (fsp + 656#64) 384 ∗
         ((fsp + 8#64) ↦₆₄ x.encA) ∗
         ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
         memRegion (fsp - 4128#64) 32 ∗
         stackAt fsp allocHookStack ∗
         A.pool ∗
         Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (polyListOf A (fsp + 256#64) polys ∗
       memRegion (fsp + 656#64) 384 ∗
       pointListOf A (x.encA + 8#64) pts ∗
       (x.encA ↦₆₄ 0#64) ∗
       ((fsp + 8#64) ↦₆₄ x.encA) ∗
       ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
       memRegion (fsp - 4128#64) 32 ∗
       stackAt fsp allocHookStack ∗
       A.pool ∗
       Frame) post := by
  have hvecs_polys : (polys.map LibsignalSpqrV1.Poly.coefficients).length = 16 := by
    simp [hlen_polys]
  have hvecs_pts : (pts.map Point.value).length = NUM_POLYS := by
    simp [NUM_POLYS, CHUNK_SIZE, hlen_pts]
  rw [polyListOf_eq_vecGF16ListOf, pointListOf_eq_vecGF16ListOf]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecGF16ListOf_entails_headers_heaps A
      (polys.map LibsignalSpqrV1.Poly.coefficients) (fsp + 256#64))) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro pins
  rw [sepConj_assoc, sepConj_assoc]
  apply sepWP_pure_left; intro hpins_len
  have hbs_len : (vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
    rw [length_vecHeadersBytesOf pins _ hpins_len, hvecs_polys]
  have hmemcpy := hA.session_memcpy_ok
  simp only [sessionMemcpySpec] at hmemcpy
  have hdrop0 : subroutine_ok ((blkPC_265).rebase (blkPl_265).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec A) :=
    drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hA.dealloc)
  have hdrop16 := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) hdrop0
  simp only [withLsCl, dropGluePoly16Spec] at hdrop16
  dsimp only [polyArrayBytes, NUM_POLYS, CHUNK_SIZE,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy hdrop16 hnext ⊢
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 265)
  wp_steps 4
  wp_call hmemcpy (fsp + 656#64, fsp + 256#64,
    vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients))
  have hsrc256 : ((fsp + 256#64) ↦ₛ
      vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ⊢
      memRegion (fsp + 256#64) 384 := by
    rw [← hbs_len]
    exact ProofLib.pointsToBytes_entails_memRegion (fsp + 256#64) _
  apply SepWP.fold hsrc256 (by sep_focus)
  have hjoin_drop_stack :
      memRegion (fsp - 4128#64) 32 ∗ stackAt s.sp 4096 ⊢
        stackAt fsp dropGluePoly16Stack := by
    rw [hsp, stackAt_dropGluePoly16_split_bottom fsp]
    exact Entails.refl _
  apply SepWP.fold hjoin_drop_stack (by sep_focus)
  wp_steps 2
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl_drop
  wp_call hdrop16 (⟨x.encA + 8#64, pts.map Point.value⟩ : DropGluePoly16Ghost)
  have hsplit_drop_stack :
      stackAt sf.sp dropGluePoly16Stack ⊢
        memRegion (fsp - 4128#64) 32 ∗ stackAt fsp 4096 := by
    rw [hsp_sf, hsp, stackAt_dropGluePoly16_split_bottom fsp]
    exact Entails.refl _
  apply SepWP.fold hsplit_drop_stack (by sep_focus)
  wp_steps 7
  wp_call hmemcpy (x.encA + 8#64, fsp + 656#64,
    vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients))
  have hsrc656 : ((fsp + 656#64) ↦ₛ
      vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ⊢
      memRegion (fsp + 656#64) 384 := by
    rw [← hbs_len]
    exact ProofLib.pointsToBytes_entails_memRegion (fsp + 656#64) _
  apply SepWP.fold hsrc656 (by sep_focus)
  have hfold_polys :
      ((x.encA + 8#64) ↦ₛ vecHeadersBytesOf pins (polys.map LibsignalSpqrV1.Poly.coefficients)) ∗
        vecGF16HeapList A pins (polys.map LibsignalSpqrV1.Poly.coefficients) ⊢
        polyListOf A (x.encA + 8#64) polys := by
    rw [polyListOf_eq_vecGF16ListOf]
    exact headers_heaps_entails_vecGF16ListOf A pins _ (x.encA + 8#64) hpins_len
  apply SepWP.fold hfold_polys (by sep_focus)
  wp_steps 2
  have hsp_sf1 : stackAt sf_1.sp 4096 ⊢ stackAt fsp allocHookStack := by
    rw [hsp_sf_1, hsp_sf, hsp]
    exact Entails.refl _
  apply SepWP.fold hsp_sf1 (by sep_focus)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, wp_norm])
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, Reg.x19, *])
      (by simp only [arm64_norm, wp_norm, Reg.x24, *])
      (by simp only [arm64_norm, wp_norm, Reg.x27, *])
      (by simp only [arm64_norm, wp_norm, Reg.x28, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]))

/-! ## 3. Prefix `0..i0` of the `Points` Fast-Path Loop (`+288 -> +288`) -/

set_option maxHeartbeats 800000 in
theorem pointsFastPrefix_step_placed_sepWP [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (out_ptr fsp u104 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (i : Nat) (hi15 : i < 15)
    (hidx_lt : (x.enc.idx.setWidth 16).toNat < (pts[i]'(by omega)).value.length)
    (Frame : SepProp) (s : State)
    (hpc : s.pc = (blkPl_416).base + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (2 * i))
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_416).base + 288#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = x.encA + 8#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x21 = 0#64 →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x28 = 24#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + 1)) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
          pointListOf A (x.encA + 8#64) pts ∗
          ((fsp + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          ((fsp + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
          ((fsp + 232#64) ↦₆₄ 32#64) ∗
          ((fsp + 240#64) ↦₆₄ out_ptr) ∗
          ((fsp + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
          Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
        pointListOf A (x.encA + 8#64) pts ∗
        ((fsp + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
        ((fsp + 104#64) ↦₆₄ u104) ∗
        ((fsp + 232#64) ↦₆₄ 32#64) ∗
        ((fsp + 240#64) ↦₆₄ out_ptr) ∗
        ((fsp + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
        Frame) post := by
  have hi16 : i < 16 := by omega
  have hi_len : i < pts.length := by omega
  have hi15_ne : (i == 15) = false := beq_eq_false_iff_ne.mpr (by omega)
  rw [pointListOf_split_idx A (x.encA + 8#64) pts i hi_len]
  apply SepWP.fold (pointOf_unfold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len))
    (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  have hpure_pull : ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
      (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest = ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_pull]
  apply SepWP.pure_elim; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [pointBufBody_eq_slice_rest A cap ptr (pts[i]'hi_len) hlen_cap,
      gf16SliceAt_split_idx ptr (pts[i]'hi_len).value (x.enc.idx.setWidth 16).toNat hidx_lt]
  have hlen_lt : (pts[i]'hi_len).value.length < 2 ^ 63 :=
    pointValue_len_lt_two_pow_63 hlen_cap hcap_bound
  rcases cmp_len_idx_gt (idx16 := x.enc.idx.setWidth 16) hidx_lt hlen_lt with
    ⟨hult_len, hule_len, hbeq_len, hsub_len⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_add_one_beq_16 hi16 with ⟨hcmp16_eq, hcmp16_sub⟩
  rw [hi15_ne] at hcmp16_eq hcmp16_sub
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
  apply sepWP_exists_left_sep; intro b0
  apply sepWP_exists_left_sep; intro b1
  wp_steps 30
  have hfold_bytes :
      (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 (((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 ((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value) ⊢
        (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + 1)) := by
    rw [chunkPointsBytes_zero_succ (x.enc.idx.setWidth 16) pts i hi_len hidx_lt]
    exact pointsToBytes_append_two_bytes out_ptr
      (chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) i
      (chunkPointsBytes_length (x.enc.idx.setWidth 16) pts 0 i) _ _
  apply SepWP.fold hfold_bytes (by sep_focus)
  have hfold_slice :
      gf16SliceAt ptr ((pts[i]'hi_len).value.take (x.enc.idx.setWidth 16).toNat) ∗
        ((ptr + BitVec.ofNat 64 (2 * (x.enc.idx.setWidth 16).toNat)) ↦₁₆
          ((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value) ∗
        gf16SliceAt (ptr + BitVec.ofNat 64 (2 * ((x.enc.idx.setWidth 16).toNat + 1)))
          ((pts[i]'hi_len).value.drop ((x.enc.idx.setWidth 16).toNat + 1)) ⊢
        gf16SliceAt ptr (pts[i]'hi_len).value := by
    rw [← gf16SliceAt_split_idx ptr (pts[i]'hi_len).value (x.enc.idx.setWidth 16).toNat hidx_lt]
    exact Entails.refl _
  apply SepWP.fold hfold_slice (by sep_focus)
  have hfold_point :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (pts[i]'hi_len).value.length) ∗
        gf16SliceAt ptr (pts[i]'hi_len).value ∗
        pointBufRest A cap ptr (pts[i]'hi_len) ⊢
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len) :=
    pointOf_fold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) cap ptr (pts[i]'hi_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_point (by sep_focus)
  have hfold_list :
      pointListOf A (x.encA + 8#64) (pts.take i) ∗
        pointOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len) ∗
        pointListOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (pts.drop (i + 1)) ⊢
        pointListOf A (x.encA + 8#64) pts := by
    rw [← pointListOf_split_idx A (x.encA + 8#64) pts i hi_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext _
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hcmp16_eq, hcmp16_sub])
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp)
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx24])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx27])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx28])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub]))

theorem pointsFastPrefix_placed_sepWP [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (out_ptr fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) :
    ∀ (k i : Nat) (u104 : BitVec 64) (s : State),
      (hik : i + k < 16) →
      (∀ (j : Nat) (hj : i ≤ j ∧ j < i + k),
        (x.enc.idx.setWidth 16).toNat < (pts[j]'(by omega)).value.length) →
      s.pc = (blkPl_416).base + 288#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x9 = BitVec.ofNat 64 i →
      s.readReg64 .x19 = x.encA + 8#64 →
      s.readReg64 .x20 = BitVec.ofNat 64 (2 * i) →
      s.readReg64 .x21 = 0#64 →
      s.readReg64 .x24 = x.encA →
      s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s.readReg64 .x28 = 24#64 →
      (∀ sf : State, ∀ u104' : BitVec 64,
        sf.pc = (blkPl_416).base + 288#64 →
        sf.status = .Running →
        sf.sp = fsp →
        sf.trace = s.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        sf.readReg64 .x9 = BitVec.ofNat 64 (i + k) →
        sf.readReg64 .x19 = x.encA + 8#64 →
        sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + k)) →
        sf.readReg64 .x21 = 0#64 →
        sf.readReg64 .x24 = x.encA →
        sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
        sf.readReg64 .x28 = 24#64 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
          ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + k)) ∗
            memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + k))) (32 - 2 * (i + k)) ∗
            pointListOf A (x.encA + 8#64) pts ∗
            ((fsp + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
            ((fsp + 104#64) ↦₆₄ u104') ∗
            ((fsp + 232#64) ↦₆₄ 32#64) ∗
            ((fsp + 240#64) ↦₆₄ out_ptr) ∗
            ((fsp + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + k))) ∗
            Frame) post) →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
        ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
          pointListOf A (x.encA + 8#64) pts ∗
          ((fsp + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          ((fsp + 104#64) ↦₆₄ u104) ∗
          ((fsp + 232#64) ↦₆₄ 32#64) ∗
          ((fsp + 240#64) ↦₆₄ out_ptr) ∗
          ((fsp + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
          Frame) post
  | 0, i, u104, s, _hik, _hfast, hpc, hrun, hsp, hx9, hx19, hx20, hx21, hx24, hx27, hx28, hnext => by
    simp only [Nat.add_zero] at hnext
    exact hnext s u104 hpc hrun hsp rfl rfl hx9 hx19 hx20 hx21 hx24 hx27 hx28 rfl
  | k + 1, i, u104, s, hik, hfast, hpc, hrun, hsp, hx9, hx19, hx20, hx21, hx24, hx27, hx28, hnext => by
    have hi15 : i < 15 := by omega
    refine pointsFastPrefix_step_placed_sepWP A ext x pts hlen_pts out_ptr fsp u104 hfsp_align
      i hi15 (hfast i ⟨by omega, by omega⟩) Frame s
      hpc hrun hsp hx9 hx19 hx20 hx21 hx24 hx27 hx28 ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1 hx27_1 hx28_1 hx29_1
    have hik' : (i + 1) + k < 16 := by omega
    have hadd_assoc : (i + 1) + k = i + (k + 1) := by omega
    refine pointsFastPrefix_placed_sepWP A ext x pts hlen_pts out_ptr fsp hfsp_align Frame
      k (i + 1) (BitVec.ofNat 64 i) s1 hik'
      (fun j hj => hfast j ⟨by omega, by omega⟩)
      hpc1 hrun1 hsp1 hx9_1 hx19_1 hx20_1 hx21_1 hx24_1 hx27_1 hx28_1 ?_
    intro sf u104' hpcf hrunf hspf htrf hvregsf hx9f hx19f hx20f hx21f hx24f hx27f hx28f hx29f
    rw [hadd_assoc] at hx9f hx20f ⊢
    exact hnext sf u104' hpcf hrunf hspf (htrf.trans htr1) (hvregsf.trans hvregs1) hx9f hx19f hx20f hx21f hx24f hx27f hx28f
      (hx29f.trans hx29_1)

/-! ## 4. Placed `sepWPp_drop_frame_placed` and `blockA_lscl_placed_sepWPp` -/

theorem sepWPp_drop_frame_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {A : RustAlloc} {x : PolyNextChunkGhost} {s0 s : State}
    {F P R : SepProp}
    (h : SepWPp prog ret s P
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ (F ∗ R)) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A x.encA x.enc' ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool ∗
             stackAt s0.sp polyNextChunkStack ∗ (F ∗ R))) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F ∗ R)) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ (F ∗ R)))) :
    SepWPp prog ret s (F ∗ P)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A x.encA x.enc' ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  intro R0 hm hL
  have hm' : s.mem ⊨ P ∗ (F ∗ R0) := by
    rwa [show P ∗ (F ∗ R0) = (F ∗ P) ∗ R0 by ac_rfl]
  obtain ⟨sf, hsteps, hout⟩ := h (F ∗ R0) hm' hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcc⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hmf⟩
  · refine Or.inl ⟨hpc, hrun, F ∗ P_f, ?_, ⟨fun hFR => ?_, hsp, hcc⟩⟩
    · rwa [show (F ∗ P_f) ∗ R0 = P_f ∗ (F ∗ R0) by ac_rfl]
    · have hFR' : sf.mem ⊨ P_f ∗ (F ∗ R) := by
        rwa [show P_f ∗ (F ∗ R) = (F ∗ P_f) ∗ R by ac_rfl]
      have h1 := hpost hFR'
      rw [show (⌜sf.trace = s0.trace⌝ ∗
            chunkAt x.outA x.chunk ∗
            polyEncoderAt A x.encA x.enc' ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            A.pool ∗
            stackAt s0.sp polyNextChunkStack ∗ (F ∗ R)) =
          F ∗ (⌜sf.trace = s0.trace⌝ ∗
            chunkAt x.outA x.chunk ∗
            polyEncoderAt A x.encA x.enc' ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            A.pool ∗
            stackAt s0.sp polyNextChunkStack ∗ R) by ac_rfl] at h1
      exact Satisfies.of_sep_right h1
  · refine Or.inr (Or.inl ⟨hpan, F ∗ P_f, ?_, fun hFR => ?_⟩)
    · rwa [show (F ∗ P_f) ∗ R0 = P_f ∗ (F ∗ R0) by ac_rfl]
    · have hFR' : sf.mem ⊨ P_f ∗ (F ∗ R) := by
        rwa [show P_f ∗ (F ∗ R) = (F ∗ P_f) ∗ R by ac_rfl]
      have h1 : sf.mem ⊨ F ∗ (nextChunkOnPanic s0 sf ∗ R) := by
        have := hqp hFR'
        rwa [show F ∗ (nextChunkOnPanic s0 sf ∗ R) = nextChunkOnPanic s0 sf ∗ (F ∗ R) by ac_rfl]
      exact Satisfies.of_sep_right h1
  · exact False.elim (not_satisfies_false_sepConj hmf)

/-- `LibsignalCodeLoaded`-preserving wrapper around `blockA_placed_sepWPp` (`+436 -> +976`). -/
theorem blockA_lscl_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp vecsBase u8 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s_out,
      LibsignalCodeLoaded lsmpl s_out.mem →
      s_out.pc = (blkPl_416).base + 976#64 →
      s_out.status = .Running →
      s_out.sp = fsp →
      s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = vecsBase →
      s_out.readReg64 .x20 = 0#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 88#64) ↦₆₄ vecsBase) ∗
         memRegion (fsp + 112#64) 120 ∗
         polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗
       memRegion (fsp + 112#64) 120 ∗
       memRegion (fsp + 256#64) 384 ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  let s0' : State := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_416).base + 976#64)
  have hlr' : s0'.readReg64 (Reg.gpr 30#5) = (blkPl_416).base + 976#64 := by
    simp [s0', arm64_norm, wp_norm]
  have htr' : s.trace = s0'.trace := by
    simpa [s0', arm64_norm, wp_norm] using htrace
  refine sepWPp_seq_lscl (mid := s0'.readReg64 (Reg.gpr 30#5)) hcl ?_
  refine blockA_placed_sepWPp hA s0' s fsp vecsBase u8 hfsp_align Frame R hpc hrun hsp htr' ?_
  intro s_out hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out
  refine SepWPp.done (hlr' ▸ hpc_out) hrun_out (fun hcl_out => ?_)
  have htr_out0 : s_out.trace = s0.trace := by simpa [s0', arm64_norm, wp_norm] using htr_out
  exact hcont s_out hcl_out hpc_out hrun_out hsp_out htr_out0 hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out

end CryptoVerification.SpqrV1.Poly.NextChunk
