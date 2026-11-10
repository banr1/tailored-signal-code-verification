/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedA
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Block A Initialization (Part B)

Relocatable `[LibsignalPlacement]` allocations `11..15` (`+704 -> +820`), 16-header `Poly::zero()`
scatter (`+820 -> +976`), and combined `blockA_placed_sepWPp` (`+436 -> +976`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two exists_pow_two_eq_eight
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

set_option maxHeartbeats 800000 in
/-- Block A part 3 (`+704 -> +820`):
    performs allocations `11..15` (`2` bytes, align `2`), storing pointers `p11..p15`
    into registers `x23, x24, x25, x26, x0` while preserving `x19, x20, x21, x22, x27, x28, x29`. -/
theorem blockA_alloc_11_15_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 704#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s16 (p11 p12 p13 p14 p15 : BitVec 64),
      p11 ≠ 0#64 → p12 ≠ 0#64 → p13 ≠ 0#64 → p14 ≠ 0#64 → p15 ≠ 0#64 →
      s16.pc = (blkPl_416).base + 820#64 →
      s16.status = .Running →
      s16.sp = fsp →
      s16.trace = s0.trace →
      calleeSavedVRegs s16 = calleeSavedVRegs s →
      s16.readReg64 .x23 = p11 →
      s16.readReg64 .x24 = p12 →
      s16.readReg64 .x25 = p13 →
      s16.readReg64 .x26 = p14 →
      s16.readReg64 .x0 = p15 →
      s16.readReg64 .x19 = s.readReg64 .x19 →
      s16.readReg64 .x20 = s.readReg64 .x20 →
      s16.readReg64 .x21 = s.readReg64 .x21 →
      s16.readReg64 .x22 = s.readReg64 .x22 →
      s16.readReg64 .x27 = s.readReg64 .x27 →
      s16.readReg64 .x28 = s.readReg64 .x28 →
      s16.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s16
        (A.pool ∗
         (A.live p11 2 2 ∗ memRegion p11 2) ∗
         (A.live p12 2 2 ∗ memRegion p12 2) ∗
         (A.live p13 2 2 ∗ memRegion p13 2) ∗
         (A.live p14 2 2 ∗ memRegion p14 2) ∗
         (A.live p15 2 2 ∗ memRegion p15 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok; simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok; simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676_placed _ ext hA.handle_error Q s0 s P R
  clear hA
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 720#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom11 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr11
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr11; exact htr11⟩
  · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr11⟩
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 744#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom12 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr12
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr11, h, htrace] at htr12; exact htr12⟩
    · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr12⟩
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 768#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom13 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr13
        refine hpanic4676 _ _ ?_
        wp_steps
        exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.refl _, by rw [h_44, htr12, h_22, htr11, h, htrace] at htr13; exact htr13⟩
      · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro ⟨_, htr13⟩
        apply SepWPp.of_sepWP (mid := (blkPl_416).base + 792#64)
        wp_steps; wp_apply; wp_steps; wp_apply
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom14 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr14
          refine hpanic4676 _ _ ?_
          wp_steps
          exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.refl _, by rw [h_66, htr13, h_44, htr12, h_22, htr11, h, htrace] at htr14; exact htr14⟩
        · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro ⟨_, htr14⟩
          apply SepWPp.of_sepWP (mid := (blkPl_416).base + 816#64)
          wp_steps; wp_apply; wp_steps; wp_apply
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          by_cases hoom15 : sf_9.readReg64 (Reg.gpr 0#5) = 0#64
          · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro htr15
            refine hpanic4676 _ _ ?_
            wp_steps
            exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.refl _, by rw [h_88, htr14, h_66, htr13, h_44, htr12, h_22, htr11, h, htrace] at htr15; exact htr15⟩
          · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro ⟨_, htr15⟩
            have hcond15 : ¬(sf_9.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
              simpa [beq_iff_eq] using hoom15
            apply SepWPp.of_sepWP (mid := (blkPl_416).base + 820#64)
            wp_steps
            apply SepWP.done (by simp only [wp_norm, hcond15, ↓reduceIte]) (by wp_norm_lhs)
            have hsp8 : sf_8.sp = fsp := by
              simp only [h_89, hsp_sf_3, h_67, hsp_sf_2, h_45, hsp_sf_1, h_23, hsp_sf, h_1, hsp]
            rw [hsp8]
            refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
              (hcont _
                (sf_1.readReg64 (Reg.gpr 0#5))
                (sf_3.readReg64 (Reg.gpr 0#5))
                (sf_5.readReg64 (Reg.gpr 0#5))
                (sf_7.readReg64 (Reg.gpr 0#5))
                (sf_9.readReg64 (Reg.gpr 0#5))
                hoom11 hoom12 hoom13 hoom14 hoom15
                (by simp only [wp_norm, hcond15, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; rw [htr15, h_88, htr14, h_66, htr13, h_44, htr12, h_22, htr11, h, htrace])
                (by simp only [arm64_norm, wp_norm, *])
                (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                (by wp_norm_lhs) (by wp_norm_lhs))

set_option maxHeartbeats 800000 in
/-- Block A part 4 (`+820 -> +976`):
    scatters the 16 `Poly::zero()` headers (`cap = 1, ptr = p_k, len = 0`) into `[fsp + 256 .. fsp + 640)`,
    reloads `x19` from `[fsp + 88]`, sets `x20 = 0`, `x28 = 24`, and folds into
    `polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩)`. -/
theorem blockA_init_scatter_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (fsp vecsBase : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0#64) (hp1 : p1 ≠ 0#64) (hp2 : p2 ≠ 0#64) (hp3 : p3 ≠ 0#64)
    (hp4 : p4 ≠ 0#64) (hp5 : p5 ≠ 0#64) (hp6 : p6 ≠ 0#64) (hp7 : p7 ≠ 0#64)
    (hp8 : p8 ≠ 0#64) (hp9 : p9 ≠ 0#64) (hp10 : p10 ≠ 0#64) (hp11 : p11 ≠ 0#64)
    (hp12 : p12 ≠ 0#64) (hp13 : p13 ≠ 0#64) (hp14 : p14 ≠ 0#64) (hp15 : p15 ≠ 0#64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = p15)
    (hx19 : s.readReg64 .x19 = p8)
    (hx20 : s.readReg64 .x20 = p10)
    (hx21 : s.readReg64 .x21 = p6)
    (hx22 : s.readReg64 .x22 = p7)
    (hx23 : s.readReg64 .x23 = p11)
    (hx24 : s.readReg64 .x24 = p12)
    (hx25 : s.readReg64 .x25 = p13)
    (hx26 : s.readReg64 .x26 = p14)
    (hx28 : s.readReg64 .x28 = p9) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 976#64)
      s
      (((fsp + 88#64) ↦₆₄ vecsBase) ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
       (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
       (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 88#64) ↦₆₄ vecsBase) ∗
          ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
          ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
          ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
          polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x19 = vecsBase ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = 24#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29) := by
  rw [show
      (((fsp + 88#64) ↦₆₄ vecsBase) ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
       (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
       (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
       Frame) =
      (cells (fsp + 256#64) 48 ∗
       (((fsp + 88#64) ↦₆₄ vecsBase) ∗
        ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
        ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
        ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
        (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
        (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
        (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
        (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
        (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
        (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
        (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
        (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
        Frame)) by ac_rfl]
  iterate 48 (apply sepWP_cells_succ; intro _)
  apply sepWP_cells_zero
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, by wp_norm_lhs, by wp_norm_lhs, rfl, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (zeroPolySlotsAt_entails_polyListOf A 16 (fsp + 256#64))))))))))
  dsimp only [zeroPolySlotsAt]
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
  have hz0 := zeroPolySlotAt_intro A (fsp + 256#64) p0 hp0
  have hz1 := zeroPolySlotAt_intro A (fsp + 280#64) p1 hp1
  have hz2 := zeroPolySlotAt_intro A (fsp + 304#64) p2 hp2
  have hz3 := zeroPolySlotAt_intro A (fsp + 328#64) p3 hp3
  have hz4 := zeroPolySlotAt_intro A (fsp + 352#64) p4 hp4
  have hz5 := zeroPolySlotAt_intro A (fsp + 376#64) p5 hp5
  have hz6 := zeroPolySlotAt_intro A (fsp + 400#64) p6 hp6
  have hz7 := zeroPolySlotAt_intro A (fsp + 424#64) p7 hp7
  have hz8 := zeroPolySlotAt_intro A (fsp + 448#64) p8 hp8
  have hz9 := zeroPolySlotAt_intro A (fsp + 472#64) p9 hp9
  have hz10 := zeroPolySlotAt_intro A (fsp + 496#64) p10 hp10
  have hz11 := zeroPolySlotAt_intro A (fsp + 520#64) p11 hp11
  have hz12 := zeroPolySlotAt_intro A (fsp + 544#64) p12 hp12
  have hz13 := zeroPolySlotAt_intro A (fsp + 568#64) p13 hp13
  have hz14 := zeroPolySlotAt_intro A (fsp + 592#64) p14 hp14
  have hz15 := zeroPolySlotAt_intro A (fsp + 616#64) p15 hp15
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8 hz9 hz10 hz11 hz12 hz13 hz14 hz15
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hz0 (sepConj_mono hz1 (sepConj_mono hz2 (sepConj_mono hz3
          (sepConj_mono hz4 (sepConj_mono hz5 (sepConj_mono hz6 (sepConj_mono hz7
          (sepConj_mono hz8 (sepConj_mono hz9 (sepConj_mono hz10 (sepConj_mono hz11
          (sepConj_mono hz12 (sepConj_mono hz13 (sepConj_mono hz14
          (sepConj_mono_left hz15)))))))))))))))))))))))
  exact Entails.of_eq (by ac_rfl)

/-- Complete Block A (`+436 -> +976`):
    allocates 16 2-byte `Poly` buffers, stores `self_ptr` (`x24`) to `[fsp + 8]`,
    initializes `[fsp + 256 .. fsp + 640)` to `polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩)`,
    restores `[fsp + 112 .. fsp + 232)` to `memRegion (fsp + 112#64) 120`,
    and sets `x19 = vecsBase`, `x20 = 0`, `x28 = 24`. -/
theorem blockA_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp vecsBase u8 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s_out,
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
  have hcells : memRegion (fsp + 256#64) 384 = cells (fsp + 256#64) 48 :=
    ProofLib.memRegion_cells (fsp + 256#64) 48 (by decide)
  rw [hcells]
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (memRegion_112_split_spills fsp))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 6 (apply SepWPp.exists_elim; intro _)
  rename_i u184 u192 u200 u208 u216 u224
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_0_5_placed hA s0 s fsp hfsp_align u8 u184 u192 u200 u208 u216 u224
      (((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗ cells (fsp + 256#64) 48 ∗ Frame)
      R hpc hrun hsp htrace ?_)
  intro s6 p0 p1 p2 p3 p4 p5 hp0 hp1 hp2 hp3 hp4 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_6_10_placed hA s0 s6 fsp hfsp_align
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗ Frame)
      R hpc6 hrun6 hsp6 htr6 ?_)
  intro s11 p6 p7 p8 p9 p10 hp6 hp7 hp8 hp9 hp10 hpc11 hrun11 hsp11 htr11 hvregs11
    hx21_11 hx22_11 hx19_11 hx28_11 hx20_11 hx27_11 hx29_11
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_11_15_placed hA s0 s11 fsp hfsp_align
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ Frame)
      R hpc11 hrun11 hsp11 htr11 ?_)
  intro s16 p11 p12 p13 p14 p15 hp11 hp12 hp13 hp14 hp15 hpc16 hrun16 hsp16 htr16 hvregs16
    hx23_16 hx24_16 hx25_16 hx26_16 hx0_16 hx19_16 hx20_16 hx21_16 hx22_16 hx27_16 hx28_16 hx29_16
  rw [hx19_11] at hx19_16
  rw [hx20_11] at hx20_16
  rw [hx21_11] at hx21_16
  rw [hx22_11] at hx22_16
  rw [hx27_11, hx27_6] at hx27_16
  rw [hx28_11] at hx28_16
  rw [hx29_11, hx29_6] at hx29_16
  rw [hvregs11, hvregs6] at hvregs16
  have hscatter := blockA_init_scatter_placed (ext := ext) A s16 fsp vecsBase
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
    hfsp_align
    (A.pool ∗ ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ memRegion (fsp + 112#64) 72 ∗
     stackAt fsp allocHookStack ∗ Frame)
    hpc16 hrun16 hsp16 hx0_16 hx19_16 hx20_16 hx21_16 hx22_16 hx23_16 hx24_16 hx25_16 hx26_16 hx28_16
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWPp.of_sepWP (SepWP.mono hscatter ?_))
  rintro s_out Pm hpc_out hrun_out ⟨hPm, hsp_out, htr_out, hvregs_out, hx19_out, hx20_out, hx27_out, hx28_out, hx29_out⟩
  rw [htr16] at htr_out
  rw [hvregs16] at hvregs_out
  rw [hx27_16] at hx27_out
  rw [hx29_16] at hx29_out
  refine SepWPp.weaken_pre (Entails.trans hPm ?_)
    (hcont s_out hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out)
  refine Entails.trans (Entails.of_eq (show
    ((fsp + 88#64) ↦₆₄ vecsBase) ∗
    ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
    ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
    ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
    polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
    A.pool ∗ ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ memRegion (fsp + 112#64) 72 ∗
    stackAt fsp allocHookStack ∗ Frame =
    (memRegion (fsp + 112#64) 72 ∗
     ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
     ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
     ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0)) ∗
    (A.pool ∗ ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ ((fsp + 88#64) ↦₆₄ vecsBase) ∗
     polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
     stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (memRegion_112_fold_spills fsp p5 p4 p3 p2 p1 p0)) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.NextChunk
