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
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Block A Initialization (Part A)

Relocatable `[LibsignalPlacement]` OOM panic blocks (`+4676`, `+4572`) and initial 2-byte
`Poly::zero()` allocations `0..10` (`+436 -> +704`) in Block `416`.
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

/-- OOM panic block at `+4676..+4684` (`mov w0, #2; mov w1, #2; bl handle_error`). -/
theorem next_chunk_panic_4676_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4676#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s P R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4676_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4676#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4676_placed h_panic s0 sm P R hpcm hrunm htrm))

/-- OOM panic block at `+4572..+4580` (`ldp x1, x0, [sp, #40]; lsl x0, x0, #2; bl handle_error`). -/
theorem next_chunk_panic_4572_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (fsp v40 v48 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Rest R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s
    (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4572_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (fsp v40 v48 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Rest R : SepProp)
    (hwp : SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4572#64) s
      (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, hspm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4572_placed h_panic s0 sm fsp v40 v48 hfsp_align Rest R hpcm hrunm hspm htrm))

/-- Block A part 1a (`+436 -> +488`):
    spills `x24` to `[fsp + 8]` and performs allocations `0..1` (`2` bytes, align `2`),
    spilling `p0..p1` to `[fsp + 224]` and `[fsp + 216]`. -/
theorem blockA_alloc_0_1_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u8 u216 u224 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s2 (p0 p1 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 →
      s2.pc = (blkPl_416).base + 488#64 →
      s2.status = .Running →
      s2.sp = fsp →
      s2.trace = s0.trace →
      calleeSavedVRegs s2 = calleeSavedVRegs s →
      s2.readReg64 .x27 = s.readReg64 .x27 →
      s2.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s2
        (A.pool ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
         (A.live p0 2 2 ∗ memRegion p0 2) ∗
         (A.live p1 2 2 ∗ memRegion p1 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok; simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok; simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676_placed _ ext hA.handle_error Q s0 s P R
  clear hA
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 460#64)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr0
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom0, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr0; exact htr0⟩
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr0⟩
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 484#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr1
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr0, h, htrace] at htr1; exact htr1⟩
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr1⟩
      have hcond1 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom1
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 488#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs)
      have hsp2 : sf_2.sp = fsp := by
        simp only [h_23, hsp_sf, h_1, hsp]
      have hx24 : s.readReg64 (Reg.gpr 24#5) = s.readReg64 .x24 := rfl
      rw [hsp2, hx24]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcont _
          (sf_1.readReg64 (Reg.gpr 0#5))
          (sf_3.readReg64 (Reg.gpr 0#5))
          hoom0 hoom1
          (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; rw [htr1, h_22, htr0, h, htrace])
          (by simp only [arm64_norm, wp_norm, *])
          (by wp_norm_lhs) (by wp_norm_lhs))

/-- Block A part 1b (`+488 -> +536`):
    performs allocations `2..3` (`2` bytes, align `2`),
    spilling `p2..p3` to `[fsp + 208]` and `[fsp + 200]`. -/
theorem blockA_alloc_2_3_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u200 u208 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s4 (p2 p3 : BitVec 64),
      p2 ≠ 0#64 → p3 ≠ 0#64 →
      s4.pc = (blkPl_416).base + 536#64 →
      s4.status = .Running →
      s4.sp = fsp →
      s4.trace = s0.trace →
      calleeSavedVRegs s4 = calleeSavedVRegs s →
      s4.readReg64 .x27 = s.readReg64 .x27 →
      s4.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗
         ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
         (A.live p2 2 2 ∗ memRegion p2 2) ∗
         (A.live p3 2 2 ∗ memRegion p3 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok; simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok; simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676_placed _ ext hA.handle_error Q s0 s P R
  clear hA
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 508#64)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom2 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr2
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom2, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr2; exact htr2⟩
  · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr2⟩
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 532#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom3 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr3
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom3, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr2, h, htrace] at htr3; exact htr3⟩
    · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr3⟩
      have hcond3 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom3
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 536#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, hcond3, ↓reduceIte]) (by wp_norm_lhs)
      have hsp2 : sf_2.sp = fsp := by
        simp only [h_23, hsp_sf, h_1, hsp]
      rw [hsp2]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcont _
          (sf_1.readReg64 (Reg.gpr 0#5))
          (sf_3.readReg64 (Reg.gpr 0#5))
          hoom2 hoom3
          (by simp only [wp_norm, hcond3, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; rw [htr3, h_22, htr2, h, htrace])
          (by simp only [arm64_norm, wp_norm, *])
          (by wp_norm_lhs) (by wp_norm_lhs))

/-- Block A part 1c (`+536 -> +584`):
    performs allocations `4..5` (`2` bytes, align `2`),
    spilling `p4..p5` to `[fsp + 192]` and `[fsp + 184]`. -/
theorem blockA_alloc_4_5_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u184 u192 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s6 (p4 p5 : BitVec 64),
      p4 ≠ 0#64 → p5 ≠ 0#64 →
      s6.pc = (blkPl_416).base + 584#64 →
      s6.status = .Running →
      s6.sp = fsp →
      s6.trace = s0.trace →
      calleeSavedVRegs s6 = calleeSavedVRegs s →
      s6.readReg64 .x27 = s.readReg64 .x27 →
      s6.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s6
        (A.pool ∗
         ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
         (A.live p4 2 2 ∗ memRegion p4 2) ∗
         (A.live p5 2 2 ∗ memRegion p5 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok; simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok; simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676_placed _ ext hA.handle_error Q s0 s P R
  clear hA
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 556#64)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom4 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr4
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom4, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr4; exact htr4⟩
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr4⟩
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 580#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom5 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr5
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom5, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr4, h, htrace] at htr5; exact htr5⟩
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr5⟩
      have hcond5 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom5
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 584#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, hcond5, ↓reduceIte]) (by wp_norm_lhs)
      have hsp2 : sf_2.sp = fsp := by
        simp only [h_23, hsp_sf, h_1, hsp]
      rw [hsp2]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcont _
          (sf_1.readReg64 (Reg.gpr 0#5))
          (sf_3.readReg64 (Reg.gpr 0#5))
          hoom4 hoom5
          (by simp only [wp_norm, hcond5, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; rw [htr5, h_22, htr4, h, htrace])
          (by simp only [arm64_norm, wp_norm, *])
          (by wp_norm_lhs) (by wp_norm_lhs))

/-- Block A part 1 (`+436 -> +584`):
    spills `x24` to `[fsp + 8]` and performs allocations `0..5` (`2` bytes, align `2`),
    spilling `p0..p5` to `[fsp + 224]` down to `[fsp + 184]`. -/
theorem blockA_alloc_0_5_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u8 u184 u192 u200 u208 u216 u224 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s6 (p0 p1 p2 p3 p4 p5 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 → p2 ≠ 0#64 → p3 ≠ 0#64 → p4 ≠ 0#64 → p5 ≠ 0#64 →
      s6.pc = (blkPl_416).base + 584#64 →
      s6.status = .Running →
      s6.sp = fsp →
      s6.trace = s0.trace →
      calleeSavedVRegs s6 = calleeSavedVRegs s →
      s6.readReg64 .x27 = s.readReg64 .x27 →
      s6.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s6
        (A.pool ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
         ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
         ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
         (A.live p0 2 2 ∗ memRegion p0 2) ∗
         (A.live p1 2 2 ∗ memRegion p1 2) ∗
         (A.live p2 2 2 ∗ memRegion p2 2) ∗
         (A.live p3 2 2 ∗ memRegion p3 2) ∗
         (A.live p4 2 2 ∗ memRegion p4 2) ∗
         (A.live p5 2 2 ∗ memRegion p5 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_0_1_placed hA s0 s fsp hfsp_align u8 u216 u224
      (((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗ Frame)
      R hpc hrun hsp htrace ?_)
  intro s2 p0 p1 hp0 hp1 hpc2 hrun2 hsp2 htr2 hvregs2 hx27_2 hx29_2
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_2_3_placed hA s0 s2 fsp hfsp_align u200 u208
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗ Frame)
      R hpc2 hrun2 hsp2 htr2 ?_)
  intro s4 p2 p3 hp2 hp3 hpc4 hrun4 hsp4 htr4 hvregs4 hx27_4 hx29_4
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_4_5_placed hA s0 s4 fsp hfsp_align u184 u192
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗ Frame)
      R hpc4 hrun4 hsp4 htr4 ?_)
  intro s6 p4 p5 hp4 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6
  rw [hvregs4, hvregs2] at hvregs6
  rw [hx27_2] at hx27_4
  rw [hx29_2] at hx29_4
  rw [hx27_4] at hx27_6
  rw [hx29_4] at hx29_6
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s6 p0 p1 p2 p3 p4 p5 hp0 hp1 hp2 hp3 hp4 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6)

set_option maxHeartbeats 800000 in
/-- Block A part 2 (`+584 -> +704`):
    performs allocations `6..10` (`2` bytes, align `2`), storing pointers `p6..p10`
    into registers `x21, x22, x19, x28, x20`. -/
theorem blockA_alloc_6_10_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 584#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s11 (p6 p7 p8 p9 p10 : BitVec 64),
      p6 ≠ 0#64 → p7 ≠ 0#64 → p8 ≠ 0#64 → p9 ≠ 0#64 → p10 ≠ 0#64 →
      s11.pc = (blkPl_416).base + 704#64 →
      s11.status = .Running →
      s11.sp = fsp →
      s11.trace = s0.trace →
      calleeSavedVRegs s11 = calleeSavedVRegs s →
      s11.readReg64 .x21 = p6 →
      s11.readReg64 .x22 = p7 →
      s11.readReg64 .x19 = p8 →
      s11.readReg64 .x28 = p9 →
      s11.readReg64 .x20 = p10 →
      s11.readReg64 .x27 = s.readReg64 .x27 →
      s11.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s11
        (A.pool ∗
         (A.live p6 2 2 ∗ memRegion p6 2) ∗
         (A.live p7 2 2 ∗ memRegion p7 2) ∗
         (A.live p8 2 2 ∗ memRegion p8 2) ∗
         (A.live p9 2 2 ∗ memRegion p9 2) ∗
         (A.live p10 2 2 ∗ memRegion p10 2) ∗
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
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 600#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom6 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr6
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr6; exact htr6⟩
  · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr6⟩
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 624#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom7 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr7
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr6, h, htrace] at htr7; exact htr7⟩
    · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr7⟩
      apply SepWPp.of_sepWP (mid := (blkPl_416).base + 648#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom8 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr8
        refine hpanic4676 _ _ ?_
        wp_steps
        exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.refl _, by rw [h_44, htr7, h_22, htr6, h, htrace] at htr8; exact htr8⟩
      · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro ⟨_, htr8⟩
        apply SepWPp.of_sepWP (mid := (blkPl_416).base + 672#64)
        wp_steps; wp_apply; wp_steps; wp_apply
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom9 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr9
          refine hpanic4676 _ _ ?_
          wp_steps
          exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.refl _, by rw [h_66, htr8, h_44, htr7, h_22, htr6, h, htrace] at htr9; exact htr9⟩
        · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro ⟨_, htr9⟩
          apply SepWPp.of_sepWP (mid := (blkPl_416).base + 696#64)
          wp_steps; wp_apply; wp_steps; wp_apply
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          by_cases hoom10 : sf_9.readReg64 (Reg.gpr 0#5) = 0#64
          · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro htr10
            refine hpanic4676 _ _ ?_
            wp_steps
            exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.refl _, by rw [h_88, htr9, h_66, htr8, h_44, htr7, h_22, htr6, h, htrace] at htr10; exact htr10⟩
          · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro ⟨_, htr10⟩
            have hcond10 : ¬(sf_9.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
              simpa [beq_iff_eq] using hoom10
            apply SepWPp.of_sepWP (mid := (blkPl_416).base + 704#64)
            wp_steps
            apply SepWP.done (by simp only [wp_norm, hcond10, ↓reduceIte]) (by wp_norm_lhs)
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
                hoom6 hoom7 hoom8 hoom9 hoom10
                (by simp only [wp_norm, hcond10, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; rw [htr10, h_88, htr9, h_66, htr8, h_44, htr7, h_22, htr6, h, htrace])
                (by simp only [arm64_norm, wp_norm, *])
                (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                (by wp_norm_lhs) (by wp_norm_lhs))

end CryptoVerification.SpqrV1.Poly.NextChunk
