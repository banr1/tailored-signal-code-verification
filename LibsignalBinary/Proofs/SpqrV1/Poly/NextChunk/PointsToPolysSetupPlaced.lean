/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetup
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Per-Polynomial `pt_vec` Setup

Relocatable `[LibsignalPlacement]` verification of per-polynomial `pt_vec` allocation,
`enumeratePts` population, and `checkCompletePoints` validation (`+976 -> +1136`).
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
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_setup_pl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

/-! ## Placed Panic Helper (`+4572`) -/

private theorem next_chunk_panic_4572_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (h_panic : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
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
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine sepWPp_panic_of_sepWP_handle_error_placed h_panic s0 s
    (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) R ?_
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

private theorem sepWPp_panic_of_sepWP_4572_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (h_panic : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
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
    SepWPp.weaken_pre hPm
      (next_chunk_panic_4572_placed h_panic s0 sm fsp v40 v48 hfsp_align Rest R hpcm hrunm hspm htrm))

/-! ## 1. Placed `fillPtVecLoop` and `checkPtVecLoop` (`+1064..+1136`) -/

/-- One step of the `enumeratePts` fill loop (`+1064..+1084`). -/
theorem fillPtVecLoop_step_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (srcBase dstBase : BitVec 64)
    (i n : Nat) (y : GF16) (rest : List GF16)
    (Frame : SepProp)
    (hn_eq : n = i + (rest.length + 1))
    (hn_bound : n ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1064#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 i)
    (hx9 : s.readReg64 .x9 = dstBase + BitVec.ofNat 64 (4 * i) + 2#64)
    (hx19 : s.readReg64 .x19 = srcBase)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n) :
    let nextPC :=
      if rest.length = 0 then
        (blkPl_416).base + 1088#64
      else
        (blkPl_416).base + 1064#64
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) nextPC s
      (((srcBase + BitVec.ofNat 64 (2 * i)) ↦₁₆ y.value) ∗
       memRegion (dstBase + BitVec.ofNat 64 (4 * i)) (4 * (rest.length + 1)) ∗ Frame)
      (fun sf P =>
        (P ⊢ ((srcBase + BitVec.ofNat 64 (2 * i)) ↦₁₆ y.value) ∗
             ptAt { x := GF16.new (BitVec.ofNat 16 i), y := y } (dstBase + BitVec.ofNat 64 (4 * i)) ∗
             memRegion (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (4 * rest.length) ∗ Frame) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (i + 1) ∧
        sf.readReg64 .x9 = dstBase + BitVec.ofNat 64 (4 * (i + 1)) + 2#64 ∧
        sf.readReg64 .x19 = srcBase ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = BitVec.ofNat 64 n ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5)) := by
  dsimp only
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (memRegion_split_pt (dstBase + BitVec.ofNat 64 (4 * i)) rest.length (by omega)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro ux
  apply SepWP.exists_elim; intro uy
  have hsrc : srcBase + (BitVec.ofNat 64 i <<< 1#64) = srcBase + BitVec.ofNat 64 (2 * i) := by
    rw [show BitVec.ofNat 64 i <<< 1#64 = BitVec.ofNat 64 i * 2#64 by bv_bits]
    bv_omega
  have hdst_x : (dstBase + BitVec.ofNat 64 (4 * i) + 2#64) + 0xfffffffffffffffe#64 =
      dstBase + BitVec.ofNat 64 (4 * i) := by
    bv_omega
  have hdst_next : dstBase + BitVec.ofNat 64 (4 * i) + 4#64 =
      dstBase + BitVec.ofNat 64 (4 * (i + 1)) := by
    bv_omega
  have hx9_next : (dstBase + BitVec.ofNat 64 (4 * i) + 2#64) + 4#64 =
      dstBase + BitVec.ofNat 64 (4 * (i + 1)) + 2#64 := by
    bv_omega
  have hx8_next : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    bv_omega
  have hx8_16 : BitVec.truncate 16 (BitVec.truncate 32 (BitVec.ofNat 64 i)) = BitVec.ofNat 16 i := by
    bv_omega
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  by_cases hrem : rest.length = 0
  · refine SepWP.done ?_ (by wp_norm_lhs) ?_
    · have hn1 : n = i + 1 := by omega
      simp only [hrem, ↓reduceIte, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
        bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true]
    · refine ⟨?_, by wp_norm_lhs, by wp_norm_lhs, rfl, ?_, ?_, ?_, by wp_norm_lhs,
        by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs⟩
      · unfold ptAt GF16.new
        have hy16 : BitVec.truncate 16 (BitVec.zeroExtend 32 y.value) = y.value := by bv_bits
        simp only [hx8, hx9, hx19, hsrc, hdst_x, hdst_next, hx8_16, hy16]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hx8, hx8_next]
      · simp only [wp_norm, hx9, hx9_next]
      · simp only [wp_norm, hx19]
      · simp only [wp_norm, hx25, ← hn_eq]
  · have hne : (BitVec.ofNat 64 n != BitVec.ofNat 64 (i + 1)) = true := by
      rw [bne_iff_ne]
      intro h0
      bv_omega
    have hsub_ne : (BitVec.ofNat 64 n - BitVec.ofNat 64 (i + 1) == 0#64) = false := by
      apply Bool.eq_false_iff.mpr
      intro h0
      have h1 : BitVec.ofNat 64 n - BitVec.ofNat 64 (i + 1) = 0#64 := eq_of_beq h0
      bv_omega
    refine SepWP.done ?_ (by wp_norm_lhs) ?_
    · simp only [hrem, ↓reduceIte, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hne, hsub_ne, Bool.false_eq_true]
    · refine ⟨?_, by wp_norm_lhs, by wp_norm_lhs, rfl, ?_, ?_, ?_, by wp_norm_lhs,
        by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs⟩
      · unfold ptAt GF16.new
        have hy16 : BitVec.truncate 16 (BitVec.zeroExtend 32 y.value) = y.value := by bv_bits
        simp only [hx8, hx9, hx19, hsrc, hdst_x, hdst_next, hx8_16, hy16]
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hx8, hx8_next]
      · simp only [wp_norm, hx9, hx9_next]
      · simp only [wp_norm, hx19]
      · simp only [wp_norm, hx25, ← hn_eq]

/-- Full `enumeratePts` fill loop (`+1064 -> +1088`) over non-empty `ys`. -/
theorem fillPtVecLoop_placed_sepWPp [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q R : State → SepProp → Prop}
    (ys : List GF16) (hne : ys ≠ [])
    (s0 s : State) (srcBase dstBase : BitVec 64)
    (i n : Nat) (Frame : SepProp)
    (hn_eq : n = i + ys.length)
    (hn_bound : n ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1064#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 i)
    (hx9 : s.readReg64 .x9 = dstBase + BitVec.ofNat 64 (4 * i) + 2#64)
    (hx19 : s.readReg64 .x19 = srcBase)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hcont : ∀ sf,
      sf.pc = (blkPl_416).base + 1088#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = BitVec.ofNat 64 n →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sf
        (gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * i)) ys ∗
         ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i ys) ∗ Frame)
        Q R) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * i)) ys ∗
       memRegion (dstBase + BitVec.ofNat 64 (4 * i)) (4 * ys.length) ∗ Frame)
      Q R := by
  induction ys generalizing s i Frame with
  | nil => contradiction
  | cons y rest ih =>
    have hgf : gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * i)) (y :: rest) =
        ((srcBase + BitVec.ofNat 64 (2 * i)) ↦₁₆ y.value) ∗
        gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * (i + 1))) rest := by
      have haddr : srcBase + BitVec.ofNat 64 (2 * i) + 2#64 = srcBase + BitVec.ofNat 64 (2 * (i + 1)) := by
        bv_omega
      simp only [gf16SliceAt, arrayAt, gf16At, gf16Stride, BitVec.ofNat_eq_ofNat, haddr]
    have hpt : ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i (y :: rest)) =
        ptAt { x := GF16.new (BitVec.ofNat 16 i), y := y } (dstBase + BitVec.ofNat 64 (4 * i)) ∗
        ptSliceAt (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (PolyEncoder.enumeratePts (i + 1) rest) := by
      have haddr : dstBase + BitVec.ofNat 64 (4 * i) + 4#64 = dstBase + BitVec.ofNat 64 (4 * (i + 1)) := by
        bv_omega
      simp only [PolyEncoder.enumeratePts, ptSliceAt, arrayAt, ptStride, BitVec.ofNat_eq_ofNat, haddr]
    have hstep := fillPtVecLoop_step_placed_sepWP (ext := ext) s srcBase dstBase i n y rest
      (gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * (i + 1))) rest ∗ Frame)
      (by simpa using hn_eq) hn_bound hpc hrun hx8 hx9 hx19 hx25
    dsimp only at hstep
    cases rest with
    | nil =>
      simp only [List.length_nil, ↓reduceIte, Nat.mul_zero, ProofLib.memRegion_zero] at hstep
      refine SepWPp.weaken_pre (by rw [hgf]; exact Entails.of_eq (by ac_rfl))
        (SepWPp.of_sepWP (SepWP.mono hstep ?_))
      intro sf P hpc_sf hrun_sf ⟨hP, hsp, htr, hvregs, _, _, _, hx20, hx24, hx25', hx26, hx27, hx28, hx29, hx30⟩
      have hP' : P ⊢ gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * i)) [y] ∗
          ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i [y]) ∗ Frame := by
        rw [hgf, hpt]
        simp only [PolyEncoder.enumeratePts, ptSliceAt, arrayAt]
        exact Entails.trans hP (Entails.of_eq (by ac_rfl))
      exact SepWPp.weaken_pre hP'
        (hcont sf hpc_sf hrun_sf hsp htr hvregs hx20 hx24 hx25' hx26 hx27 hx28 hx29 hx30)
    | cons y' rest' =>
      have hlen_ne : (y' :: rest').length ≠ 0 := by simp
      simp only [hlen_ne, ↓reduceIte] at hstep
      refine SepWPp.weaken_pre (by rw [hgf, List.length_cons]; exact Entails.of_eq (by ac_rfl))
        (SepWPp.of_sepWP (SepWP.mono hstep ?_))
      intro sm Pm hpc_sm hrun_sm ⟨hPm, hsp_m, htr_m, hvregs_m, hx8_m, hx9_m, hx19_m,
        hx20_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hx30_m⟩
      refine SepWPp.weaken_pre (Entails.trans hPm (Entails.of_eq (by ac_rfl)))
        (ih (List.cons_ne_nil y' rest') sm (i + 1)
          (((srcBase + BitVec.ofNat 64 (2 * i)) ↦₁₆ y.value) ∗
           ptAt { x := GF16.new (BitVec.ofNat 16 i), y := y } (dstBase + BitVec.ofNat 64 (4 * i)) ∗ Frame)
          (by simp only [List.length_cons] at hn_eq ⊢; omega) hpc_sm hrun_sm hx8_m hx9_m hx19_m hx25_m ?_)
      intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f
      refine SepWPp.weaken_pre (by rw [hgf, hpt]; exact Entails.of_eq (by ac_rfl))
        (hcont sf hpc_f hrun_f (hsp_f.trans hsp_m) (htr_f.trans htr_m) (hvregs_f.trans hvregs_m)
          (hx20_f.trans hx20_m) (hx24_f.trans hx24_m) hx25_f
          (hx26_f.trans hx26_m) (hx27_f.trans hx27_m) (hx28_f.trans hx28_m)
          (hx29_f.trans hx29_m) (hx30_f.trans hx30_m))

/-- One step of the `checkCompletePoints` loop (`+1112 -> +1136/+1112`). -/
theorem checkPtVecLoop_step_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (dstBase : BitVec 64)
    (i n : Nat) (y : GF16) (rest : List GF16)
    (Frame : SepProp)
    (hn_eq : n = i + (rest.length + 1))
    (hn_bound : n ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1112#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (4 * i))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * n))
    (hx26 : s.readReg64 .x26 = dstBase) :
    let nextPC :=
      if rest.length = 0 then
        (blkPl_416).base + 1136#64
      else
        (blkPl_416).base + 1112#64
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) nextPC s
      (((dstBase + BitVec.ofNat 64 (4 * i)) ↦₁₆ BitVec.ofNat 16 i) ∗
       ((dstBase + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ y.value) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((dstBase + BitVec.ofNat 64 (4 * i)) ↦₁₆ BitVec.ofNat 16 i) ∗
              ((dstBase + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ y.value) ∗ Frame) ∧
        sm.sp = s.sp ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (4 * (i + 1)) ∧
        sm.readReg64 .x9 = BitVec.ofNat 64 (i + 1) ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x24 = BitVec.ofNat 64 (4 * n) ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = dstBase ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5)) := by
  dsimp only
  have hx8_next : BitVec.ofNat 64 (4 * i) + 4#64 = BitVec.ofNat 64 (4 * (i + 1)) := by
    bv_omega
  have hx9_next : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    bv_omega
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  by_cases hrem : rest.length = 0
  · refine SepWP.done ?_ (by wp_norm_lhs) ?_
    · have hn1 : n = i + 1 := by omega
      simp only [hrem, ↓reduceIte, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1, beq_self_eq_true]
    · refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_lhs, by wp_norm_lhs, rfl, ?_, ?_,
        by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · simp only [wp_norm, hx8, hx8_next]
      · simp only [wp_norm, hx9, hx9_next]
      · simp only [wp_norm, hx24, ← hn_eq]
  · have hne : (BitVec.ofNat 64 (4 * n) == BitVec.ofNat 64 (4 * (i + 1))) = false := by
      apply Bool.eq_false_iff.mpr
      intro h0
      have h1 := eq_of_beq h0
      bv_omega
    have hsub_ne : (BitVec.ofNat 64 (4 * n) - BitVec.ofNat 64 (4 * (i + 1)) == 0#64) = false := by
      apply Bool.eq_false_iff.mpr
      intro h0
      have h1 := eq_of_beq h0
      bv_omega
    refine SepWP.done ?_ (by wp_norm_lhs) ?_
    · simp only [hrem, ↓reduceIte, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hne, hsub_ne, Bool.false_eq_true]
    · refine ⟨Entails.of_eq (by ac_rfl), by wp_norm_lhs, by wp_norm_lhs, rfl, ?_, ?_,
        by wp_norm_lhs, ?_, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
      · simp only [wp_norm, hx8, hx8_next]
      · simp only [wp_norm, hx9, hx9_next]
      · simp only [wp_norm, hx24, ← hn_eq]

/-- Verification loop (`+1112 -> +1136`) over non-empty `ys`. -/
theorem checkPtVecLoop_placed_sepWPp [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q R : State → SepProp → Prop}
    (ys : List GF16) (hne : ys ≠ [])
    (s0 s : State) (dstBase : BitVec 64)
    (i n : Nat) (Frame : SepProp)
    (hn_eq : n = i + ys.length)
    (hn_bound : n ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1112#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (4 * i))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * n))
    (hx26 : s.readReg64 .x26 = dstBase)
    (hcont : ∀ sf,
      sf.pc = (blkPl_416).base + 1136#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x24 = BitVec.ofNat 64 (4 * n) →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = dstBase →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sf
        (ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i ys) ∗ Frame)
        Q R) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i ys) ∗ Frame)
      Q R := by
  induction ys generalizing s i Frame with
  | nil => contradiction
  | cons y rest ih =>
    have hpt : ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i (y :: rest)) =
        ((dstBase + BitVec.ofNat 64 (4 * i)) ↦₁₆ BitVec.ofNat 16 i) ∗
        ((dstBase + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ y.value) ∗
        ptSliceAt (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (PolyEncoder.enumeratePts (i + 1) rest) := by
      have haddr : dstBase + BitVec.ofNat 64 (4 * i) + 4#64 = dstBase + BitVec.ofNat 64 (4 * (i + 1)) := by
        bv_omega
      simp only [PolyEncoder.enumeratePts, ptSliceAt, arrayAt, ptAt, GF16.new, ptStride, BitVec.ofNat_eq_ofNat, haddr]
      ac_rfl
    have hstep := checkPtVecLoop_step_placed_sepWP (ext := ext) s dstBase i n y rest
      (ptSliceAt (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (PolyEncoder.enumeratePts (i + 1) rest) ∗ Frame)
      (by simpa using hn_eq) hn_bound hpc hrun hx8 hx9 hx24 hx26
    dsimp only at hstep
    cases rest with
    | nil =>
      simp only [List.length_nil, ↓reduceIte] at hstep
      refine SepWPp.weaken_pre (by rw [hpt]; exact Entails.of_eq (by ac_rfl))
        (SepWPp.of_sepWP (SepWP.mono hstep ?_))
      intro sf P hpc_f hrun_f ⟨hP, hsp_f, htr_f, hvregs_f, _, _, hx20_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hx30_f⟩
      refine SepWPp.weaken_pre (by rw [hpt]; exact Entails.trans hP (Entails.of_eq (by ac_rfl)))
        (hcont sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f)
    | cons y' rest' =>
      have hlen_ne : (y' :: rest').length ≠ 0 := by simp
      simp only [hlen_ne, ↓reduceIte] at hstep
      refine SepWPp.weaken_pre (by rw [hpt]; exact Entails.of_eq (by ac_rfl))
        (SepWPp.of_sepWP (SepWP.mono hstep ?_))
      intro sm Pm hpc_sm hrun_sm ⟨hPm, hsp_m, htr_m, hvregs_m, hx8_m, hx9_m,
        hx20_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hx30_m⟩
      refine SepWPp.weaken_pre (Entails.trans hPm (Entails.of_eq (by ac_rfl)))
        (ih (List.cons_ne_nil y' rest') sm (i + 1)
          (((dstBase + BitVec.ofNat 64 (4 * i)) ↦₁₆ BitVec.ofNat 16 i) ∗
           ((dstBase + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ y.value) ∗ Frame)
          (by simp only [List.length_cons] at hn_eq ⊢; omega) hpc_sm hrun_sm hx8_m hx9_m hx24_m hx26_m ?_)
      intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f
      refine SepWPp.weaken_pre (by rw [hpt]; exact Entails.of_eq (by ac_rfl))
        (hcont sf hpc_f hrun_f (hsp_f.trans hsp_m) (htr_f.trans htr_m) (hvregs_f.trans hvregs_m)
          (hx20_f.trans hx20_m) hx24_f (hx25_f.trans hx25_m)
          hx26_f (hx27_f.trans hx27_m) (hx28_f.trans hx28_m)
          (hx29_f.trans hx29_m) (hx30_f.trans hx30_m))

/-! ## 2. Placed Full Per-Polynomial Setup (`+976 -> +1136`) -/

/-- Full placed per-polynomial setup (`+976 -> +1136`):
    reads `pt = pts[j]` from `ptsBase + 24 * j`, allocates & populates `pt_vec`,
    verifies `checkCompletePoints`, stores `j + 1` at `[fsp + 32]` and `pt.value.length`
    at `[fsp + 40]`, and produces `ptVecBufAt A ptVecPtr pt.value`. -/
theorem setupPtVec_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s0 s : State) (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (hj : j < 16)
    (pt : Point) (hpt_bound : pt.value.length ≤ 0x0555555555555555)
    (u32 u40 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 976#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ s1 (ptVecPtr : BitVec 64),
      ptVecPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 1136#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = BitVec.ofNat 64 j →
      s1.readReg64 .x24 = BitVec.ofNat 64 (4 * pt.value.length) →
      s1.readReg64 .x25 = BitVec.ofNat 64 pt.value.length →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         ptVecBufAt A ptVecPtr pt.value ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗
       ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  unfold pointOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro ptCap
  apply SepWPp.exists_elim; intro ptPtr
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      A.pool ∗
      ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
      ⌜pt.value.length ≤ ptCap.toNat ∧ ptCap.toNat * 2 < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝ ∗
      (((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
       ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr (ptCap.toNat * 2) 2 ∗ arrayAt gf16At 2 ptPtr pt.value ∗
          memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2)) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗ ((fsp + 48#64) ↦₆₄ 2#64) ∗
       stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
  apply sepWPp_pure_mid; intro ⟨hpt_cap, hpt_cap_bound, hpt_ptr_ne⟩
  have hmadd : ptsBase + BitVec.ofNat 64 j * 24#64 = ptsBase + BitVec.ofNat 64 (24 * j) := by
    bv_omega
  have hlsl : BitVec.ofNat 64 pt.value.length <<< 2#64 = BitVec.ofNat 64 (4 * pt.value.length) := by
    rw [show BitVec.ofNat 64 pt.value.length <<< 2#64 = BitVec.ofNat 64 pt.value.length * 4#64 by bv_bits]
    bv_omega
  have hlsl_nat : BitVec.ofNat 64 pt.value.length <<< 2 = BitVec.ofNat 64 (4 * pt.value.length) :=
    hlsl
  have hnhi : (0x7ffffffffffffffe#64).ult (BitVec.ofNat 64 (4 * pt.value.length)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h0
    have h1 : (0x7ffffffffffffffe#64 : BitVec 64) < BitVec.ofNat 64 (4 * pt.value.length) :=
      BitVec.ult_iff_lt.mp h0
    bv_omega
  have hnhi_not : ¬((0x7ffffffffffffffe#64).ult (BitVec.ofNat 64 (4 * pt.value.length)) = true) := by
    simp [hnhi]
  have hnhi_lsl : (0x7ffffffffffffffe#64).ult (BitVec.ofNat 64 pt.value.length <<< 2) = false := by
    rw [hlsl_nat]; exact hnhi
  have hj_next : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
    bv_omega
  by_cases hys : pt.value = []
  · try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1136#64)
    wp_steps
    refine SepWP.done ?_ (by wp_norm_lhs) ?_
    · simp only [wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil, BitVec.ofNat_eq_ofNat,
        BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte, BitVec.sub_self]
    · have hptOf : (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
          ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
          ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
          (if ptCap = 0#64 then emp
           else A.live ptPtr (ptCap.toNat * 2) 2 ∗ arrayAt gf16At 2 ptPtr [] ∗
             memRegion (ptPtr + BitVec.ofNat 64 (0 * 2)) ((ptCap.toNat - 0) * 2))) ⊢
          pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt := by
        unfold pointOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
        refine Entails.sepExists_right ptCap (Entails.sepExists_right ptPtr ?_)
        simp only [hys, List.length_nil, BitVec.ofNat_eq_ofNat]
        rw [sepConj_pure_left_comm]
        exact Entails.pure_right ⟨by omega, hpt_cap_bound, hpt_ptr_ne⟩ (Entails.of_eq (by ac_rfl))
      refine SepWPp.weaken_pre ?_ (hcont _ 2#64 (by decide) ?_ (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm]; exact htrace)
        rfl
        (by simp only [wp_norm, hx20])
        (by simp only [wp_norm, hys, List.length_nil, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero])
        (by simp only [wp_norm, hys, List.length_nil, BitVec.ofNat_eq_ofNat])
        (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [wp_norm, hx28]) (by wp_norm_lhs))
      · simp only [hmadd, hj_next, hys, List.length_nil, BitVec.ofNat_eq_ofNat]
        refine Entails.trans (Entails.of_eq (show _ =
          (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
           ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
           ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
           (if ptCap = 0#64 then emp
            else A.live ptPtr (ptCap.toNat * 2) 2 ∗ arrayAt gf16At 2 ptPtr [] ∗
              memRegion (ptPtr + 0#64) ((ptCap.toNat - 0) * 2))) ∗
          emp ∗
          (A.pool ∗
           ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
           ((fsp + 40#64) ↦₆₄ 0#64) ∗
           ((fsp + 48#64) ↦₆₄ 2#64) ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hptOf (sepConj_mono_left (ptVecBufAt_nil A))) ?_
        exact Entails.of_eq (by ac_rfl)
      · simp only [wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil, BitVec.ofNat_eq_ofNat,
          BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte, BitVec.sub_self]
  · have hn_pos : 0 < pt.value.length := List.length_pos_iff.mpr hys
    have hcap_ne : ptCap ≠ 0#64 := by
      intro hc; subst hc; bv_omega
    simp only [hcap_ne, ↓reduceIte]
    have hlayout : LayoutOk (4 * pt.value.length) 2 :=
      ⟨by omega, ⟨1, rfl⟩, by omega⟩
    have hshim := hA.shim_ok
    simp only [sessionShimSpec] at hshim
    have halloc := hA.alloc_ok
    simp only [rustAllocSpec] at halloc
    have hpanic4572 := fun (s : State) (Rest : SepProp) =>
      @sepWPp_panic_of_sepWP_4572_placed _ ext Q hA.handle_error s0 s fsp
        (BitVec.ofNat 64 pt.value.length) 2#64 hfsp_align Rest R
    have hx24_ne : (BitVec.ofNat 64 (4 * pt.value.length) == 0#64) = false := by
      apply Bool.eq_false_iff.mpr; intro h0
      have h1 := eq_of_beq h0; bv_omega
    have hx24_sub_ne : (BitVec.ofNat 64 (4 * pt.value.length) - 0#64 == 0#64) = false := by
      simpa using hx24_ne
    have hx25_ne : (BitVec.ofNat 64 pt.value.length == 0#64) = false := by
      apply Bool.eq_false_iff.mpr; intro h0
      have h1 := eq_of_beq h0; bv_omega
    have hsz_toNat : (BitVec.ofNat 64 (4 * pt.value.length)).toNat = 4 * pt.value.length := by
      bv_omega
    try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4572 hcont ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1032#64)
    wp_steps; wp_call hshim; wp_steps; wp_call halloc; wp_steps
    refine SepWP.done ?_ (by wp_norm_lhs) ?_
    · simp only [wp_norm, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl, hx24_ne, ↓reduceIte, Bool.false_eq_true]
    · by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr0
        have hsp_sf : sf.sp = fsp := by simp only [h_1, hsp]
        rw [hsp_sf]
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (hpanic4572 _
            (A.pool ∗ stackAt fsp allocHookStack ∗
             ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
             ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
             ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
             A.live ptPtr (ptCap.toNat * 2) 2 ∗
             arrayAt gf16At 2 ptPtr pt.value ∗
             memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2) ∗
             ((fsp + 32#64) ↦₆₄ u32) ∗ Frame) ?_)
        wp_steps
        exact SepWP.done (by simp only [wp_norm, hoom, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
          ⟨Entails.refl _, by simp only [wp_norm, ‹sf_1.sp = sf.sp›, hsp_sf], by rw [h, htrace] at htr0; exact htr0⟩
      · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro ⟨_, htr0⟩
        have hcond_oom : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
          simpa [beq_iff_eq] using hoom
        apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1036#64)
        wp_steps
        refine SepWP.done (by simp only [wp_norm, hcond_oom, ↓reduceIte]) (by wp_norm_lhs) ?_
        apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1056#64)
        wp_steps
        refine SepWP.done (by simp only [wp_norm, hx25_ne, ↓reduceIte, Bool.not_false]) (by wp_norm_lhs) ?_
        apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1064#64)
        wp_steps
        refine SepWP.done ?_ (by wp_norm_lhs) ?_
        · wp_norm_goal
        · have hsp_sf : sf.sp = fsp := by simp only [h_1, hsp]
          rw [hsp_sf]
          try simp only [hlsl, hlsl_nat, hsz_toNat]
          have hsp_sf1 : sf_1.sp = fsp := by simp only [‹sf_1.sp = sf.sp›, hsp_sf]
          have hx25_sf1 : sf_1.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 pt.value.length := by
            rw [h_18, h_8]
          refine SepWPp.weaken_pre ?_
            (fillPtVecLoop_placed_sepWPp (ext := ext) (Q := Q)
              (R := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
              pt.value hys
              s0 _ ptPtr (sf_1.readReg64 (Reg.gpr 0#5)) 0 pt.value.length
              (A.pool ∗
               ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
               ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
               ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
               A.live ptPtr (ptCap.toNat * 2) 2 ∗
               memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2) ∗
               A.live (sf_1.readReg64 (Reg.gpr 0#5)) (4 * pt.value.length) 2 ∗
               ((fsp + 32#64) ↦₆₄ u32) ∗
               ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
               ((fsp + 48#64) ↦₆₄ 2#64) ∗
               stackAt fsp allocHookStack ∗ Frame)
              (by omega) hpt_bound
              (by wp_norm_goal)
              (by wp_norm_lhs)
              (by wp_norm_lhs)
              (by simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero])
              (by simp only [wp_norm, h_12, h_2])
              (by simp only [wp_norm, hx25_sf1])
              ?_)
          · unfold gf16SliceAt
            simp only [hmadd, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
            exact Entails.of_eq (by ac_rfl)
          · intro sFill hpcFill hrunFill hspFill htrFill hvregsFill
              hx20Fill hx24Fill hx25Fill hx26Fill hx27Fill hx28Fill hx29Fill hx30Fill
            have hspFill' : sFill.sp = fsp := by
              rw [hspFill]; simp only [wp_norm, hsp_sf1]
            have hx20Fill' : sFill.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 j := by
              change sFill.readReg64 .x20 = BitVec.ofNat 64 j
              rw [hx20Fill]; simp only [wp_norm, h_13, h_3]; exact hx20
            have hx24Fill' : sFill.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (4 * pt.value.length) := by
              change sFill.readReg64 .x24 = BitVec.ofNat 64 (4 * pt.value.length)
              rw [hx24Fill]; simp only [wp_norm, h_17, h_7]
            have hx26Fill' : sFill.readReg64 .x26 = sf_1.readReg64 (Reg.gpr 0#5) := by
              rw [hx26Fill]; simp only [wp_norm]
            apply SepWPp.of_sepWP (mid := (blkPl_416).base + 1112#64)
            wp_steps
            refine SepWP.done ?_ (by wp_norm_lhs) ?_
            · simp only [wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, ↓reduceIte, Bool.false_eq_true]
            · refine SepWPp.weaken_pre (by simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl))
                (checkPtVecLoop_placed_sepWPp (ext := ext) (Q := Q)
                  (R := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
                  pt.value hys
                  s0 _ (sf_1.readReg64 (Reg.gpr 0#5)) 0 pt.value.length
                  (gf16SliceAt (ptPtr + 0#64) pt.value ∗
                   A.pool ∗
                   ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
                   ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
                   ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                   A.live ptPtr (ptCap.toNat * 2) 2 ∗
                   memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2) ∗
                   A.live (sf_1.readReg64 (Reg.gpr 0#5)) (4 * pt.value.length) 2 ∗
                   ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
                   ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                   ((fsp + 48#64) ↦₆₄ 2#64) ∗
                   stackAt fsp allocHookStack ∗ Frame)
                  (by omega) hpt_bound
                  (by simp only [wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, ↓reduceIte, Bool.false_eq_true])
                  (by wp_norm_lhs)
                  (by wp_norm_lhs)
                  (by wp_norm_lhs)
                  (by simp only [wp_norm, hx24Fill'])
                  (by simp only [wp_norm, hx26Fill'])
                  ?_)
              intro sEnd hpcEnd hrunEnd hspEnd htrEnd hvregsEnd
                hx20End hx24End hx25End hx26End hx27End hx28End hx29End hx30End
              have hptOf : (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
                  ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
                  ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                  A.live ptPtr (ptCap.toNat * 2) 2 ∗
                  gf16SliceAt (ptPtr + 0#64) pt.value ∗
                  memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2)) ⊢
                  pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt := by
                unfold pointOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align gf16SliceAt
                dsimp only [gf16Stride]
                refine Entails.sepExists_right ptCap (Entails.sepExists_right ptPtr ?_)
                simp only [show (0 : BitVec 64) = 0#64 from rfl, hcap_ne, ↓reduceIte, BitVec.add_zero]
                rw [sepConj_pure_left_comm]
                exact Entails.pure_right ⟨hpt_cap, hpt_cap_bound, hpt_ptr_ne⟩ (Entails.of_eq (by ac_rfl))
              have hbuf : (ptSliceAt (sf_1.readReg64 (Reg.gpr 0#5) + 0#64) (PolyEncoder.enumeratePts 0 pt.value) ∗
                  A.live (sf_1.readReg64 (Reg.gpr 0#5)) (4 * pt.value.length) 2) ⊢
                  ptVecBufAt A (sf_1.readReg64 (Reg.gpr 0#5)) pt.value := by
                unfold ptVecBufAt
                have hlen_ne0 : pt.value.length ≠ 0 := by omega
                simp only [hlen_ne0, ↓reduceIte, BitVec.add_zero]
                exact Entails.pure_right hoom (Entails.of_eq (by ac_rfl))
              have hPEnd' :
                  (ptSliceAt (sf_1.readReg64 (Reg.gpr 0#5) + 0#64) (PolyEncoder.enumeratePts 0 pt.value) ∗
                   gf16SliceAt (ptPtr + 0#64) pt.value ∗
                   A.pool ∗
                   ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
                   ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
                   ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                   A.live ptPtr (ptCap.toNat * 2) 2 ∗
                   memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2) ∗
                   A.live (sf_1.readReg64 (Reg.gpr 0#5)) (4 * pt.value.length) 2 ∗
                   ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
                   ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                   ((fsp + 48#64) ↦₆₄ 2#64) ∗
                   stackAt fsp allocHookStack ∗ Frame) ⊢
                  (A.pool ∗
                   pointOf A (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
                   ptVecBufAt A (sf_1.readReg64 (Reg.gpr 0#5)) pt.value ∗
                   ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
                   ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                   ((fsp + 48#64) ↦₆₄ 2#64) ∗
                   stackAt fsp allocHookStack ∗ Frame) := by
                refine Entails.trans (Entails.of_eq (show
                  ptSliceAt (sf_1.readReg64 (Reg.gpr 0#5) + 0#64) (PolyEncoder.enumeratePts 0 pt.value) ∗
                  gf16SliceAt (ptPtr + 0#64) pt.value ∗
                  A.pool ∗
                  ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
                  ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
                  ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                  A.live ptPtr (ptCap.toNat * 2) 2 ∗
                  memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2) ∗
                  A.live (sf_1.readReg64 (Reg.gpr 0#5)) (4 * pt.value.length) 2 ∗
                  ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
                  ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                  ((fsp + 48#64) ↦₆₄ 2#64) ∗
                  stackAt fsp allocHookStack ∗ Frame =
                  (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
                   ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
                   ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                   A.live ptPtr (ptCap.toNat * 2) 2 ∗
                   gf16SliceAt (ptPtr + 0#64) pt.value ∗
                   memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2)) ∗
                  (ptSliceAt (sf_1.readReg64 (Reg.gpr 0#5) + 0#64) (PolyEncoder.enumeratePts 0 pt.value) ∗
                   A.live (sf_1.readReg64 (Reg.gpr 0#5)) (4 * pt.value.length) 2) ∗
                  (A.pool ∗
                   ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
                   ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
                   ((fsp + 48#64) ↦₆₄ 2#64) ∗
                   stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
                refine Entails.trans (sepConj_mono hptOf (sepConj_mono_left hbuf)) ?_
                exact Entails.of_eq (by ac_rfl)
              refine SepWPp.weaken_pre hPEnd'
                (hcont sEnd (sf_1.readReg64 (Reg.gpr 0#5)) hoom hpcEnd hrunEnd
                  ?_ ?_ ?_ ?_ hx24End ?_ hx26End ?_ ?_ ?_)
              · rw [hspEnd]; simp only [wp_norm, hspFill']
              · rw [htrEnd]; simp only [arm64_norm, wp_norm]; rw [htrFill]; simp only [arm64_norm, wp_norm]; rw [htr0, h, htrace]
              · rw [hvregsEnd]; simp only [arm64_norm, wp_norm]; rw [hvregsFill]; simp only [arm64_norm, wp_norm, *]
              · rw [hx20End]; simp only [wp_norm]; exact hx20Fill'
              · rw [hx25End]; simp only [wp_norm]; exact hx25Fill
              · rw [hx27End]; simp only [wp_norm]; rw [hx27Fill]; simp only [wp_norm, h_20, h_10]
              · rw [hx28End]; simp only [wp_norm]; rw [hx28Fill]; simp only [wp_norm, h_21, h_11]; exact hx28
              · rw [hx29End]; simp only [wp_norm]; rw [hx29Fill]; simp only [wp_norm, hcs_sf, hpost_sf]

end CryptoVerification.SpqrV1.Poly.NextChunk
