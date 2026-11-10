/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExit
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `Poly::lagrange_sum` Loop and Basis Deallocation

**Checked by Lean.**

Verifies the `Poly::lagrange_sum` accumulation loop (`0x6adb4..0x6b2c8`, `+2608 -> +3908`),
`Vec<Poly>` basis deallocation (`+3908 -> +4004`), and combined `lagrangeSumAndFree_sepWPp`.
-/

@[expose] public section

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
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two_sm exists_pow_two_eq_eight_sm
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

/-! ## 1. `Poly::lagrange_sum` Loop (`0x6adb4..0x6b2c8`, `+2608 -> +3908`) -/

/-- Full iteration `i = 0` of `Poly::lagrange_sum` (`0x6adf0..0x6adec`, `+2668 -> +2668 / +3908`). -/
theorem lagrangeSumStepFirst_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (m n : Nat) (pt : Pt) (poly : Poly)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (hplen : poly.coefficients.length = n) (h1m : 1 + m = n)
    (s0 s : State) (fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 0)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 u112' u136',
      s1.pc = (if m = 0 then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3908#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = BitVec.ofNat 64 1 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         gf16SliceAt accPtr (Poly.addAssign Poly.zero (poly.multAssign pt.y)).coefficients ∗
         polyOf A (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
         ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 0) ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
         shiftSlotsRawAt fsp ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         tokenInitAt b ∗ reduceTableAt b ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       memRegion accPtr (2 * n) ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ 0#64) ∗
       tokenInitAt b ∗ reduceTableAt b ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hcs_ne : poly.coefficients ≠ [] := List.ne_nil_of_length_pos (by omega)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeSumClone_sepWPp hA 0 n pt poly hn_pos hn hplen
      s0 s fsp basisPtr ptVecPtr v27 u120 u128 hfsp_align
      (memRegion accPtr (2 * n) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ 0#64) ∗
       tokenInitAt b ∗ reduceTableAt b ∗ Frame) R
      hpc hrun hsp htrace hx21 hx24 hx25 hx26 hx27 hx28 hx29 ?_)
  intro s1 clonePtr hclone_ne hpc1 hrun1 hsp1 htr1 hvregs1
    hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP
    (mid := if m = 0 then
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3908#64
      else
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (parallelMult_sepWP hb poly.coefficients hcs_ne (by omega) pt.y.value
      s1 fsp clonePtr basisPtr (BitVec.ofNat 64 n) ptVecPtr v27 u112 u136 hfsp_align
      (A.pool ∗ A.live clonePtr (2 * n) 2 ∗ memRegion accPtr (2 * n) ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
       ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 0) ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ 0#64) ∗
       stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 (by rw [hx20_1, hplen]) hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 ?_)
  intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro u112'
  apply SepWP.exists_elim; intro u136'
  have hpm_len : (parallelMult pt.y poly.coefficients).length = n := by
    rw [parallelMult_length, hplen]
  have hpm_ne : parallelMult pt.y poly.coefficients ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (addAssignFirst_sepWP (parallelMult pt.y poly.coefficients) n hpm_ne hpm_len hn
      s2 fsp accPtr clonePtr hfsp_align
      (A.pool ∗ A.live clonePtr (2 * n) 2 ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 0) ∗
       ((fsp + 136#64) ↦₆₄ u136') ∗ shiftSlotsRawAt fsp ∗
       tokenInitAt b ∗ reduceTableAt b ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc2 hrun2 hsp2 hx22_2 ?_)
  intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx1_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeSumDeallocNext_sepWP hA (parallelMult pt.y poly.coefficients) 0 m n
      hn_pos hn hpm_len h1m s3 fsp clonePtr hclone_ne hfsp_align
      (gf16SliceAt accPtr (Poly.addAssignCoeffs [] (parallelMult pt.y poly.coefficients)) ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       tokenInitAt b ∗ reduceTableAt b ∗ Frame)
      hpc3 hrun3 hsp3 hx1_3 hx22_3 (by rw [hx25_3, hx25_2]) ?_)
  intro s4 hpc4 hrun4 hsp4 htr4 hvregs4 hx21_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
  apply SepWP.done hpc4 hrun4
  have hscalar : Poly.addAssignCoeffs [] (parallelMult pt.y poly.coefficients) =
      (Poly.addAssign Poly.zero (poly.multAssign pt.y)).coefficients := rfl
  rw [hscalar]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s4 u112' u136' hpc4 hrun4 hsp4
      (by rw [htr4, htr3, htr2, htr1])
      (by rw [hvregs4, hvregs3, hvregs2, hvregs1])
      hx21_4
      (by rw [hx24_4, hx24_3, hx24_2])
      hx25_4
      (by rw [hx26_4, hx26_3, hx26_2])
      (by rw [hx27_4, hx27_3, hx27_2])
      (by rw [hx28_4, hx28_3, hx28_2])
      (by rw [hx29_4, hx29_3, hx29_2, hx29_1]))

/-- Full iteration `i > 0` of `Poly::lagrange_sum` (`0x6adf0..0x6adec`, `+2668 -> +2668 / +3908`). -/
theorem lagrangeSumStepNext_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (i m n : Nat) (acc : Poly) (pt : Pt) (poly : Poly)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (halen : acc.coefficients.length = n) (hplen : poly.coefficients.length = n)
    (him : (i + 1) + m = n)
    (s0 s : State) (fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 u112' u136',
      s1.pc = (if m = 0 then
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3908#64
        else
          (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = BitVec.ofNat 64 (i + 1) →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         gf16SliceAt accPtr (Poly.addAssign acc (poly.multAssign pt.y)).coefficients ∗
         polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
         ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
         shiftSlotsRawAt fsp ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         tokenInitAt b ∗ reduceTableAt b ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       gf16SliceAt accPtr acc.coefficients ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       tokenInitAt b ∗ reduceTableAt b ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hcs_ne : poly.coefficients ≠ [] := List.ne_nil_of_length_pos (by omega)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeSumClone_sepWPp hA i n pt poly hn_pos hn hplen
      s0 s fsp basisPtr ptVecPtr v27 u120 u128 hfsp_align
      (gf16SliceAt accPtr acc.coefficients ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       tokenInitAt b ∗ reduceTableAt b ∗ Frame) R
      hpc hrun hsp htrace hx21 hx24 hx25 hx26 hx27 hx28 hx29 ?_)
  intro s1 clonePtr hclone_ne hpc1 hrun1 hsp1 htr1 hvregs1
    hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP
    (mid := if m = 0 then
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3908#64
      else
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (parallelMult_sepWP hb poly.coefficients hcs_ne (by omega) pt.y.value
      s1 fsp clonePtr basisPtr (BitVec.ofNat 64 n) ptVecPtr v27 u112 u136 hfsp_align
      (A.pool ∗ A.live clonePtr (2 * n) 2 ∗ gf16SliceAt accPtr acc.coefficients ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 (by rw [hx20_1, hplen]) hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 ?_)
  intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro u112'
  apply SepWP.exists_elim; intro u136'
  have hpm_len : (parallelMult pt.y poly.coefficients).length = n := by
    rw [parallelMult_length, hplen]
  have hpm_ne : parallelMult pt.y poly.coefficients ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (addAssignNext_sepWP acc.coefficients (parallelMult pt.y poly.coefficients) n
      hpm_ne halen hpm_len hn s2 fsp accPtr clonePtr hfsp_align
      (A.pool ∗ A.live clonePtr (2 * n) 2 ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       ((fsp + 136#64) ↦₆₄ u136') ∗ shiftSlotsRawAt fsp ∗
       tokenInitAt b ∗ reduceTableAt b ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc2 hrun2 hsp2 hx22_2 ?_)
  intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx1_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeSumDeallocNext_sepWP hA (parallelMult pt.y poly.coefficients) i m n
      hn_pos hn hpm_len him s3 fsp clonePtr hclone_ne hfsp_align
      (gf16SliceAt accPtr (Poly.addAssignCoeffs acc.coefficients (parallelMult pt.y poly.coefficients)) ∗
       polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       tokenInitAt b ∗ reduceTableAt b ∗ Frame)
      hpc3 hrun3 hsp3 hx1_3 hx22_3 (by rw [hx25_3, hx25_2]) ?_)
  intro s4 hpc4 hrun4 hsp4 htr4 hvregs4 hx21_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
  apply SepWP.done hpc4 hrun4
  have hscalar : Poly.addAssignCoeffs acc.coefficients (parallelMult pt.y poly.coefficients) =
      (Poly.addAssign acc (poly.multAssign pt.y)).coefficients := rfl
  rw [hscalar]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s4 u112' u136' hpc4 hrun4 hsp4
      (by rw [htr4, htr3, htr2, htr1])
      (by rw [hvregs4, hvregs3, hvregs2, hvregs1])
      hx21_4
      (by rw [hx24_4, hx24_3, hx24_2])
      hx25_4
      (by rw [hx26_4, hx26_3, hx26_2])
      (by rw [hx27_4, hx27_3, hx27_2])
      (by rw [hx28_4, hx28_3, hx28_2])
      (by rw [hx29_4, hx29_3, hx29_2, hx29_1]))

/-- Inductive tail loop of `Poly::lagrange_sum` for iterations `i ≥ 1` (`0x6adf0..0x6adec`, `+2668 -> +3908`). -/
theorem lagrangeSumTailLoop_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64) :
    ∀ (ptsRest : List Pt) (polysRest : List Poly) (i n : Nat) (acc : Poly)
      (hrest_ne : ptsRest ≠ []) (hlen_eq : ptsRest.length = polysRest.length)
      (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
      (halen : acc.coefficients.length = n)
      (hplen : ∀ p ∈ polysRest, p.coefficients.length = n)
      (hin : i + ptsRest.length = n)
      (s0 s : State) (fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136 : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
      (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64)
      (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
      (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 i)
      (hx24 : s.readReg64 .x24 = basisPtr)
      (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
      (hx26 : s.readReg64 .x26 = ptVecPtr)
      (hx27 : s.readReg64 .x27 = v27)
      (hx28 : s.readReg64 .x28 = 24#64)
      (hx29 : s.readReg64 .x29 = fsp + 1104#64)
      (hcont : ∀ s1 u112' u120' u128' u136',
        s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3908#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x24 = basisPtr →
        s1.readReg64 .x25 = BitVec.ofNat 64 n →
        s1.readReg64 .x26 = ptVecPtr →
        s1.readReg64 .x27 = v27 →
        s1.readReg64 .x28 = 24#64 →
        s1.readReg64 .x29 = fsp + 1104#64 →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
          (A.pool ∗
           gf16SliceAt accPtr (lagrangeSumFoldPoly acc ptsRest polysRest).coefficients ∗
           polyListOf A (basisPtr + BitVec.ofNat 64 (24 * i)) polysRest ∗
           ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ptsRest ∗
           ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
           ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ u120') ∗
           ((fsp + 128#64) ↦₆₄ u128') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
           shiftSlotsRawAt fsp ∗
           ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           ((fsp + 664#64) ↦₆₄ accPtr) ∗
           ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           tokenInitAt b ∗ reduceTableAt b ∗
           stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))),
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
        (A.pool ∗
         gf16SliceAt accPtr acc.coefficients ∗
         polyListOf A (basisPtr + BitVec.ofNat 64 (24 * i)) polysRest ∗
         ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ptsRest ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
         ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
         shiftSlotsRawAt fsp ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         tokenInitAt b ∗ reduceTableAt b ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
  | [], _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    absurd rfl hne
  | _ :: _, [], _, _, _, _, hlen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp at hlen
  | pt :: ptsTail, poly :: polysTail, i, n, acc, _, hlen_eq, hn_pos, hn, halen, hplen, hin,
    s0, s, fsp, accPtr, basisPtr, ptVecPtr, v27, u112, u120, u128, u136,
    hfsp_align, Frame, R, hpc, hrun, hsp, htrace,
    hx21, hx24, hx25, hx26, hx27, hx28, hx29, hcont => by
    have hpoly_len : poly.coefficients.length = n := hplen poly (List.mem_cons_self ..)
    have htail_len : ∀ p ∈ polysTail, p.coefficients.length = n :=
      fun p hp => hplen p (List.mem_cons_of_mem poly hp)
    have him : (i + 1) + ptsTail.length = n := by simp at hin; omega
    have hbasis_add : (basisPtr + BitVec.ofNat 64 (24 * i)) + 24#64 =
        basisPtr + BitVec.ofNat 64 (24 * (i + 1)) := by
      rw [show 24 * (i + 1) = 24 * i + 24 by omega, BitVec.ofNat_add]; bv_omega
    have hpt_add : (ptVecPtr + BitVec.ofNat 64 (4 * i)) + 4#64 =
        ptVecPtr + BitVec.ofNat 64 (4 * (i + 1)) := by
      rw [show 4 * (i + 1) = 4 * i + 4 by omega, BitVec.ofNat_add]; bv_omega
    have hpoly_cons :
        polyListOf A (basisPtr + BitVec.ofNat 64 (24 * i)) (poly :: polysTail) =
        (polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
         polyListOf A (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) polysTail) := by
      rw [polyListOf_cons_fbl, hbasis_add]
    have hpt_cons :
        ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * i)) (pt :: ptsTail) =
        (ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
         ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * (i + 1))) ptsTail) := by
      simp only [ptSliceAt, arrayAt, ptStride, BitVec.ofNat_eq_ofNat, hpt_add]
    rw [hpoly_cons, hpt_cons]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (lagrangeSumStepNext_sepWPp hA hb i ptsTail.length n acc pt poly
        hn_pos hn halen hpoly_len him s0 s fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136
        hfsp_align
        (polyListOf A (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) polysTail ∗
         ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * (i + 1))) ptsTail ∗ Frame) R
        hpc hrun hsp htrace hx21 hx24 hx25 hx26 hx27 hx28 hx29 ?_)
    intro s1 u112' u136' hpc1 hrun1 hsp1 htr1 hvregs1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    cases ptsTail with
    | nil =>
      cases polysTail with
      | nil =>
        simp only [List.length_nil, ↓reduceIte] at hpc1
        simp only [lagrangeSumFoldPoly_cons, lagrangeSumFoldPoly_nil_left] at hcont
        refine SepWPp.weaken_pre
          (by rw [hpoly_cons, hpt_cons]; exact Entails.of_eq (by ac_rfl))
          (hcont s1 u112' (BitVec.ofNat 64 i) (BitVec.ofNat 64 (2 * n)) u136'
            hpc1 hrun1 hsp1 htr1 hvregs1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1)
      | cons _ _ => simp at hlen_eq
    | cons pt2 ptsTail' =>
      cases polysTail with
      | nil => simp at hlen_eq
      | cons poly2 polysTail' =>
        have hne' : pt2 :: ptsTail' ≠ [] := List.cons_ne_nil _ _
        have hlen_eq' : (pt2 :: ptsTail').length = (poly2 :: polysTail').length := by
          simp at hlen_eq ⊢; omega
        have halen' : (Poly.addAssign acc (poly.multAssign pt.y)).coefficients.length = n := by
          unfold Poly.addAssign
          rw [addAssignCoeffs_length_eq (by rw [halen, multAssign_length, hpoly_len]), halen]
        simp only [List.length_cons, Nat.succ_ne_zero, ↓reduceIte] at hpc1
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (lagrangeSumTailLoop_sepWPp hA hb (pt2 :: ptsTail') (poly2 :: polysTail') (i + 1) n
            (Poly.addAssign acc (poly.multAssign pt.y))
            hne' hlen_eq' hn_pos hn halen' htail_len him
            s0 s1 fsp accPtr basisPtr ptVecPtr v27 u112' (BitVec.ofNat 64 i)
            (BitVec.ofNat 64 (2 * n)) u136' hfsp_align
            (polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
             ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗ Frame) R
            hpc1 hrun1 hsp1 htr1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 ?_)
        intro s2 u112'' u120'' u128'' u136'' hpc2 hrun2 hsp2 htr2 hvregs2
          hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
        simp only [lagrangeSumFoldPoly_cons] at hcont
        refine SepWPp.weaken_pre
          (by rw [hpoly_cons, hpt_cons]; exact Entails.of_eq (by ac_rfl))
          (hcont s2 u112'' u120'' u128'' u136''
            hpc2 hrun2 hsp2 htr2 (hvregs2.trans hvregs1) hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2)

/-- Full `Poly::lagrange_sum` loop from `+2608` (`0x6adb4`) to `+3908` (`0x6b2c8`). -/
theorem lagrangeSumLoop_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (pts : List Pt) (polys : List Poly) (n : Nat)
    (hpts_ne : pts ≠ []) (hpts_len : pts.length = n) (hpolys_len : polys.length = n)
    (hn : n ≤ 0x0555555555555555)
    (hplen : ∀ p ∈ polys, p.coefficients.length = n)
    (s0 s : State) (fsp accPtr basisPtr ptVecPtr cIdx v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u16 u64 u72 u80 u112 u120 u128 u136 u656 u664 u672 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = accPtr)
    (hx20 : s.readReg64 .x20 = cIdx)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 u112' u120' u128' u136',
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3908#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         gf16SliceAt accPtr (Poly.lagrangeSum pts polys).coefficients ∗
         polyListOf A basisPtr polys ∗
         ptSliceAt ptVecPtr pts ∗
         ((fsp + 16#64) ↦₆₄ cIdx) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ u120') ∗
         ((fsp + 128#64) ↦₆₄ u128') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
         shiftSlotsRawAt fsp ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         tokenInitAt b ∗ reduceTableAt b ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       memRegion accPtr (2 * n) ∗
       polyListOf A basisPtr polys ∗
       ptSliceAt ptVecPtr pts ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt fsp ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗ ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗
       tokenInitAt b ∗ reduceTableAt b ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  rcases pts with _ | ⟨pt0, ptsTail⟩
  · contradiction
  · rcases polys with _ | ⟨poly0, polysTail⟩
    · simp at hpts_len hpolys_len; omega
    · have hn_pos : 0 < n := by simp at hpts_len; omega
      have h1m : 1 + ptsTail.length = n := by simp at hpts_len; omega
      have hpoly0_len : poly0.coefficients.length = n := hplen poly0 (List.mem_cons_self ..)
      have htail_len : ∀ p ∈ polysTail, p.coefficients.length = n :=
        fun p hp => hplen p (List.mem_cons_of_mem poly0 hp)
      have hb0 : basisPtr + BitVec.ofNat 64 (24 * 0) = basisPtr := by bv_omega
      have hp0 : ptVecPtr + BitVec.ofNat 64 (4 * 0) = ptVecPtr := by bv_omega
      have hpoly_cons0 :
          polyListOf A basisPtr (poly0 :: polysTail) =
          (polyOf A (basisPtr + BitVec.ofNat 64 (24 * 0)) poly0 ∗
           polyListOf A (basisPtr + BitVec.ofNat 64 (24 * 1)) polysTail) := by
        rw [polyListOf_cons_fbl, hb0]
      have hpt_cons0 :
          ptSliceAt ptVecPtr (pt0 :: ptsTail) =
          (ptAt pt0 (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
           ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * 1)) ptsTail) := by
        unfold ptSliceAt; rw [arrayAt_cons, hp0]
      apply SepWPp.of_sepWP
        (mid := (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2668#64)
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (lagrangeSumSetup_sepWP n s fsp accPtr basisPtr ptVecPtr cIdx v27 hfsp_align
          u16 u64 u72 u80 u656 u664 u672
          (A.pool ∗ memRegion accPtr (2 * n) ∗
           polyListOf A basisPtr (poly0 :: polysTail) ∗
           ptSliceAt ptVecPtr (pt0 :: ptsTail) ∗
           ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
           ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
           shiftSlotsRawAt fsp ∗ tokenInitAt b ∗ reduceTableAt b ∗
           stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx0 hx20 hx24 hx25 hx26 hx27 hx28 hx29 ?_)
      intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWP.done hpc1 hrun1
      rw [hpoly_cons0, hpt_cons0]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (lagrangeSumStepFirst_sepWPp hA hb ptsTail.length n pt0 poly0
          hn_pos hn hpoly0_len h1m s0 s1 fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136
          hfsp_align
          (polyListOf A (basisPtr + BitVec.ofNat 64 (24 * 1)) polysTail ∗
           ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * 1)) ptsTail ∗
           ((fsp + 16#64) ↦₆₄ cIdx) ∗ Frame) R
          hpc1 hrun1 hsp1 (by rw [htr1, htrace])
          hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 ?_)
      intro s2 u112' u136' hpc2 hrun2 hsp2 htr2 hvregs2 hx21_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
      cases ptsTail with
      | nil =>
        cases polysTail with
        | nil =>
          simp only [List.length_nil, ↓reduceIte] at hpc2
          have hsum_eq : Poly.lagrangeSum [pt0] [poly0] = Poly.addAssign Poly.zero (poly0.multAssign pt0.y) := by
            rw [lagrangeSum_eq_foldPoly]; rfl
          rw [← hsum_eq]
          refine SepWPp.weaken_pre
            (by rw [hpoly_cons0, hpt_cons0]; exact Entails.of_eq (by ac_rfl))
            (hcont s2 u112' (BitVec.ofNat 64 0) (BitVec.ofNat 64 (2 * n)) u136'
              hpc2 hrun2 hsp2 htr2 (hvregs2.trans hvregs1) hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2)
        | cons _ _ => simp at hpts_len hpolys_len; omega
      | cons pt1 ptsTail' =>
        cases polysTail with
        | nil => simp at hpts_len hpolys_len; omega
        | cons poly1 polysTail' =>
          have hne' : pt1 :: ptsTail' ≠ [] := List.cons_ne_nil _ _
          have hlen_eq' : (pt1 :: ptsTail').length = (poly1 :: polysTail').length := by
            simp at hpts_len hpolys_len ⊢; omega
          have halen' : (Poly.addAssign Poly.zero (poly0.multAssign pt0.y)).coefficients.length = n := by
            unfold Poly.addAssign Poly.zero
            rw [addAssignCoeffs_nil_left, multAssign_length, hpoly0_len]
          simp only [List.length_cons, Nat.succ_ne_zero, ↓reduceIte] at hpc2
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (lagrangeSumTailLoop_sepWPp hA hb (pt1 :: ptsTail') (poly1 :: polysTail') 1 n
              (Poly.addAssign Poly.zero (poly0.multAssign pt0.y))
              hne' hlen_eq' hn_pos hn halen' htail_len h1m
              s0 s2 fsp accPtr basisPtr ptVecPtr v27 u112' (BitVec.ofNat 64 0)
              (BitVec.ofNat 64 (2 * n)) u136' hfsp_align
              (polyOf A (basisPtr + BitVec.ofNat 64 (24 * 0)) poly0 ∗
               ptAt pt0 (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
               ((fsp + 16#64) ↦₆₄ cIdx) ∗ Frame) R
              hpc2 hrun2 hsp2 htr2 hx21_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 ?_)
          intro s3 u112'' u120'' u128'' u136'' hpc3 hrun3 hsp3 htr3 hvregs3
            hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
          have hsum_eq : Poly.lagrangeSum (pt0 :: pt1 :: ptsTail') (poly0 :: poly1 :: polysTail') =
              lagrangeSumFoldPoly (Poly.addAssign Poly.zero (poly0.multAssign pt0.y))
                (pt1 :: ptsTail') (poly1 :: polysTail') := by
            rw [lagrangeSum_eq_foldPoly, lagrangeSumFoldPoly_cons]
          rw [← hsum_eq]
          refine SepWPp.weaken_pre
            (by rw [hpoly_cons0, hpt_cons0]; exact Entails.of_eq (by ac_rfl))
            (hcont s3 u112'' u120'' u128'' u136''
              hpc3 hrun3 hsp3 htr3 (hvregs3.trans (hvregs2.trans hvregs1))
              hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3)

/-! ## 2. Deallocating `polys: Vec<Poly>` and Exiting `Poly::lagrange_sum` (`0x6b2c8..0x6b328`, `+3908 -> +4004`) -/

@[local arm64_norm, local wp_norm]
theorem sub1_ofNat_sum (m : Nat) :
    BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := by
  have h : BitVec.ofNat 64 (m + 1) = BitVec.ofNat 64 m + 1#64 := by
    rw [BitVec.ofNat_add]
  rw [h]; bv_omega

@[local arm64_norm, local wp_norm]
theorem sub1_ofNat_sum_add (m : Nat) :
    BitVec.ofNat 64 (m + 1) + 18446744073709551615#64 = BitVec.ofNat 64 m := by
  have h1 : (18446744073709551615#64 : BitVec 64) = -1#64 := rfl
  have h2 : BitVec.ofNat 64 (m + 1) = BitVec.ofNat 64 m + 1#64 := by
    rw [BitVec.ofNat_add]
  rw [h1, h2]; bv_omega

theorem beq_m1_one_sum {m : Nat} (hm : m ≤ 0x0555555555555555) :
    (BitVec.ofNat 64 (m + 1) == 1#64) = decide (m = 0) := by
  by_cases h : m = 0
  · subst h; rfl
  · rw [decide_eq_false_iff_not.mpr h, beq_eq_false_iff_ne]; intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    change m + 1 = 1 at hto; omega

@[local arm64_norm, local wp_norm]
theorem mul24_ofNat_sum (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (24 * n) := by
  have h1 : (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1#64)) <<< 3#64 =
      24#64 * BitVec.ofNat 64 n := by bv_bits
  have h2 : BitVec.ofNat 64 (24 * n) = 24#64 * BitVec.ofNat 64 n := by
    rw [BitVec.ofNat_mul]
  rw [h1, h2]

@[local arm64_norm, local wp_norm]
theorem mul24_ofNat_sum_nat (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 3 = BitVec.ofNat 64 (24 * n) :=
  mul24_ofNat_sum n

/-- Element-by-element deallocation loop (`0x6b2f0 -> 0x6b2e4..0x6b308`, `+3948 -> +3976`)
    over `polyListOf A base polysRest`. -/
theorem basisElemDeallocLoop_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContracts b A ext) :
    ∀ (polysRest : List Poly) (n : Nat)
      (hrest_ne : polysRest ≠ [])
      (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
      (hrest_bound : polysRest.length ≤ n)
      (hplen : ∀ p ∈ polysRest, p.coefficients.length = n)
      (s : State) (fsp base : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
      (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3948#64)
      (hrun : s.status = .Running) (hsp : s.sp = fsp)
      (hx20 : s.readReg64 .x20 = base + 8#64)
      (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 polysRest.length)
      (hcont : ∀ s1 : State,
        s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3976#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x19 = s.readReg64 .x19 →
        s1.readReg64 .x24 = s.readReg64 .x24 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = s.readReg64 .x27 →
        s1.readReg64 .x28 = s.readReg64 .x28 →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
          (A.pool ∗
           memRegion base (24 * polysRest.length) ∗
           stackAt fsp allocHookStack ∗ Frame) post),
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
        (A.pool ∗
         polyListOf A base polysRest ∗
         stackAt fsp allocHookStack ∗ Frame) post
  | [], _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | p :: pTail, n, _, hn_pos, hn, hrest_bound, hplen, s, fsp, base, hfsp_align, Frame,
    hpc, hrun, hsp, hx20, hx25, hcont => by
    have hp_len : p.coefficients.length = n := hplen p (List.mem_cons_self ..)
    have htail_len : ∀ q ∈ pTail, q.coefficients.length = n :=
      fun q hq => hplen q (List.mem_cons_of_mem p hq)
    have hdealloc := hA.dealloc_ok_at polyNextChunkName
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
      (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_dealloc")])
    simp only [rustDeallocSpec] at hdealloc
    have hsub1 := sub1_ofNat_sum pTail.length
    have hsub1_add := sub1_ofNat_sum_add pTail.length
    have hbeq1 := beq_m1_one_sum (m := pTail.length) (by simp at hrest_bound; omega)
    rw [polyListOf_cons_fbl]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
        (polyOf_entails_dealloc_sum A base p n hn_pos hp_len)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
    apply SepWP.exists_elim; intro cap
    apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; rintro ⟨hcap_lt, hptr, hcap⟩
    have hcap_bne : ¬(cap == 0#64) = true := by simpa [beq_iff_eq] using hcap
    have hcap_shl := shl_one_cap_toNat_nat hcap_lt
    rw [← hcap_shl]
    rw [show (p :: pTail).length = pTail.length + 1 by simp] at hx25
    poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xf60 44
    dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
    generalize_entry hentry :
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
    examples_hide_fetches
    wp_steps; wp_apply; wp_steps
    subst hentry
    have hsp_sf : sf.sp = fsp := by rw [‹sf.sp = _›]; simp only [wp_norm, hsp]
    rw [hsp]
    have hhdr24 := polyHeader_entails_memRegion24 base cap ptr (BitVec.ofNat 64 n)
    cases pTail with
    | nil =>
      have h24_1 : 24 * [p].length = 24 := rfl
      rw [h24_1] at hcont
      simp only [polyListOf, arrayAt, sepConj_emp]
      refine SepWP.weaken_pre ?_
        (hcont _ (by simp only [wp_norm, h_6, hx25, hbeq1, List.length_nil, decide_true, ↓reduceIte])
          (by wp_norm_lhs) (by simp only [wp_norm, hsp_sf])
          (by simp only [arm64_norm, wp_norm]; exact hpost)
          (by simp only [arm64_norm, wp_norm]; exact hvregs)
          (by simp only [wp_norm, h])
          (by simp only [wp_norm, h_5])
          (by simp only [wp_norm, h_7])
          (by simp only [wp_norm, h_8])
          (by simp only [wp_norm, h_9])
          (by simp only [wp_norm, hcs_sf]))
      refine Entails.trans (Entails.of_eq (show _ =
        ((base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗ ((base + 16#64) ↦₆₄ BitVec.ofNat 64 n)) ∗
        (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hhdr24) ?_
      exact Entails.of_eq (by ac_rfl)
    | cons p2 pTail' =>
      have hne' : p2 :: pTail' ≠ [] := List.cons_ne_nil _ _
      have hbound' : (p2 :: pTail').length ≤ n := by simp at hrest_bound ⊢; omega
      have hbase20 : base + 8#64 + 24#64 = (base + 24#64) + 8#64 := by bv_omega
      refine SepWP.weaken_pre ?_
        (basisElemDeallocLoop_sepWP hA (p2 :: pTail') n hne' hn_pos hn hbound' htail_len
          _ fsp (base + 24#64) hfsp_align
          (memRegion base 24 ∗ Frame)
          (by simp only [wp_norm, h_6, hx25, hbeq1, List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
          (by wp_norm_lhs) (by simp only [wp_norm, hsp_sf])
          (by simp only [wp_norm, h_1, hx20, hbase20])
          (by simp only [wp_norm, h_6, hx25, hsub1, hsub1_add]) ?_)
      · refine Entails.trans (Entails.of_eq (show _ =
          ((base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗ ((base + 16#64) ↦₆₄ BitVec.ofNat 64 n)) ∗
          (A.pool ∗ polyListOf A (base + 24#64) (p2 :: pTail') ∗
           stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hhdr24) ?_
        exact Entails.of_eq (by ac_rfl)
      · intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx24_1 hx26_1 hx27_1 hx28_1 hx29_1
        have hjoin :
            memRegion base 24 ∗ memRegion (base + 24#64) (24 * (p2 :: pTail').length) =
            memRegion base (24 * (p :: p2 :: pTail').length) := by
          have hm : 24 * (p :: p2 :: pTail').length = 24 + 24 * (p2 :: pTail').length := by
            simp [Nat.mul_add]; omega
          rw [hm, ProofLib.memRegion_split' (b := base) (n := 24) (k := 24 * (p2 :: pTail').length)
            (b' := base + 24#64) rfl (by bv_omega) (by simp at hrest_bound; omega)]
        refine SepWP.weaken_pre
          (by rw [← hjoin]; exact Entails.of_eq (by ac_rfl))
          (hcont s1 hpc1 hrun1 hsp1
            (by rw [htr1]; simp only [arm64_norm, wp_norm]; exact hpost)
            (by rw [hvregs1]; simp only [arm64_norm, wp_norm]; exact hvregs)
            (by rw [hx19_1]; simp only [wp_norm, h])
            (by rw [hx24_1]; simp only [wp_norm, h_5])
            (by rw [hx26_1]; simp only [wp_norm, h_7])
            (by rw [hx27_1]; simp only [wp_norm, h_8])
            (by rw [hx28_1]; simp only [wp_norm, h_9])
            (by rw [hx29_1]; simp only [wp_norm, hcs_sf]))

/-- Cleanup block of `Poly::lagrange_sum` (`0x6b2c8..0x6b328`, `+3908 -> +4004`):
    copies `[fsp + 664..680]` (`accPtr, n`) to `[fsp + 640..656]`, deallocates each element of
    `basisVecAt A basisPtr polys`, and deallocates `basisPtr` (`24 * n` bytes, align `8`). -/
theorem lagrangeSumCleanup_sepWP {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (polys : List Poly) (n : Nat)
    (hpolys_ne : polys ≠ []) (hpolys_len : polys.length = n)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (hplen : ∀ p ∈ polys, p.coefficients.length = n)
    (s : State) (fsp accPtr basisPtr ptVecPtr cIdx v27 u640 u648 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 3908#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 : State,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4004#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 n →
      s1.readReg64 .x20 = cIdx →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
         ((fsp + 16#64) ↦₆₄ cIdx) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 640#64) ↦₆₄ accPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
       basisVecAt A basisPtr polys ∗
       ((fsp + 16#64) ↦₆₄ cIdx) ∗
       ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗
       ((fsp + 648#64) ↦₆₄ u648) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hdealloc := hA.dealloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_dealloc")])
  simp only [rustDeallocSpec] at hdealloc
  obtain ⟨hn_ne0, _⟩ := ofNat_pos_ne_zero hn_pos hn
  have hn_bne0 : ¬(BitVec.ofNat 64 n == 0#64) = true := by simpa [beq_iff_eq] using hn_ne0
  have h24n_toNat : (BitVec.ofNat 64 (24 * n)).toNat = 24 * n := Nat.mod_eq_of_lt (by omega)
  unfold basisVecAt
  simp only [sepConj_pure_left_comm, hpolys_len, sepConj_assoc]
  apply SepWP.pure_elim; intro hbasis_ne
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xf44 28
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xf88 28
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (basisElemDeallocLoop_sepWP hA polys n hpolys_ne hn_pos hn (by omega) hplen
      _ fsp basisPtr hfsp_align
      (A.live basisPtr (24 * n) 8 ∗
       ((fsp + 16#64) ↦₆₄ cIdx) ∗
       ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 640#64) ↦₆₄ accPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame)
      (by subst hentry; wp_norm_goal) (by wp_norm_lhs) (by simp only [wp_norm, hsp])
      (by simp only [wp_norm, hx24])
      (by simp only [wp_norm, hx25, hpolys_len]) ?_)
  intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx24_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [hpolys_len, ← h24n_toNat]
  rw [hentry] at hpc1
  wp_steps; wp_apply
  subst hentry
  have hsp_sf : sf.sp = fsp := by rw [‹sf.sp = _›]; simp only [wp_norm, hsp1]
  rw [hsp1]
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont sf hpc_sf hrun_sf hsp_sf
      (by rw [hpost, htr1]; simp only [arm64_norm, wp_norm])
      (by rw [hvregs, hvregs1]; simp only [arm64_norm, wp_norm])
      (by rw [h, hx19_1]; wp_norm_lhs)
      (by rw [h_1])
      (by rw [h_7, hx26_1]; simp only [wp_norm, hx26])
      (by rw [h_8, hx27_1]; simp only [wp_norm, hx27])
      (by rw [h_9, hx28_1]; simp only [wp_norm, hx28])
      (by rw [hcs_sf, hx29_1]; simp only [wp_norm, hx29]))

/-- Combined `Poly::lagrange_sum` + `polys` deallocation (`0x6adb4..0x6b328`, `+2608 -> +4004`)
    for `pts ≠ []`. Matches the continuation of `basis_pos_sepWPp`. -/
theorem lagrangeSumAndFree_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (fsp accPtr basisPtr ptVecPtr cIdx v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u16 u64 u72 u80 u640 u648 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = accPtr)
    (hx20 : s.readReg64 .x20 = cIdx)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 u656' u664' u672',
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4004#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x20 = cIdx →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         ptSliceAt ptVecPtr pts ∗
         A.live accPtr (2 * pts.length) 2 ∗
         gf16SliceAt accPtr (Poly.lagrangeSum pts (completePointsBasisPure pts)).coefficients ∗
         ((fsp + 16#64) ↦₆₄ cIdx) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ accPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 656#64) ↦₆₄ u656') ∗
         ((fsp + 664#64) ↦₆₄ u664') ∗
         ((fsp + 672#64) ↦₆₄ u672') ∗
         tokenInitAt b ∗ reduceTableAt b ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ptSliceAt ptVecPtr pts ∗
       basisVecAt A basisPtr (completePointsBasisPure pts) ∗
       A.live accPtr (2 * pts.length) 2 ∗
       memRegion accPtr (2 * pts.length) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗
       ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗
       ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       tokenInitAt b ∗ reduceTableAt b ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_pos : 0 < pts.length := List.length_pos_iff.mpr hpts_ne
  have hpolys_len : (completePointsBasisPure pts).length = pts.length :=
    completePointsBasisPure_length pts
  have hpolys_ne : completePointsBasisPure pts ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have hplen : ∀ p ∈ completePointsBasisPure pts, p.coefficients.length = pts.length :=
    completePointsBasisPure_mem_length pts
  unfold basisVecAt
  rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 112#64) 120 ∗
      (A.pool ∗ ptSliceAt ptVecPtr pts ∗
       (⌜basisPtr ≠ 0#64⌝ ∗ A.live basisPtr (24 * (completePointsBasisPure pts).length) 8 ∗
        polyListOf A basisPtr (completePointsBasisPure pts)) ∗
       A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       (∃∗ u16' : BitVec 64, ∃∗ u8' : BitVec 64, ∃∗ u0' : BitVec 64,
         ((fsp + 656#64) ↦₆₄ u0') ∗ ((fsp + 664#64) ↦₆₄ u8') ∗ ((fsp + 672#64) ↦₆₄ u16')) ∗
       tokenInitAt b ∗ reduceTableAt b ∗
       (stackAt fsp allocHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
          (lagrangePrepareStack - allocHookStack)) ∗ Frame) by ac_rfl))
      (sepConj_mono_left (memRegion_112_split_sum fsp))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  apply SepWPp.exists_elim; intro u672
  apply SepWPp.exists_elim; intro u664
  apply SepWPp.exists_elim; intro u656
  apply SepWPp.exists_elim; intro u112
  apply SepWPp.exists_elim; intro u120
  apply SepWPp.exists_elim; intro u128
  apply SepWPp.exists_elim; intro u136
  apply SepWPp.pure_left; intro hbasis_ne
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeSumLoop_sepWPp hA hb pts (completePointsBasisPure pts) pts.length
      hpts_ne rfl hpolys_len hbound hplen
      s0 s fsp accPtr basisPtr ptVecPtr cIdx v27 hfsp_align
      u16 u64 u72 u80 u112 u120 u128 u136 u656 u664 u672
      (A.live basisPtr (24 * (completePointsBasisPure pts).length) 8 ∗
       A.live accPtr (2 * pts.length) 2 ∗
       ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       shiftTablePadAt fsp ∗
       memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗ Frame) R
      hpc hrun hsp htrace hx0 hx20 hx24 hx25 hx26 hx27 hx28 hx29 ?_)
  intro s1 u112' u120' u128' u136' hpc1 hrun1 hsp1 htr1 hvregs1
    hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply SepWPp.of_sepWP
    (mid := (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4004#64)
  refine SepWP.weaken_pre ?_
    (lagrangeSumCleanup_sepWP hA (completePointsBasisPure pts) pts.length
      hpolys_ne hpolys_len hn_pos hbound hplen
      s1 fsp accPtr basisPtr ptVecPtr cIdx v27 u640 u648 hfsp_align
      (gf16SliceAt accPtr (Poly.lagrangeSum pts (completePointsBasisPure pts)).coefficients ∗
       ptSliceAt ptVecPtr pts ∗
       A.live accPtr (2 * pts.length) 2 ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ u120') ∗
       ((fsp + 128#64) ↦₆₄ u128') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt fsp ∗ shiftTablePadAt fsp ∗
       tokenInitAt b ∗ reduceTableAt b ∗
       memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗ Frame)
      hpc1 hrun1 hsp1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 ?_)
  · unfold basisVecAt
    simp only [← sepConj_assoc, sepConj_pure_left_comm, sepConj_assoc]
    exact Entails.pure_right hbasis_ne (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx26_2 hx27_2 hx28_2 hx29_2
    apply SepWP.done hpc2 hrun2
    refine SepWPp.weaken_pre ?_
      (hcont s2 (BitVec.ofNat 64 pts.length) accPtr (BitVec.ofNat 64 pts.length)
        hpc2 hrun2 hsp2 (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1])
        hx19_2 hx20_2 hx26_2 hx27_2 hx28_2 hx29_2)
    rw [stackAt_lagrangePrepare_split_alloc fsp]
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ u120') ∗
       ((fsp + 128#64) ↦₆₄ u128') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt fsp ∗ shiftTablePadAt fsp) ∗
      (A.pool ∗ ptSliceAt ptVecPtr pts ∗
       A.live accPtr (2 * pts.length) 2 ∗
       gf16SliceAt accPtr (Poly.lagrangeSum pts (completePointsBasisPure pts)).coefficients ∗
       ((fsp + 16#64) ↦₆₄ cIdx) ∗ ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 640#64) ↦₆₄ accPtr) ∗ ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       tokenInitAt b ∗ reduceTableAt b ∗
       (stackAt fsp allocHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
          (lagrangePrepareStack - allocHookStack)) ∗ Frame) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (memRegion_112_fold_sum fsp u112' u120' u128' u136')) ?_
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.NextChunk
