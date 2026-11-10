/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProof
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed `lagrange_sum` Specialization and Cleanup

Specializes `lagrangeSumAndFree_gen_placed_sepWPp` (`+2608 -> +4004`) to `completePointsBasisPure`
and verifies per-iteration slot cleanup (`+4004 -> +976 / +4424`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_p2p_pl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm] add_8_add_8_eq

/-! ## 1. Specialization of `lagrangeSumAndFree_gen_placed_sepWPp` to `completePointsBasisPure` -/

/-- Combined `Poly::lagrange_sum` + `polys` deallocation (`+2608 -> +4004`) specialized to
    `completePointsBasisPure pts`. -/
theorem lagrangeSumAndFree_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp accPtr basisPtr ptVecPtr cIdx v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u16 u64 u72 u80 u640 u648 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2608#64)
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
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 4004#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x20 = cIdx →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
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
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
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
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeSumAndFree_gen_placed_sepWPp hA pts (completePointsBasisPure pts)
      hpts_ne hbound
      (completePointsBasisPure_length pts)
      (completePointsBasisPure_mem_length pts)
      s0 s hcl fsp accPtr basisPtr ptVecPtr cIdx v27 hfsp_align
      u16 u64 u72 u80 u640 u648 Frame R
      hpc hrun hsp htrace hx0 hx20 hx24 hx25 hx26 hx27 hx28 hx29 ?_)
  intro s1 u656' u664' u672' hcl1 hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx26_1 hx27_1 hx28_1 hx29_1
  exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s1 u656' u664' u672' hcl1 hpc1 hrun1 hsp1 htr1 hvregs1
      hx19_1 hx20_1 hx26_1 hx27_1 hx28_1 hx29_1)

/-! ## 2. Per-Iteration Cleanup (`+4004 -> +976 / +4424`, Block `416`) -/

/-- Sub-block 1 (`+4004 -> +4048`):
    checks `x19 + 1 != 0`, computes `slot = (fsp + 256) + 24 * j`, and deallocates the old
    `Poly` buffer in `slot` if `oldCap != 0`. -/
theorem deallocOldPolySlot_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j n : Nat) (hn : n ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4004#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 n)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ s1 oldCap oldPtr,
      s1.pc = (blkPl_416).base + 4048#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 n →
      s1.readReg64 .x20 = (fsp + 256#64) + BitVec.ofNat 64 (24 * j) →
      s1.readReg64 .x21 = ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool ∗
         (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool ∗
       polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hdealloc := hA.dealloc_ok
  simp only [rustDeallocSpec, BitVec.ofNat_eq_ofNat] at hdealloc
  have hcmn := cmn_one_ne_zero hn
  have hmul24 : BitVec.ofNat 64 j * 24#64 = BitVec.ofNat 64 (24 * j) := by bv_omega
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (polyOf_empty_unfold A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro oldCap
  apply SepWP.exists_elim; intro oldPtr
  have hpull :
      A.pool ∗
      (⌜oldCap.toNat * 2 < 2 ^ 63 ∧ oldPtr ≠ 0#64⌝ ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       (if oldCap = 0#64 then emp else A.live oldPtr (oldCap.toNat * 2) 2 ∗ memRegion oldPtr (oldCap.toNat * 2))) ∗
      stackAt fsp allocHookStack ∗ Frame =
      ⌜oldCap.toNat * 2 < 2 ^ 63 ∧ oldPtr ≠ 0#64⌝ ∗
      (A.pool ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       (if oldCap = 0#64 then emp else A.live oldPtr (oldCap.toNat * 2) 2 ∗ memRegion oldPtr (oldCap.toNat * 2)) ∗
       stackAt fsp allocHookStack ∗ Frame) := by
    ac_rfl
  rw [hpull]
  apply SepWP.pure_elim; rintro ⟨holdCap_lt, holdPtr_ne⟩
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  by_cases hcap0 : oldCap = 0#64
  · subst hcap0
    simp only [↓reduceIte, sepConj_emp]
    wp_steps 7
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ 0#64 oldPtr
        (by simp only [arm64_norm, wp_norm, hx19, hcmn])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx19])
        (by simp only [arm64_norm, wp_norm, hsp, hx20, hx28, hmul24])
        (by simp only [arm64_norm, wp_norm, hsp, hx20, hx28, hmul24])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx28])
        (by simp only [arm64_norm, wp_norm]))
  · have hcap_beq : (oldCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hcap_bne : ¬(oldCap == 0#64) = true := by simp [hcap_beq]
    obtain ⟨hshl_nat, hshl_bv, hshl_toNat⟩ := shl1_oldCap_eq holdCap_lt
    simp only [hcap0, ↓reduceIte]
    rw [← hshl_toNat]
    wp_steps 11; wp_call hdealloc
    have hsp_sf : sf.sp = fsp := by rw [‹sf.sp = _›]; simp only [arm64_norm, wp_norm, hsp]
    rw [hsp]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont sf oldCap oldPtr hpc_sf hrun_sf hsp_sf
        (by rw [hpost])
        (by rw [hvregs])
        (by rw [h]; simp only [arm64_norm, wp_norm, hx19])
        (by rw [h_1])
        (by rw [h_2])
        (by rw [h_7])
        (by rw [h_8])
        (by rw [h_9]; simp only [arm64_norm, wp_norm, hx28])
        (by rw [hcs_sf]))

/-- Sub-block 2 (`+4048 -> +4088`):
    writes the new `Poly` header `(n, newPtr, n)` into `slot = (fsp + 256) + 24 * j`,
    folds `polyOf A slot (pointToPolyPure pt)`, and deallocates `ptVecBufAt A ptVecPtr pt.value`. -/
theorem storeNewPolyAndFreePtVec_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s : State) (fsp oldCap oldPtr newPtr ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (pt : Point) (hbound : pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4048#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 pt.value.length)
    (hx20 : s.readReg64 .x20 = (fsp + 256#64) + BitVec.ofNat 64 (24 * j))
    (hx21 : s.readReg64 .x21 = ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ s1,
      s1.pc = (blkPl_416).base + 4088#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       newPolyBufAt A newPtr pt ∗
       ptVecBufAt A ptVecPtr pt.value ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hdealloc := hA.dealloc_ok
  simp only [rustDeallocSpec, BitVec.ofNat_eq_ofNat] at hdealloc
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  by_cases hn0 : pt.value.length = 0
  · have hpoly0 := polyOf_of_newPolyBufAt A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) newPtr pt hbound
    simp only [hn0, BitVec.ofNat_eq_ofNat] at hpoly0
    wp_steps 6
    apply SepWP.fold hpoly0 (by sep_frame)
    simp only [hn0, BitVec.ofNat_eq_ofNat] at hcont ⊢
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        ptVecBufAt A ptVecPtr pt.value ∗
        (A.pool ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 40#64) ↦₆₄ 0#64) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ 0#64) ∗
         stackAt fsp allocHookStack ∗ Frame) by ac_rfl))
        (ptVecBufAt_zero_drop A ptVecPtr pt.value hn0 _))
      (hcont _
        (by simp only [arm64_norm, wp_norm, hn0])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx28])
        (by simp only [arm64_norm, wp_norm]))
  · have hn_pos : 0 < pt.value.length := by omega
    obtain ⟨hn_beq, hn_bne⟩ := ofNat_pos_ne_zero hn_pos hbound
    obtain ⟨hshl2_nat, hshl2_bv, hshl2_toNat⟩ := shl2_len_eq hbound
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (ptVecBufAt_pos_entails A ptVecPtr pt.value hn_pos hbound))))))) ?_
    have hpull :
        A.pool ∗
        (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
        ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
        ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
        newPolyBufAt A newPtr pt ∗
        (⌜ptVecPtr ≠ 0#64⌝ ∗ A.live ptVecPtr (4 * pt.value.length) 2 ∗ memRegion ptVecPtr (4 * pt.value.length)) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ((fsp + 640#64) ↦₆₄ newPtr) ∗
        ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        stackAt fsp allocHookStack ∗ Frame =
        ⌜ptVecPtr ≠ 0#64⌝ ∗
        (A.pool ∗
         (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
         newPolyBufAt A newPtr pt ∗
         A.live ptVecPtr (4 * pt.value.length) 2 ∗ memRegion ptVecPtr (4 * pt.value.length) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) := by
      ac_rfl
    rw [hpull]
    apply SepWP.pure_elim; intro hptVec_ne
    rw [← hshl2_toNat]
    wp_steps 10; wp_call hdealloc
    have hsp_sf : sf.sp = fsp := by rw [‹sf.sp = _›]; simp only [arm64_norm, wp_norm, hsp]
    rw [hsp]
    apply SepWP.fold (polyOf_of_newPolyBufAt A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) newPtr pt hbound)
      (by sep_frame)
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont sf hpc_sf hrun_sf hsp_sf
        (by rw [hpost])
        (by rw [hvregs])
        (by rw [h_8])
        (by rw [h_9]; simp only [arm64_norm, wp_norm, hx28])
        (by rw [hcs_sf]))

/-- Full per-iteration cleanup (`+4004 -> +976 / +4424`):
    deallocates the dummy `Poly` buffer in `slot j`, writes the newly constructed `Poly` into `slot j`,
    deallocates `ptVecBufAt`, reloads `x20 = j + 1` and `x19 = ptsBase`, and branches to
    `+976` (`j < 15`) or `+4424` (`j = 15`). -/
theorem cleanupIter_placed_sepWP [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (s : State) (fsp ptsBase newPtr ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (hj : j < 16)
    (pt : Point) (hbound : pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4004#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 pt.value.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ s1,
      s1.pc = (if j == 15 then (blkPl_416).base + 4424#64 else (blkPl_416).base + 976#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = ptsBase →
      s1.readReg64 .x20 = BitVec.ofNat 64 (j + 1) →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool ∗
         polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool ∗
       polyOf A ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       newPolyBufAt A newPtr pt ∗
       ptVecBufAt A ptVecPtr pt.value ∗
       ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (deallocOldPolySlot_placed_sepWP hA s fsp hfsp_align j pt.value.length hbound
      (newPolyBufAt A newPtr pt ∗
       ptVecBufAt A ptVecPtr pt.value ∗
       ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗ Frame)
      hpc hrun hsp hx19 hx20 hx28 ?_)
  intro s1 oldCap oldPtr hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx21_1 hx26_1 hx27_1 hx28_1 hx29_1
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (storeNewPolyAndFreePtVec_placed_sepWP hA s1 fsp oldCap oldPtr newPtr ptVecPtr hfsp_align j pt hbound
      (((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ Frame)
      hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 (hx26_1.trans hx26) hx28_1 ?_)
  intro s2 hpc2 hrun2 hsp2 htr2 hvregs2 hx27_2 hx28_2 hx29_2
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc2 hcont ⊢
  by_cases hj15 : j = 15
  · subst hj15
    wp_steps 5
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _
        (by simp only [arm64_norm, wp_norm])
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp2])
        (by simp only [arm64_norm, wp_norm, htr2, htr1])
        (by simp only [arm64_norm, wp_norm, hvregs2, hvregs1])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx27_2, hx27_1])
        (by simp only [arm64_norm, wp_norm, hx28_2])
        (by simp only [arm64_norm, wp_norm, hx29_2, hx29_1]))
  · have hj15_beq : (j == 15) = false := beq_eq_false_iff_ne.mpr hj15
    have hcmp_sub : (BitVec.ofNat 64 (j + 1) - 16#64 == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr; bv_omega
    have hcmp_eq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := by
      apply beq_eq_false_iff_ne.mpr; bv_omega
    have hcmp_bne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := by
      simp [bne, hcmp_eq]
    wp_steps 4
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _
        (by simp only [arm64_norm, wp_norm, hj15_beq, hcmp_sub, hcmp_eq, hcmp_bne]; rfl)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hsp2])
        (by simp only [arm64_norm, wp_norm, htr2, htr1])
        (by simp only [arm64_norm, wp_norm, hvregs2, hvregs1])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx27_2, hx27_1])
        (by simp only [arm64_norm, wp_norm, hx28_2])
        (by simp only [arm64_norm, wp_norm, hx29_2, hx29_1]))

end CryptoVerification.SpqrV1.Poly.NextChunk
