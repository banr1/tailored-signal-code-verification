/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProof
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFastPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsSlow
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsSlowPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysTailPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Top-Level Verification

Composes all branches of `<PolyEncoder as Encoder>::next_chunk` under `[LibsignalPlacement]`,
parameterized over `PointsToPolysLoopPlacedProp A ext` (`+976 -> +4424`), to prove
`poly_next_chunk_rodata_placed_ok_of_p2p` and `poly_next_chunk_placed_ok_of_p2p`.
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
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

/-! ## 1. Placed Interface for the 16-Iteration `points_to_polys` Loop (`+976 -> +4424`) -/

/-- Relocatable `[LibsignalPlacement]` contract for the 16-iteration `points_to_polys` conversion
    loop (`+976 -> +4424` in Block `416`), matching `pointsToPolysLoop_tail_sepWPp` at `rem = 15, j = 0`. -/
def PointsToPolysLoopPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  ∀ {Q : State → SepProp → Prop}
    (s0 s : State) (_hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptsBase : BitVec 64)
    (_hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Point) (_hlen : pts.length = 16)
    (_hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp)
    (_hpc : s.pc = (blkPl_416).base + 976#64)
    (_hrun : s.status = .Running) (_hsp : s.sp = fsp) (_htrace : s.trace = s0.trace)
    (_hx19 : s.readReg64 .x19 = ptsBase)
    (_hx20 : s.readReg64 .x20 = 0#64)
    (_hx28 : s.readReg64 .x28 = 24#64)
    (_hx29 : s.readReg64 .x29 = fsp + 1104#64),
    (∀ s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      s_out.pc = (blkPl_416).base + 4424#64 →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase →
      s_out.readReg64 .x20 = 16#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool ∗
         pointListOf A ptsBase pts ∗
         polyListOf A (fsp + 256#64) (pts.map pointToPolyPure) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) →
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       pointListOf A ptsBase pts ∗
       polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))

private theorem pointsToPolysLoop_lscl_of_prop [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (h_p2p : PointsToPolysLoopPlacedProp A ext)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Point) (hlen : pts.length = 16)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 976#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = 0#64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056',
      LibsignalCodeLoaded lsmpl s_out.mem →
      s_out.pc = (blkPl_416).base + 4424#64 →
      s_out.status = .Running → s_out.sp = fsp → s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = ptsBase →
      s_out.readReg64 .x20 = 16#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool ∗
         pointListOf A ptsBase pts ∗
         polyListOf A (fsp + 256#64) (pts.map pointToPolyPure) ∗
         ((fsp + 16#64) ↦₆₄ u16') ∗ ((fsp + 24#64) ↦₆₄ u24') ∗
         ((fsp + 32#64) ↦₆₄ u32') ∗ ((fsp + 40#64) ↦₆₄ u40') ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         ((fsp + 64#64) ↦₆₄ u64') ∗ ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96') ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ u640') ∗ ((fsp + 648#64) ↦₆₄ u648') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       pointListOf A ptsBase pts ∗
       polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  let s0' : State := s0.writeReg64 (Reg.gpr 30#5) ((blkPl_416).base + 4424#64)
  have hlr' : s0'.readReg64 (Reg.gpr 30#5) = (blkPl_416).base + 4424#64 := by
    simp [s0', arm64_norm, wp_norm]
  have htr' : s.trace = s0'.trace := by
    simpa [s0', arm64_norm, wp_norm] using htrace
  refine sepWPp_seq_lscl (mid := s0'.readReg64 (Reg.gpr 30#5)) hcl ?_
  refine h_p2p s0' s hcl fsp ptsBase hfsp_align pts hlen hbounds
    u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056 Frame R
    hpc hrun hsp htr' hx19 hx20 hx28 hx29 ?_
  intro s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out
  refine SepWPp.done (hlr' ▸ hpc_out) hrun_out (fun hcl_out => ?_)
  have htr_out0 : s_out.trace = s0.trace := by simpa [s0', arm64_norm, wp_norm] using htr_out
  exact hcont s_out u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hcl_out hpc_out hrun_out hsp_out htr_out0 hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out

/-! ## 2. Slow `EncoderState::Points` Path (`nextChunk_points_slow_placed_sepWPp`) -/

set_option maxHeartbeats 800000 in
theorem nextChunk_points_slow_placed_sepWPp [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (h_p2p : PointsToPolysLoopPlacedProp A ext)
    (x : PolyNextChunkGhost) (pts : List Point)
    (hs_pts : x.enc.s = .points pts)
    (hlen_pts : pts.length = NUM_POLYS)
    (hbounds : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (i0 : Nat) (hi0 : i0 < 16)
    (hfast : ∀ j (hj : j < pts.length), j < i0 →
      (x.enc.idx.setWidth 16).toNat < (pts[j]'hj).value.length)
    (hslow : (pts[i0]'(by rw [hlen_pts]; exact hi0)).value.length ≤ (x.enc.idx.setWidth 16).toNat)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) s0
      (memRegion x.outA chunkSize ∗
       polyEncoderAt A x.encA x.enc ∗
       completePointsPolysPlacedAt ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool ∗
       stackAt s0.sp polyNextChunkStack)
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
  have hfsp_align : ((s0.sp - 1200#64) &&& 15#64 == 0#64) = true := by
    apply beq_iff_eq.mpr; revert hsp0; bv_bits
  conv => arg 4; unfold polyEncoderAt encoderStateAt; rw [hs_pts]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad P_ro Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ P_ro ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ (P_list ∗ P_ro) ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; intro _
  have hlen16 : pts.length = 16 := hlen_pts
  have henc_eq : x.enc = { idx := x.enc.idx, s := .points pts } := by rw [← hs_pts]
  have hnc := nextChunk_points_slow_eq hlen16 hbounds i0 hi0 hfast hslow
  rw [← henc_eq] at hnc
  rw [hnc, Except.ok.injEq, Prod.mk.injEq] at hnext
  rcases hnext with ⟨henc'_eq, hchunk_eq⟩
  have hdata_eq : x.chunk.data.toList =
      chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0 ++
        chunkPolysBytes (x.enc.idx.setWidth 16) (pts.map pointToPolyPure) i0 (15 - i0 + 1) := by
    rw [← hchunk_eq]; rfl
  have hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16 := by rw [← hchunk_eq]
  have hidx_enc' : x.enc'.idx = x.enc.idx + 1#32 := by rw [← henc'_eq]
  have hs_enc' : x.enc'.s = .polys (pts.map pointToPolyPure) := by rw [← henc'_eq]
  refine prologue_lscl_placed_sepWPp A ext hA x polyEncoderPointsTag
    (pointListOf A (x.encA + polyEncoderVecsOff) pts ∗ completePointsPolysPlacedAt)
    R s0 hcl0 hpc hrun hsp0 hx0 hx8 ?_
  intro s1 out_ptr hout_ne hpc1 hrun1 hsp1 htr1 hvregs1 hcl1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1
  change s1.readReg64 .x9 = 0#64 at hx9_1
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 436#64) hcl1 ?_
  apply SepWP.fold (localFrameRest_unfold_points (s0.sp - 1200#64)) (by sep_focus)
  apply sepWP_exists_left_sep; intro u48
  apply sepWP_exists_left_sep; intro u88
  apply sepWP_exists_left_sep; intro u104
  wp_steps 9
  have hinit_buf :
      memRegion out_ptr 32 =
        (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 0) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (32 - 2 * 0) := by
    simp [chunkPointsBytes, pointsToBytes_nil, emp_sepConj]
  rw [hinit_buf]
  refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [polyEncoderVecsOff]; simp only [arm64_norm]; ac_rfl))
    (pointsFastPrefix_placed_sepWP A ext x pts hlen16 out_ptr (s0.sp - 1200#64) hfsp_align
      (A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPointsTag) ∗
       completePointsPolysPlacedAt ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       localFramePointsRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      i0 0 u104 _ (by omega)
      (fun j hj => hfast j (by omega) (by omega))
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      rfl (by simpa [arm64_norm, wp_norm] using hx19_1) rfl rfl
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1) rfl ?_)
  intro s2 u104' hpc2 hrun2 hsp2 htr2 hvregs2 hx9_2 hx19_2 hx20_2 hx21_2 hx24_2 hx27_2 hx28_2 hx29_2
  simp only [Nat.zero_add] at hx9_2 hx20_2 ⊢
  refine SepWP.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
    (pointsSlowTrigger_placed_sepWP A ext x pts hlen16 i0 hi0 hslow (s0.sp - 1200#64) u104' hfsp_align
      ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i0)) (32 - 2 * i0) ∗
       (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i0)) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPointsTag) ∗
       completePointsPolysPlacedAt ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       localFramePointsRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      s2 hpc2 hrun2 hsp2 hx9_2 hx19_2 hx21_2 hx24_2 hx27_2 hx28_2 ?_)
  intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx24_3 hx27_3 hx29_3
  refine SepWP.done hpc3 hrun3 ?_
  intro hcl3
  have htr3_0 : s3.trace = s0.trace := by
    rw [htr3, htr2]; simpa [arm64_norm, wp_norm] using htr1
  have hx29_3_0 : s3.readReg64 .x29 = (s0.sp - 1200#64) + 1104#64 := by
    rw [hx29_3, hx29_2]; simpa [arm64_norm, wp_norm] using hx29_1
  apply SepWPp.fold (localFramePointsRest_unfold_slow (s0.sp - 1200#64)) (by sep_focus)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWPp.exists_elim; intro _)
  rename_i u8 u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
  rw [stackAt_nextChunkCallee_split_lagrangePrepare (s0.sp - 1200#64),
      stackAt_lagrangePrepare_split_alloc (s0.sp - 1200#64)]
  refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
    (blockA_lscl_placed_sepWPp hA s0 s3 hcl3 (s0.sp - 1200#64) (x.encA + 8#64) u8 hfsp_align
      (pointListOf A (x.encA + 8#64) pts ∗
       (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
       (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i0)) (32 - 2 * i0) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i0)) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPointsTag) ∗
       completePointsPolysPlacedAt ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       memRegion (s0.sp - 1200#64) 8 ∗
       (((s0.sp - 1200#64) + 16#64) ↦₆₄ u16) ∗
       (((s0.sp - 1200#64) + 24#64) ↦₆₄ u24) ∗
       (((s0.sp - 1200#64) + 32#64) ↦₆₄ u32) ∗
       (((s0.sp - 1200#64) + 40#64) ↦₆₄ u40) ∗
       (((s0.sp - 1200#64) + 64#64) ↦₆₄ u64) ∗
       (((s0.sp - 1200#64) + 72#64) ↦₆₄ u72) ∗
       (((s0.sp - 1200#64) + 80#64) ↦₆₄ u80) ∗
       (((s0.sp - 1200#64) + 96#64) ↦₆₄ u96) ∗
       (((s0.sp - 1200#64) + 640#64) ↦₆₄ u640) ∗
       (((s0.sp - 1200#64) + 648#64) ↦₆₄ u648) ∗
       memRegion ((s0.sp - 1200#64) + 656#64) 24 ∗
       memRegion ((s0.sp - 1200#64) + 680#64) 360 ∗
       (((s0.sp - 1200#64) + 1040#64) ↦₆₄ u1040) ∗
       (((s0.sp - 1200#64) + 1048#64) ↦₆₄ u1048) ∗
       (((s0.sp - 1200#64) + 1056#64) ↦₆₄ u1056) ∗
       memRegion ((s0.sp - 1200#64) + 1064#64) 40 ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       memRegion ((s0.sp - 1200#64) - 17232#64) 12928 ∗
       memRegion ((s0.sp - 1200#64) - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack))
      R hpc3 hrun3 hsp3 htr3_0 ?_)
  intro s4 hcl4 hpc4 hrun4 hsp4 htr4 hvregs4 hx19_4 hx20_4 hx27_4 hx28_4 hx29_4
  rw [hx24_3]
  rw [hx27_3] at hx27_4
  rw [hx29_3_0] at hx29_4
  apply SepWPp.fold (stackAt_lagrangePrepare_fold_alloc (s0.sp - 1200#64)) (by sep_focus)
  refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm, wp_norm]; ac_rfl))
    (pointsToPolysLoop_lscl_of_prop h_p2p s0 s4 hcl4 (s0.sp - 1200#64) (x.encA + 8#64) hfsp_align
      pts hlen16 hbounds
      u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
      ((((s0.sp - 1200#64) + 8#64) ↦₆₄ x.encA) ∗
       (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i0) ∗
       (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i0)) (32 - 2 * i0) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i0)) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPointsTag) ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       memRegion (s0.sp - 1200#64) 8 ∗
       memRegion ((s0.sp - 1200#64) + 680#64) 360 ∗
       memRegion ((s0.sp - 1200#64) + 1064#64) 40 ∗
       savedCells s0 ∗
       memRegion ((s0.sp - 1200#64) - 17232#64) 12928)
      R hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx28_4 hx29_4 ?_)
  intro s5 u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056'
    hcl5 hpc5 hrun5 hsp5 htr5 hvregs5 hx19_5 hx20_5 hx27_5 hx28_5 hx29_5
  rw [hx27_4] at hx27_5
  have hfold_nc_stack :
      memRegion ((s0.sp - 1200#64) - 17232#64) 12928 ∗
        stackAt (s0.sp - 1200#64) lagrangePrepareStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    rw [stackAt_nextChunkCallee_split_lagrangePrepare (s0.sp - 1200#64)]
    exact Entails.refl _
  apply SepWPp.fold hfold_nc_stack (by sep_focus)
  apply SepWPp.fold (memRegion_656_join_680 (s0.sp - 1200#64)) (by sep_focus)
  rw [stackAt_nextChunkCallee_split_blockC (s0.sp - 1200#64)]
  have hlen_polys : (pts.map pointToPolyPure).length = 16 := by simp [hlen16]
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 296#64) hcl5 ?_
  refine SepWP.weaken_pre (Entails.of_eq (by simp only [arm64_norm, wp_norm]; ac_rfl))
    (blockC_placed_sepWP A ext hA x pts hlen16 (pts.map pointToPolyPure) hlen_polys i0
      (s0.sp - 1200#64) hfsp_align
      ((((s0.sp - 1200#64) + 16#64) ↦₆₄ u16') ∗
       (((s0.sp - 1200#64) + 24#64) ↦₆₄ u24') ∗
       (((s0.sp - 1200#64) + 32#64) ↦₆₄ u32') ∗
       (((s0.sp - 1200#64) + 40#64) ↦₆₄ u40') ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
       (((s0.sp - 1200#64) + 64#64) ↦₆₄ u64') ∗
       (((s0.sp - 1200#64) + 72#64) ↦₆₄ u72') ∗
       (((s0.sp - 1200#64) + 80#64) ↦₆₄ u80') ∗
       (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
       (((s0.sp - 1200#64) + 96#64) ↦₆₄ u96') ∗
       memRegion ((s0.sp - 1200#64) + 112#64) 120 ∗
       (((s0.sp - 1200#64) + 640#64) ↦₆₄ u640') ∗
       (((s0.sp - 1200#64) + 648#64) ↦₆₄ u648') ∗
       (((s0.sp - 1200#64) + 1040#64) ↦₆₄ u1040') ∗
       (((s0.sp - 1200#64) + 1048#64) ↦₆₄ u1048') ∗
       (((s0.sp - 1200#64) + 1056#64) ↦₆₄ u1056') ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i0)) (32 - 2 * i0) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i0)) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       memRegion (s0.sp - 1200#64) 8 ∗
       memRegion ((s0.sp - 1200#64) + 1064#64) 40 ∗
       savedCells s0 ∗
       memRegion ((s0.sp - 1200#64) - 17232#64) 13104)
      s5 hcl5 hpc5 hrun5 hsp5 hx19_5 hx27_5 hx28_5 ?_)
  intro s6 hpc6 hrun6 hsp6 htr6 hvregs6 hx9_6 hx19_6 hx24_6 hx27_6 hx28_6 hx29_6
  refine SepWP.done hpc6 hrun6 ?_
  intro hcl6
  have htr6_0 : s6.trace = s0.trace := htr6.trans htr5
  have hvregs6_0 : calleeSavedVRegs s6 = calleeSavedVRegs s0 := by
    rw [hvregs6, hvregs5, hvregs4, hvregs3, hvregs2]
    simpa [arm64_norm, wp_norm] using hvregs1
  have hfold_bc_stack :
      memRegion ((s0.sp - 1200#64) - 17232#64) 13104 ∗
        memRegion ((s0.sp - 1200#64) - 4128#64) 32 ∗
        stackAt (s0.sp - 1200#64) allocHookStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    rw [stackAt_nextChunkCallee_split_blockC (s0.sp - 1200#64)]
    exact Entails.refl _
  apply SepWPp.fold hfold_bc_stack (by sep_focus)
  apply SepWPp.fold
    (localFramePointsRest_fold_slow (s0.sp - 1200#64)
      x.encA u16' u24' u32' u40' u64' u72' u80' u96' u640' u648' u1040' u1048' u1056')
    (by sep_focus)
  refine SepWPp.weaken_pre ?h_ent
    (sepWPp_drop_frame_placed (F := completePointsPolysPlacedAt)
      (polysTailLoop_placed_sepWPp A ext hA x (pts.map pointToPolyPure) hlen_polys
        out_ptr 2#64 (completePointsPolysPlacedAt ∗ R) s0 hsp0
        (15 - i0) i0 (chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i0) s6 hcl6
        (by omega) (chunkPointsBytes_length (x.enc.idx.setWidth 16) pts 0 i0)
        hpc6 hrun6 hsp6 htr6_0 hvregs6_0 hx9_6 hx19_6 hx24_6 hx27_6 hx28_6 ?h_tail))
  case h_ent =>
    exact Entails.of_eq (by simp only [arm64_norm, Nat.mul_comm 2 i0]; ac_rfl)
  case h_tail =>
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _hcl_f hx20_f hx24_f hx27_f
    apply SepWPp.of_sepWP_ret
    have hlfr_fold :
        (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
          (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          (((s0.sp - 1200#64) + 104#64) ↦₆₄ 15#64) ∗
          localFramePointsRest (s0.sp - 1200#64) ⊢
          localFrameRest (s0.sp - 1200#64) :=
      localFrameRest_fold_points (s0.sp - 1200#64) 2#64 (x.encA + 8#64) 15#64
    apply SepWP.fold hlfr_fold (by sep_focus)
    have henc'_state :
        (x.encA ↦₆₄ polyEncoderPolysTag) ∗ polyListOf A (x.encA + 8#64) (pts.map pointToPolyPure) ⊢
          encoderStateAt A x.encA x.enc'.s := by
      rw [hs_enc']
      unfold encoderStateAt
      dsimp only [polyEncoderVecsOff]
      have htrue : ((pts.map pointToPolyPure).length = NUM_POLYS) = True :=
        propext ⟨fun _ => trivial, fun _ => by simp [hlen_pts]⟩
      rw [htrue, pure_true, emp_sepConj]
      exact Entails.refl _
    apply SepWP.fold henc'_state (by sep_focus)
    rw [← hdata_eq]
    refine SepWP.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
      (epilogue_placed_sepWP A ext hA x (completePointsPolysPlacedAt ∗ R) s0 sf out_ptr hout_ne
        hidx_chunk hidx_enc' hpc_f hrun_f hsp_f hsp0 htr_f hx20_f hx24_f ?_ hvregs_f)
    rw [hx27_f, BitVec.setWidth_setWidth_of_le (x.enc.idx.setWidth 16) (by decide)]
    rfl

/-! ## 3. Full `EncoderState::Points` Dispatcher (`nextChunk_points_placed_sepWPp`) -/

theorem nextChunk_points_placed_sepWPp [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (h_p2p : PointsToPolysLoopPlacedProp A ext)
    (x : PolyNextChunkGhost) (pts : List Point)
    (hs_pts : x.enc.s = .points pts)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) s0
      (memRegion x.outA chunkSize ∗
       polyEncoderAt A x.encA x.enc ∗
       completePointsPolysPlacedAt ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool ∗
       stackAt s0.sp polyNextChunkStack)
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
  conv => arg 4; unfold polyEncoderAt encoderStateAt; rw [hs_pts]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ P_list ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; rintro ⟨hlen_pts, hbounds⟩
  have hrestore :
      memRegion x.outA chunkSize ∗
        (x.encA ↦₆₄ polyEncoderPointsTag) ∗
        pointListOf A (x.encA + polyEncoderVecsOff) pts ∗
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
        memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
        completePointsPolysPlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        stackAt s0.sp polyNextChunkStack =
      memRegion x.outA chunkSize ∗
        polyEncoderAt A x.encA x.enc ∗
        completePointsPolysPlacedAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        stackAt s0.sp polyNextChunkStack := by
    unfold polyEncoderAt encoderStateAt
    rw [hs_pts]
    dsimp only []
    have htrue : (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)) = True :=
      propext ⟨fun _ => trivial, fun _ => ⟨hlen_pts, hbounds⟩⟩
    rw [htrue, pure_true, emp_sepConj]
    ac_rfl
  rw [hrestore]
  have hlen16 : pts.length = 16 := hlen_pts
  let i0 := firstSlowIdxAux (x.enc.idx.setWidth 16).toNat pts 16 0
  have hi0_le : i0 ≤ 16 := firstSlowIdxAux_le_16 (x.enc.idx.setWidth 16).toNat pts 16 0 (by omega)
  by_cases hi0 : i0 < 16
  · have hi0_len : i0 < pts.length := by omega
    have hslow : (pts[i0]'hi0_len).value.length ≤ (x.enc.idx.setWidth 16).toNat := by
      have h := firstSlowIdxAux_slow (x.enc.idx.setWidth 16).toNat pts 16 0 (by omega) hi0
      change (pts[i0]?.getD ⟨[]⟩).value.length ≤ (x.enc.idx.setWidth 16).toNat at h
      simpa [List.getElem?_eq_getElem hi0_len] using h
    have hfast : ∀ j (hj : j < pts.length), j < i0 →
        (x.enc.idx.setWidth 16).toNat < (pts[j]'hj).value.length := by
      intro j hj hjlt
      have h := firstSlowIdxAux_fast (x.enc.idx.setWidth 16).toNat pts 16 0 j (by omega) (by omega) hjlt
      simpa [List.getElem?_eq_getElem hj] using h
    exact nextChunk_points_slow_placed_sepWPp A ext hA h_p2p x pts hs_pts hlen_pts hbounds
      i0 hi0 hfast hslow hnext R s0 hcl0 hpc hrun hsp0 hx0 hx8
  · have hi0_16 : i0 = 16 := by omega
    have hfast_all : ∀ k : Fin NUM_POLYS,
        (x.enc.idx.setWidth 16).toNat < (pts[k.val]'(by have := k.isLt; omega)).value.length := by
      intro k
      have hk_len : k.val < pts.length := by have := k.isLt; omega
      have hk_i0 : k.val < i0 := by have := k.isLt; change k.val < 16 at this; omega
      have h := firstSlowIdxAux_fast (x.enc.idx.setWidth 16).toNat pts 16 0 k.val (by omega) (by omega) hk_i0
      simpa [List.getElem?_eq_getElem hk_len] using h
    refine SepWPp.weaken_pre ?h_ent
      (sepWPp_drop_frame_placed (F := completePointsPolysPlacedAt)
        (nextChunk_points_fast_placed_sepWPp A ext hA x pts hs_pts hlen_pts hfast_all
          hnext (completePointsPolysPlacedAt ∗ R) s0 hpc hrun hsp0 hx0 hx8))
    case h_ent =>
      exact Entails.of_eq (by ac_rfl)

/-! ## 4. Top-Level Placed Contracts (`poly_next_chunk_rodata_placed_ok_of_p2p` & `poly_next_chunk_placed_ok_of_p2p`) -/

private def polyNextChunkRodataLsclAuxSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec PolyNextChunkGhost where
  pre := fun x s =>
    ⌜LibsignalCodeLoaded lsmpl s.mem ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.encA ∧
      x.enc.nextChunk = .ok (x.enc', x.chunk)⌝ ∗
      memRegion x.outA chunkSize ∗
      polyEncoderAt A x.encA x.enc ∗
      completePointsPolysPlacedAt ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp polyNextChunkStack
  post := (polyNextChunkPlacedSpec A).post
  onPanic := (polyNextChunkPlacedSpec A).onPanic

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `PolyNextChunkRodataPlacedOkExt A ext` given `h_p2p`. -/
theorem poly_next_chunk_rodata_placed_ok_of_p2p [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (h_p2p : PointsToPolysLoopPlacedProp A ext) :
    PolyNextChunkRodataPlacedOkExt A ext := by
  unfold PolyNextChunkRodataPlacedOkExt
  have haux : subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (blkPl_416).base (polyNextChunkRodataLsclAuxSpec A) := by
    simp only [polyNextChunkRodataLsclAuxSpec, polyNextChunkPlacedSpec]
    wpp_init x s0
    have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
    have hx8 : s0.readReg64 .x8 = x.outA := by assumption
    have hx0 : s0.readReg64 .x0 = x.encA := by assumption
    have hnext : x.enc.nextChunk = .ok (x.enc', x.chunk) := by assumption
    have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
    conv => arg 5; ext sf P_f; simp only [sepConj_assoc]
    cases hs : x.enc.s with
    | polys polys =>
      refine SepWPp.weaken_pre ?h_ent
        (sepWPp_drop_frame_placed (F := completePointsPolysPlacedAt)
          (nextChunk_polys_placed_sepWPp A ext hA x polys hs hnext
            (completePointsPolysPlacedAt ∗ R) s0 hcl0 hpc hrun hsp0 hx0 hx8))
      case h_ent =>
        exact Entails.of_eq (by ac_rfl)
    | points pts =>
      exact nextChunk_points_placed_sepWPp A ext hA h_p2p x pts hs hnext
        R s0 hcl0 hpc hrun hsp0 hx0 hx8
  refine subroutine_ok_mono haux (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hp
  dsimp only [polyNextChunkRodataPlacedSpec] at hpre
  dsimp only [polyNextChunkRodataLsclAuxSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨hcl, hpre.1⟩, hpre.2⟩

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `PolyNextChunkPlacedOkExt A ext` (`withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A)`)
    given `h_p2p`. -/
theorem poly_next_chunk_placed_ok_of_p2p [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (h_p2p : PointsToPolysLoopPlacedProp A ext) :
    PolyNextChunkPlacedOkExt A ext := by
  unfold PolyNextChunkPlacedOkExt
  have hro_ok := poly_next_chunk_rodata_placed_ok_of_p2p A ext hA h_p2p
  unfold PolyNextChunkRodataPlacedOkExt at hro_ok
  refine subroutine_ok_mono hro_ok (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [polyNextChunkPlacedSpec] at hpre
  dsimp only [withLsCodeLoaded, polyNextChunkRodataPlacedSpec]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨hpre.1, ?_⟩
  have hro_pre := rodata_completePointsPolys_placed hro hpre.2
  rwa [show (memRegion x.outA chunkSize ∗
        polyEncoderAt A x.encA x.enc ∗
        completePointsPolysPlacedAt ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        A.pool ∗ stackAt s0.sp polyNextChunkStack) ∗ R =
      completePointsPolysPlacedAt ∗
        ((memRegion x.outA chunkSize ∗
          polyEncoderAt A x.encA x.enc ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool ∗ stackAt s0.sp polyNextChunkStack) ∗ R) by ac_rfl]

end CryptoVerification.SpqrV1.Poly.NextChunk

namespace CryptoVerification.SpqrV1.Poly
export NextChunk (PointsToPolysLoopPlacedProp
  poly_next_chunk_rodata_placed_ok_of_p2p poly_next_chunk_placed_ok_of_p2p)
end CryptoVerification.SpqrV1.Poly
