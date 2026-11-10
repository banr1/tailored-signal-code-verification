/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExit
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst30Placed
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5Placed
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoopPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed Fallback Exit and Unified Positive Basis

Relocatable `[LibsignalPlacement]` verification of `lagrangeBasisExit_placed_sepWPp`
(`+4116 -> +2608`), `basis_fallback_placed_sepWPp`, and the unified basis construction
`basis_pos_placed_sepWPp` (`+1136 -> +2608`) for all `0 < pts.length ≤ 0x0555555555555555`.
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
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_fbe_pl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_eight_fbe_pl :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one_fb ofNat_succ_add_neg_one_fb ofNat_add_one_eq_succ_fb
  shl_one_ofNat_eq shl_one_ofNat_eq_nat

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

/-! ## 1. `LibsignalCodeLoaded`-Preserving CPS Cut Helpers -/

private def s0WithLr (s0 : State) (mid : BitVec 64) : State :=
  s0.writeReg64 (Reg.gpr 30#5) mid

private theorem s0WithLr_trace (s0 : State) (mid : BitVec 64) :
    (s0WithLr s0 mid).trace = s0.trace := rfl

private theorem s0WithLr_lr (s0 : State) (mid : BitVec 64) :
    (s0WithLr s0 mid).readReg64 (Reg.gpr 30#5) = mid := by
  simp [s0WithLr, arm64_norm, wp_norm]

private theorem sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp prog mid s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp) Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hcont⟩ | hpan_or_oom⟩ := h R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont (hcl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

section
set_option quotPrecheck false
local notation "s0WithLr_pub" =>
  (fun (s0 : State) (mid : BitVec 64) => (s0.writeReg64 (Reg.gpr 30#5) mid : State))

/-- Cut a CPS `SepWPp` lemma parameterized by `s0` (whose `ret` is `s0.readReg64 (Reg.gpr 30#5)`
    and whose `onPanic` is `nextChunkOnPanic s0`) at `mid`, threading `LibsignalCodeLoaded`. -/
theorem sepWPp_cut_s0WithLr [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    {s0 s : State} {mid : BitVec 64} {P R : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((s0WithLr_pub s0 mid).readReg64 (Reg.gpr 30#5)) s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) sm Pm Q
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic (s0WithLr_pub s0 mid) sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  change SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((s0WithLr s0 mid).readReg64 (Reg.gpr 30#5)) s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) sm Pm Q
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic (s0WithLr s0 mid) sf ∗ R)) at h
  rw [s0WithLr_lr] at h
  exact sepWPp_bind_lscl hcl h

theorem sepWPp_done_s0WithLr [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    {s0 s1 : State} {mid : BitVec 64} {P1 R : SepProp}
    (hpc1 : s1.pc = mid) (hrun1 : s1.status = .Running)
    (hcont : LibsignalCodeLoaded lsmpl s1.mem →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1 P1 Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((s0WithLr_pub s0 mid).readReg64 (Reg.gpr 30#5)) s1 P1
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) sm Pm Q
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic (s0WithLr_pub s0 mid) sf ∗ R)) :=
  SepWPp.done (by change s1.pc = (s0WithLr s0 mid).readReg64 (Reg.gpr 30#5); rw [s0WithLr_lr]; exact hpc1) hrun1 hcont

end

/-! ## 2. Dynamic Lagrange Basis Loop Entry/Exit (`+4116 -> +2608`, Block `416`) -/

/-- `+4116 -> +2608`: runs `lagrangeBasisLoop_placed_sepWPp` on `toOnePts pts`,
    deallocates `xsPtr`, and allocates `accPtr` (`2 * pts.length` bytes, align 2). -/
theorem lagrangeBasisExit_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptVecPtr xsPtr basisPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hxs_ne : xsPtr ≠ 0#64) (hbasis_ne : basisPtr ≠ 0#64)
    (u72 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4116#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = xsPtr)
    (hx21 : s.readReg64 .x21 = basisPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 accPtr u216' u224' u1040' u1048' u1056',
      LibsignalCodeLoaded lsmpl s1.mem →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x25 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         basisVecAt A basisPtr (lagrangeBasisPure (toOnePts pts)) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 72#64) ↦₆₄ basisPtr) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       A.live xsPtr (4 * pts.length) 2 ∗ ptSliceAt xsPtr (toOnePts pts) ∗
       A.live basisPtr (24 * pts.length) 8 ∗ memRegion basisPtr (24 * pts.length) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_pos : 0 < pts.length := List.length_pos_iff.mpr hpts_ne
  have hones_ne : toOnePts pts ≠ [] := toOnePts_ne_nil hpts_ne
  have hones_len : (toOnePts pts).length = pts.length := toOnePts_length pts
  have hones_bound : (toOnePts pts).length ≤ 0x0555555555555555 := by rw [hones_len]; exact hbound
  have hsum : 0 + ((toOnePts pts).length - 1 + 1) = (toOnePts pts).length := by rw [hones_len]; omega
  have h24_eq : 24 * ((toOnePts pts).length - 1 + 1) = 24 * (toOnePts pts).length := by rw [hones_len]; omega
  have hshim := hA.shim_ok; simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok; simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hdealloc := hA.dealloc_ok; simp only [rustDeallocSpec, BitVec.ofNat_eq_ofNat] at hdealloc
  have hpanic4796 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4796_placed _ ext hA.handle_error Q s0 s P R
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hshim halloc hdealloc hpanic4796 hcont ⊢
  apply sepWPp_seq_lscl_fb hcl (mid := (blkPl_416).base + 4128#64)
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  rw [← hones_len, ← h24_eq]
  intro hcl0
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeBasisLoop_placed_sepWPp hA ((toOnePts pts).length - 1) 0 (toOnePts pts)
      hones_ne hones_bound hsum
      s0 _ hcl0 fsp xsPtr basisPtr hfsp_align u216 u224 u1040 u1048 u1056
      (A.live xsPtr (4 * (toOnePts pts).length) 2 ∗
       A.live basisPtr (24 * (((toOnePts pts).length - 1) + 1)) 8 ∗
       ((fsp + 72#64) ↦₆₄ basisPtr) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ Frame) R
      (by wp_norm_goal)
      (by wp_norm_lhs)
      (by simp only [wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htrace])
      (by wp_norm_lhs)
      (by simp only [wp_norm, hx20])
      (by simp only [wp_norm, hx21])
      (by rw [hones_len]; wp_norm_lhs)
      (by simp only [wp_norm, hx29]) ?_)
  intro s1 u216' u224' u1040' u1048' u1056' hcl1
    hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
  have hfrom_eq : lagrangeBasisFrom (toOnePts pts) 0 (((toOnePts pts).length - 1) + 1) =
      lagrangeBasisPure (toOnePts pts) := by
    rw [show ((toOnePts pts).length - 1) + 1 = (toOnePts pts).length by rw [hones_len]; omega]
    exact lagrangeBasisFrom_zero_eq (toOnePts pts)
  rw [hfrom_eq, h24_eq, hones_len]
  rw [hones_len] at hx22_1
  simp only [wp_norm] at hx24_1 hx25_1 hx27_1 hx28_1
  rw [hx24] at hx24_1
  have hlayout4 : LayoutOk (4 * pts.length) 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have h4n_toNat : (BitVec.ofNat 64 (4 * pts.length)).toNat = 4 * pts.length :=
    Nat.mod_eq_of_lt (by omega)
  have hlayout2 : LayoutOk (2 * pts.length) 2 := ⟨by omega, ⟨1, rfl⟩, by omega⟩
  have h2n_toNat : (BitVec.ofNat 64 (2 * pts.length)).toNat = 2 * pts.length :=
    Nat.mod_eq_of_lt (by omega)
  have hxs_mem : ptSliceAt xsPtr (toOnePts pts) ⊢ memRegion xsPtr (4 * pts.length) := by
    rw [← hones_len]
    exact ptSliceAt_entails_memRegion xsPtr (toOnePts pts) hones_bound
  have hsp72_al : ((fsp + 72#64) &&& 7#64 == 0#64) = true := by
    revert hfsp_align; bv_bits
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  apply sepWPp_seq_lscl_fb hcl1 (mid := (blkPl_416).base + 4416#64)
  apply SepWP.fold hxs_mem (by sep_frame)
  wp_steps; wp_call hdealloc; wp_steps; wp_call hshim; wp_steps; wp_call halloc
  refine SepWP.done hpc_sf_2 hrun_sf_2 ?_
  intro hcl2
  by_cases hoom : sf_2.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr_oom
    refine hpanic4796 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h_10, hpost, htr1] at htr_oom; exact htr_oom⟩
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc, h_17, h_7, hx22_1, shl_one_ofNat_eq_nat, h2n_toNat]
    apply sepWPp_pure_mid; intro ⟨_, htr_alloc⟩
    have hcond_oom : ¬(sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom
    have hcond_ne : (sf_2.readReg64 (Reg.gpr 0#5) != 0#64) = true := by
      simpa [bne_iff_ne] using hoom
    apply sepWPp_seq_lscl_fb hcl2 (mid := (blkPl_416).base + 2608#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond_ne, hcond_oom, ↓reduceIte]) (by wp_norm_lhs) ?_
    intro hcl3
    have hsp_sf : sf.sp = fsp := by rw [‹sf.sp = s1.sp›, hsp1]
    have hsp_sf1 : sf_1.sp = fsp := by rw [‹sf_1.sp = _›]; simp only [wp_norm, hsp_sf]
    have hsp_sf2 : sf_2.sp = fsp := by rw [‹sf_2.sp = sf_1.sp›, hsp_sf1]
    have hbasis :
        (A.live basisPtr (24 * pts.length) 8 ∗
         polyListOf A basisPtr (lagrangeBasisPure (toOnePts pts))) ⊢
        basisVecAt A basisPtr (lagrangeBasisPure (toOnePts pts)) := by
      unfold basisVecAt
      rw [lagrangeBasisPure_length, hones_len]
      exact Entails.pure_right hbasis_ne (Entails.refl _)
    refine SepWPp.weaken_pre ?_
      (hcont _ (sf_2.readReg64 (Reg.gpr 0#5)) u216' u224' u1040' u1048' u1056' hcl3 hoom
        (by simp only [wp_norm, hcond_ne, hcond_oom, ↓reduceIte])
        (by wp_norm_lhs)
        (by simp only [wp_norm, hsp_sf2])
        (by simp only [arm64_norm, wp_norm]; rw [htr_alloc, h_10, hpost, htr1])
        (by simp only [arm64_norm, wp_norm, *])
        (by wp_norm_lhs)
        (by simp only [wp_norm, h_23, h_13])
        (by simp only [wp_norm, h_27, h_17])
        (by simp only [wp_norm, h_28, h_18])
        (by simp only [wp_norm, h_29, h_19])
        (by simp only [wp_norm, h_30, h_20, h_8, hx27_1])
        (by simp only [wp_norm, h_31, h_21, h_9, hx28_1])
        (by simp only [wp_norm, hcs_sf_1, hpost_sf, hcs_sf, hx29_1]))
    rw [hsp_sf1, stackAt_lagrangePrepare_split_alloc fsp,
        show BitVec.ofNat 64 lagrangePrepareStack = 4304#64 from rfl]
    refine Entails.trans (Entails.of_eq (show _ =
      (A.live basisPtr (24 * pts.length) 8 ∗
       polyListOf A basisPtr (lagrangeBasisPure (toOnePts pts))) ∗
      (A.pool ∗
       A.live (sf_2.readReg64 (Reg.gpr 0#5)) (2 * pts.length) 2 ∗
       memRegion (sf_2.readReg64 (Reg.gpr 0#5)) (2 * pts.length) ∗
       ((fsp + 72#64) ↦₆₄ basisPtr) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp allocHookStack ∗
       memRegion (fsp - 4304#64) (lagrangePrepareStack - allocHookStack) ∗
       Frame) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hbasis) ?_
    exact Entails.of_eq (by ac_rfl)

/-! ## 3. Full Dynamic Lagrange Fallback (`+1136 -> +2608`, Block `416`) -/

/-- Full dynamic Lagrange fallback (`+1136 -> +1804 -> +4116 -> +2608`) for
    `pts.length ∉ {0, 1, 3, 5, 30, 34, 36}`. -/
theorem basis_fallback_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (pts : List Pt) (hpts_ne : pts ≠ [])
    (hn1 : pts.length ≠ 1) (hn3 : pts.length ≠ 3) (hn5 : pts.length ≠ 5)
    (hn30 : pts.length ≠ 30) (hn34 : pts.length ≠ 34) (hn36 : pts.length ≠ 36)
    (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u72 u80 u96 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056',
      LibsignalCodeLoaded lsmpl s1.mem →
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗ ptSliceAt ptVecPtr pts ∗
         basisVecAt A basisPtr (lagrangeBasisPure (toOnePts pts)) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn0 : pts.length ≠ 0 := by intro h0; exact hpts_ne (List.eq_nil_of_length_eq_zero h0)
  apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 1804#64)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (dispatch_fallback_placed_sepWPp (s0WithLr s0 ((blkPl_416).base + 1804#64)) s fsp hfsp_align
      pts.length hn0 hn1 hn3 hn5 hn30 hn34 hn36 hbound u96
      (A.pool ∗ ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame) R
      hpc hrun hsp htrace hx25 ?_)
  intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
  rw [s0WithLr_trace] at htr1
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  apply sepWPp_cut_s0WithLr hcl1 (mid := (blkPl_416).base + 4116#64)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (allocXsAndBasis_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 4116#64)) s1
      fsp ptVecPtr hfsp_align pts hpts_ne hbound u24 u80
      (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
      hpc1 hrun1 hsp1 htr1 hx19_1 (by rw [hx24_1, hx24]) (by rw [hx26_1, hx26]) ?_)
  intro s2 xsPtr basisPtr hxs_ne hbasis_ne _ hpc2 hrun2 hsp2 htr2 hvregs2
    hx20_2 hx21_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  apply sepWPp_done_s0WithLr hpc2 hrun2; intro hcl2
  rw [s0WithLr_trace] at htr2
  refine SepWPp.weaken_pre
    (by
      have hst := (stackAt_lagrangePrepare_split_alloc fsp).symm
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack)) ∗
        (A.pool ∗ ptSliceAt ptVecPtr pts ∗
         A.live xsPtr (4 * pts.length) 2 ∗ ptSliceAt xsPtr (toOnePts pts) ∗
         A.live basisPtr (24 * pts.length) 8 ∗ memRegion basisPtr (24 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) by ac_rfl)) ?_
      rw [← hst]
      exact Entails.of_eq (by ac_rfl))
    (lagrangeBasisExit_placed_sepWPp hA pts hpts_ne hbound s0 s2 hcl2 fsp ptVecPtr xsPtr basisPtr
      hfsp_align hxs_ne hbasis_ne u72 u216 u224 u1040 u1048 u1056
      (ptSliceAt ptVecPtr pts ∗ ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame) R
      hpc2 hrun2 hsp2 htr2 hx20_2 hx21_2 hx24_2 (by rw [hx29_2, hx29_1, hx29]) ?_)
  intro s3 accPtr u216' u224' u1040' u1048' u1056' hcl3 hacc_ne
    hpc3 hrun3 hsp3 htr3 hvregs3 hx0_3 hx20_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s3 basisPtr accPtr basisPtr ptVecPtr u216' u224' u1040' u1048' u1056'
      hcl3 hbasis_ne hacc_ne hpc3 hrun3 hsp3 htr3 (by rw [hvregs3, hvregs2, hvregs1]) hx0_3
      (by rw [hx20_3, hx25_2, hx20_1]) hx24_3 hx25_3 hx26_3
      (by rw [hx27_3, hx27_2, hx27_1]) (by rw [hx28_3, hx28_2, hx28_1]) hx29_3)

/-! ## 4. Unified Basis Construction for `0 < pts.length` (`basis_pos_placed_sepWPp`) -/

/-- Unified basis construction (`+1136 -> +2608`) for all `pts ≠ []` with
    `pts.length ≤ 0x0555555555555555`. -/
theorem basis_pos_placed_sepWPp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsPlaced A ext)
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u72 u80 u96 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056',
      LibsignalCodeLoaded lsmpl s1.mem →
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗ ptSliceAt ptVecPtr pts ∗
         basisVecAt A basisPtr (completePointsBasisPure pts) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  by_cases hn1 : pts.length = 1
  · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_1 := by
      unfold completePointsBasisPure; simp [hn1]
    rw [stackAt_lagrangePrepare_split_alloc fsp]
    apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (basis_n1_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align u24 u96
        (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗
         ptSliceAt ptVecPtr pts ∗
         ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
        hpc hrun hsp htrace (by rw [hx25, hn1]) ?_)
    intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
      hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
    rw [s0WithLr_trace] at htr1
    refine SepWPp.weaken_pre
      (by
        rw [hbasis_eq, hn1, stackAt_lagrangePrepare_split_alloc fsp]
        exact Entails.of_eq (by ac_rfl))
      (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
        hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
        (by rw [hx25_1, hn1]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
  · by_cases hn3 : pts.length = 3
    · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_3 := by
        unfold completePointsBasisPure; simp [hn3]
      rw [stackAt_lagrangePrepare_split_alloc fsp]
      apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (basis_n3_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align u24 u96
          (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
             (lagrangePrepareStack - allocHookStack) ∗
           ptSliceAt ptVecPtr pts ∗
           ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
           ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
           memRegion (fsp + 656#64) 24 ∗
           ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
           completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
          hpc hrun hsp htrace (by rw [hx25, hn3]) ?_)
      intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
        hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
      rw [s0WithLr_trace] at htr1
      refine SepWPp.weaken_pre
        (by
          rw [hbasis_eq, hn3, stackAt_lagrangePrepare_split_alloc fsp]
          exact Entails.of_eq (by ac_rfl))
        (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
          hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
          (by rw [hx25_1, hn3]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
    · by_cases hn5 : pts.length = 5
      · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_5 := by
          unfold completePointsBasisPure; simp [hn5]
        unfold completePointsPolysPlacedAt
        rw [stackAt_lagrangePrepare_split_alloc fsp]
        apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (basis_n5_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align u24 u96
            (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
               (lagrangePrepareStack - allocHookStack) ∗
             ptSliceAt ptVecPtr pts ∗
             ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
             ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
             memRegion (fsp + 656#64) 24 ∗
             ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
             completePointsPolys30PlacedAt ∗ completePointsPolys34PlacedAt ∗ completePointsPolys36PlacedAt ∗
             reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
            hpc hrun hsp htrace (by rw [hx25, hn5]) ?_)
        intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
          hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
        apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
        rw [s0WithLr_trace] at htr1
        refine SepWPp.weaken_pre
          (by
            unfold completePointsPolysPlacedAt
            rw [hbasis_eq, hn5, stackAt_lagrangePrepare_split_alloc fsp]
            exact Entails.of_eq (by ac_rfl))
          (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
            hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
            (by rw [hx25_1, hn5]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
      · by_cases hn30 : pts.length = 30
        · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_30 := by
            unfold completePointsBasisPure; simp [hn30]
          unfold completePointsPolysPlacedAt
          rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWPp.exists_elim; intro u672
          apply SepWPp.exists_elim; intro u664
          apply SepWPp.exists_elim; intro u656
          apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (basis_n30_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align
              u24 u96 u656 u664 u672
              (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                 (lagrangePrepareStack - allocHookStack) ∗
               ptSliceAt ptVecPtr pts ∗
               ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
               ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
               ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
               completePointsPolys5PlacedAt ∗ completePointsPolys34PlacedAt ∗ completePointsPolys36PlacedAt ∗
               reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
              hpc hrun hsp htrace (by rw [hx25, hn30]) ?_)
          intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
            hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
          apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
          rw [s0WithLr_trace] at htr1
          refine SepWPp.weaken_pre
            (by
              unfold completePointsPolysPlacedAt
              rw [hbasis_eq, hn30, stackAt_lagrangePrepare_split_alloc fsp]
              refine Entails.trans (Entails.of_eq (show _ =
                (((fsp + 656#64) ↦₆₄ 30#64) ∗ ((fsp + 664#64) ↦₆₄ basisPtr) ∗ ((fsp + 672#64) ↦₆₄ 30#64)) ∗
                (A.pool ∗ ptSliceAt ptVecPtr pts ∗
                 basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_30) ∗
                 A.live accPtr 60 2 ∗ memRegion accPtr 60 ∗
                 ((fsp + 24#64) ↦₆₄ 30#64) ∗
                 ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                 ((fsp + 96#64) ↦₆₄ 30#64) ∗
                 ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                 ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
                 (completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗
                  completePointsPolys34PlacedAt ∗ completePointsPolys36PlacedAt) ∗
                 reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
                 (stackAt fsp allocHookStack ∗
                  memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                    (lagrangePrepareStack - allocHookStack)) ∗ Frame) by ac_rfl)) ?_
              refine Entails.trans (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 30#64 basisPtr 30#64)) ?_
              exact Entails.of_eq (by ac_rfl))
            (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
              hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
              (by rw [hx25_1, hn30]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
        · by_cases hn34 : pts.length = 34
          · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_34 := by
              unfold completePointsBasisPure; simp [hn34]
            unfold completePointsPolysPlacedAt
            rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWPp.exists_elim; intro u672
            apply SepWPp.exists_elim; intro u664
            apply SepWPp.exists_elim; intro u656
            apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
            refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
              (basis_n34_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align
                u24 u96 u656 u664 u672
                (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                   (lagrangePrepareStack - allocHookStack) ∗
                 ptSliceAt ptVecPtr pts ∗
                 ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                 ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                 ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
                 completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗ completePointsPolys36PlacedAt ∗
                 reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
                hpc hrun hsp htrace (by rw [hx25, hn34]) ?_)
            intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
              hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
            apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
            rw [s0WithLr_trace] at htr1
            refine SepWPp.weaken_pre
              (by
                unfold completePointsPolysPlacedAt
                rw [hbasis_eq, hn34, stackAt_lagrangePrepare_split_alloc fsp]
                refine Entails.trans (Entails.of_eq (show _ =
                  (((fsp + 656#64) ↦₆₄ 34#64) ∗ ((fsp + 664#64) ↦₆₄ basisPtr) ∗ ((fsp + 672#64) ↦₆₄ 34#64)) ∗
                  (A.pool ∗ ptSliceAt ptVecPtr pts ∗
                   basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_34) ∗
                   A.live accPtr 68 2 ∗ memRegion accPtr 68 ∗
                   ((fsp + 24#64) ↦₆₄ 34#64) ∗
                   ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                   ((fsp + 96#64) ↦₆₄ 34#64) ∗
                   ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                   ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
                   (completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗
                    completePointsPolys34PlacedAt ∗ completePointsPolys36PlacedAt) ∗
                   reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
                   (stackAt fsp allocHookStack ∗
                    memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                      (lagrangePrepareStack - allocHookStack)) ∗ Frame) by ac_rfl)) ?_
                refine Entails.trans (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 34#64 basisPtr 34#64)) ?_
                exact Entails.of_eq (by ac_rfl))
              (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
                hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
                (by rw [hx25_1, hn34]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
          · by_cases hn36 : pts.length = 36
            · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_36 := by
                unfold completePointsBasisPure; simp [hn36]
              unfold completePointsPolysPlacedAt
              rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWPp.exists_elim; intro u672
              apply SepWPp.exists_elim; intro u664
              apply SepWPp.exists_elim; intro u656
              apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
              refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
                (basis_n36_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align
                  u24 u96 u656 u664 u672
                  (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                     (lagrangePrepareStack - allocHookStack) ∗
                   ptSliceAt ptVecPtr pts ∗
                   ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                   ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                   ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
                   completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗ completePointsPolys34PlacedAt ∗
                   reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
                  hpc hrun hsp htrace (by rw [hx25, hn36]) ?_)
              intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
              apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
              rw [s0WithLr_trace] at htr1
              refine SepWPp.weaken_pre
                (by
                  unfold completePointsPolysPlacedAt
                  rw [hbasis_eq, hn36, stackAt_lagrangePrepare_split_alloc fsp]
                  refine Entails.trans (Entails.of_eq (show _ =
                    (((fsp + 656#64) ↦₆₄ 36#64) ∗ ((fsp + 664#64) ↦₆₄ basisPtr) ∗ ((fsp + 672#64) ↦₆₄ 36#64)) ∗
                    (A.pool ∗ ptSliceAt ptVecPtr pts ∗
                     basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_36) ∗
                     A.live accPtr 72 2 ∗ memRegion accPtr 72 ∗
                     ((fsp + 24#64) ↦₆₄ 36#64) ∗
                     ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                     ((fsp + 96#64) ↦₆₄ 36#64) ∗
                     ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                     ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
                     (completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗
                      completePointsPolys34PlacedAt ∗ completePointsPolys36PlacedAt) ∗
                     reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
                     (stackAt fsp allocHookStack ∗
                      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                        (lagrangePrepareStack - allocHookStack)) ∗ Frame) by ac_rfl)) ?_
                  refine Entails.trans (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 36#64 basisPtr 36#64)) ?_
                  exact Entails.of_eq (by ac_rfl))
                (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
                  hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
                  (by rw [hx25_1, hn36]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
            · have hn0 : pts.length ≠ 0 := by intro h0; exact hpts_ne (List.eq_nil_of_length_eq_zero h0)
              have hbasis_eq : completePointsBasisPure pts = lagrangeBasisPure (toOnePts pts) := by
                unfold completePointsBasisPure; simp [hn0, hn1, hn3, hn5, hn30, hn34, hn36]
              refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
                (basis_fallback_placed_sepWPp hA pts hpts_ne hn1 hn3 hn5 hn30 hn34 hn36 hbound
                  s0 s hcl fsp ptVecPtr hfsp_align u24 u72 u80 u96 u216 u224 u1040 u1048 u1056
                  (completePointsPolysPlacedAt ∗ Frame) R
                  hpc hrun hsp htrace hx24 hx25 hx26 hx29 ?_)
              intro s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056'
                hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
              refine SepWPp.weaken_pre
                (by rw [hbasis_eq]; exact Entails.of_eq (by ac_rfl))
                (hcont s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056'
                  hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                  hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1)

end CryptoVerification.SpqrV1.Poly.NextChunk
