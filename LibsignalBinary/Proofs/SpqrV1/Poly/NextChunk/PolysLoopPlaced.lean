/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Placed `EncoderState::Polys` Path

Relocatable `[LibsignalPlacement]` verification of the 16-iteration `EncoderState::Polys`
evaluation loop (`+92 -> +136..+220 -> +4484`), invoking `computeAt_placed_ok` (Block `371`).
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
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
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

attribute [local simp, local arm64_norm, local wp_norm]
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize
  x21_sub_8_eq x21_sub_8_add_8_eq x21_add_24_eq
  ofNat_two_mul_add_one ofNat_two_mul_add_two
  ofNat_succ_add_neg1 ofNat_succ_sub_one'
  setWidth16_mov_w_zext16

/-! ## 1. `LibsignalCodeLoaded`-Preserving `SepWPp` Sequencing, Prologue, and `compute_at` Call -/

/-- Sequence a `SepWPp` prefix ending at `mid` with a `SepWPp` continuation to `ret`,
    threading `LibsignalCodeLoaded lsmpl ·.mem` across `Steps.keepsFrozen`. -/
theorem sepWPp_seq_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
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

/-- Sequence a `SepWP` segment ending at `mid` into `SepWPp` while threading
    `LibsignalCodeLoaded lsmpl ·.mem`. -/
theorem sepWPp_of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ hf hkf => hf.of_keepsFrozen hkf) hcl h

/-- Panic-aware cross-block call combinator discharging `withLsCodeLoaded lsmpl` from `hcl`
    and handing `LibsignalCodeLoaded lsmpl sf.mem` to `hnext`. -/
theorem call_panic_lscl_sepWPp [LibsignalPlacement] {α : Type}
    {prog : Program} {entry ret_pc ret : BitVec 64}
    {s0 s : State} {spec : Spec α} {x : α} {φ : Prop} {T F P R : SepProp}
    {Q : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  apply sepWPp_seq_lscl (mid := ret_pc) hcl
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · intro sf code R' hex hpost
    exact hexit sf code R' hex hpost
  · intro sm _ hm'
    have hpan_tr : allocFailedIn s sm = allocFailedIn s0 sm := by
      unfold allocFailedIn; rw [htr]
    dsimp only [withLsCodeLoaded] at hm'
    rw [hpan_eq sm, hpan_tr, htr, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm'
    rcases hm' with ⟨hp, hm2⟩
    rw [← sepConj_assoc] at hm2
    unfold nextChunkOnPanic
    exact allowPanic_panicked (φ := allocFailedIn s0 sm ∧ s0.trace <+: sm.trace) hp hm2
  · intro sf hpcm hrunm hspm hcsm
    exact SepWPp.done hpcm hrunm (hnext sf hpcm hrunm hspm hcsm)
  · intro sm R' _ hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [hoom_eq sm, satisfies_pure_sepConj] at hpost
    exact False.elim hpost.1

set_option maxHeartbeats 800000 in
/-- `LibsignalCodeLoaded`-preserving wrapper around `prologue_placed_sepWPp` (`+0..+92`). -/
theorem prologue_lscl_placed_sepWPp [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (x : PolyNextChunkGhost) (tag : BitVec 64) (restEnc R : SepProp)
    {Q : State → SepProp → Prop}
    (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hcont : ∀ s1 (out_ptr : BitVec 64),
      out_ptr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 92#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 1200#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.readReg64 .x9 = (tag.setWidth 32).setWidth 64 →
      s1.readReg64 .x19 = x.encA + 8#64 →
      s1.readReg64 .x24 = x.encA →
      s1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
        (memRegion out_ptr 32 ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ tag) ∗
         restEnc ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ 0#64) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ tag) ∗
       restEnc ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool ∗
       stackAt s0.sp polyNextChunkStack)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  have h32_toNat : (32#64 : BitVec 64).toNat = 32 := rfl
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  have hshim := hA.shim_ok
  simp only [sessionShimSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.alloc_ok
  simp only [rustAllocSpec, BitVec.ofNat_eq_ofNat] at halloc
  have hpanic4736 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4736_placed _ ext hA.handle_error Q s0 s P R
  clear hA
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 64#64) hcl0 ?_
  apply SepWP.fold (prologue_stack_split s0) (by sep_focus)
  apply sepWP_exists_left_sep; intro v29
  apply sepWP_exists_left_sep; intro v30
  apply sepWP_exists_left_sep; intro v28
  apply sepWP_exists_left_sep; intro v27
  apply sepWP_exists_left_sep; intro v26
  apply sepWP_exists_left_sep; intro v25
  apply sepWP_exists_left_sep; intro v24
  apply sepWP_exists_left_sep; intro v23
  apply sepWP_exists_left_sep; intro v22
  apply sepWP_exists_left_sep; intro v21
  apply sepWP_exists_left_sep; intro v20
  apply sepWP_exists_left_sep; intro v19
  apply sepWP_exists_left_sep; intro u0
  apply sepWP_exists_left_sep; intro u56
  apply sepWP_exists_left_sep; intro u232
  apply sepWP_exists_left_sep; intro u240
  apply sepWP_exists_left_sep; intro u248
  wp_conv_pre =>
    rw [pointsTo32_eq_pointsTo16_pair (x.encA + polyEncoderIdxOff) x.enc.idx,
        pointsTo64_eq_pointsTo32_pair x.encA tag]
    dsimp only [polyEncoderIdxOff]
  wp_steps 12
  wp_call hshim
  wp_steps 3
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_call halloc
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl_sf1
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr0
    refine hpanic4736 _ _ ?_
    wp_steps 1
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, by simp only [arm64_norm, wp_norm, *]⟩
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩
    have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 92#64) hcl_sf1 ?_
    wp_steps 7
    have hfold_tag :
        (x.encA ↦₃₂ tag.setWidth 32) ∗ ((x.encA + 4#64) ↦₃₂ (tag >>> 32).setWidth 32) ⊢
          (x.encA ↦₆₄ tag) := by
      rw [← pointsTo64_eq_pointsTo32_pair x.encA tag]
      exact Entails.refl _
    apply SepWP.fold hfold_tag (by sep_focus)
    have hfold_idx :
        ((x.encA + 392#64) ↦₁₆ x.enc.idx.setWidth 16) ∗
          (((x.encA + 392#64) + 2#64) ↦₁₆ (x.enc.idx >>> 16).setWidth 16) ⊢
          ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) := by
      dsimp only [polyEncoderIdxOff]
      rw [← pointsTo32_eq_pointsTo16_pair (x.encA + 392#64) x.enc.idx]
      exact Entails.refl _
    apply SepWP.fold hfold_idx (by sep_focus)
    have hfold_rest :
        ((s0.sp - 1200#64) ↦₆₄ 0#64) ∗
          memRegion ((s0.sp - 1200#64) + 8#64) 48 ∗
          memRegion ((s0.sp - 1200#64) + 64#64) 168 ∗
          memRegion ((s0.sp - 1200#64) + 256#64) 848 ⊢
          localFrameRest (s0.sp - 1200#64) :=
      localFrameRest_fold_prologue (s0.sp - 1200#64) 0#64
    apply SepWP.fold hfold_rest (by sep_focus)
    have hfold_saved :
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
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
          savedCells s0 := by
      unfold savedCells
      exact Entails.refl _
    apply SepWP.fold hfold_saved (by sep_focus)
    wp_conv_pre => rw [h_1]
    have hfold_callee :
        memRegion ((s0.sp - 1200#64) - 17232#64) 13136 ∗
          stackAt (s0.sp - 1200#64) allocHookStack ⊢
          stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
      rw [← stackAt_nextChunkCallee_split_allocHook (s0.sp - 1200#64)]
      exact Entails.refl _
    apply SepWP.fold hfold_callee (by sep_focus)
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    intro hcl1
    refine SepWPp.weaken_pre ?_
      (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom ?_ ?_ ?_ ?_ ?_ hcl1 ?_ ?_ ?_ ?_ ?_)
    · simp only [arm64_norm]
      exact Entails.of_eq (by ac_rfl)
    all_goals simp only [arm64_norm, wp_norm, Reg.x0, Reg.x8, Reg.x9, Reg.x19, Reg.x24, Reg.x27, Reg.x29, Reg.lr, *]

theorem computeAt_pre_split_placed [LibsignalPlacement] (p_coeffs : BitVec 64)
    (poly : LibsignalSpqrV1.Poly) (fsp : BitVec 64) (A : RustAlloc)
    (P_cap P_ptr P_len P_restBuf P_out P_rem P_live P_outA P_tag P_take P_drop
     P_idx P_pad P_56 P_232 P_240 P_248 P_lfr P_saved : SepProp) :
    (P_cap ∗ P_ptr ∗ P_len ∗ (gf16SliceAt p_coeffs poly.coefficients ∗ P_restBuf)) ∗
      (P_out ∗ P_rem ∗ P_live ∗ P_outA ∗ P_tag ∗ P_take ∗ P_drop ∗
        P_idx ∗ P_pad ∗ P_56 ∗ P_232 ∗ P_240 ∗ P_248 ∗ P_lfr ∗ P_saved ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
        (memRegion (fsp - 17232#64) 12880 ∗ stackAt fsp computeAtStack)) =
    (gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗
      stackAt fsp computeAtStack) ∗
    (P_cap ∗ P_ptr ∗ P_len ∗ P_restBuf ∗
      P_out ∗ P_rem ∗ P_live ∗ P_outA ∗ P_tag ∗ P_take ∗ P_drop ∗
      P_idx ∗ P_pad ∗ P_56 ∗ P_232 ∗ P_240 ∗ P_248 ∗ P_lfr ∗ P_saved ∗
      memRegion (fsp - 17232#64) 12880) := by
  ac_rfl

theorem call_computeAt_placed_sepWPp [LibsignalPlacement]
    {ext : String → Option (State → State)} {A : RustAlloc}
    {ret_pc ret fsp : BitVec 64}
    {s0 s : State} {p_coeffs : BitVec 64} {poly : LibsignalSpqrV1.Poly} {x_gf : GF16}
    {F P R : SepProp} {Q : State → SepProp → Prop}
    (hcall : subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 371)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hfsp_al : fsp &&& 0xf#64 = 0#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = p_coeffs)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 poly.coefficients.length)
    (hx2 : (s.readReg64 Reg.x2).truncate 16 = x_gf.value)
    (hlen : 2 * poly.coefficients.length + 2 ≤ 2 ^ 63)
    (hP : P = (gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt fsp computeAtStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.trace = s0.trace →
      (sf.readReg64 Reg.x0).truncate 16 = (computeAtPure poly x_gf).value →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        ((gf16SliceAt p_coeffs poly.coefficients ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt fsp computeAtStack) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, hfsp_al]
  refine call_panic_lscl_sepWPp hcall hcl (x := { p_coeffs := p_coeffs, poly := poly, x := x_gf })
    (φ := s.readReg64 Reg.x0 = p_coeffs ∧
      s.readReg64 Reg.x1 = BitVec.ofNat 64 poly.coefficients.length ∧
      (s.readReg64 Reg.x2).truncate 16 = x_gf.value ∧
      2 * poly.coefficients.length + 2 ≤ 2 ^ 63)
    (T := gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗ stackAt fsp computeAtStack)
    hpc hrun hsp_al hlr htr
    (by simp only [computeAtPlacedSpec, hsp_eq])
    ⟨hx0, hx1, hx2, hlen⟩
    hP
    (fun _ => rfl)
    (fun _ _ _ _ hm => by simp [computeAtPlacedSpec, satisfies_pure_sepConj] at hm)
    (fun sf hpcf hrunf hspf hcsf hclf => ?_)
  have hspf' : sf.sp = fsp := hspf.trans hsp_eq
  conv => arg 4; simp only [computeAtPlacedSpec, hsp_eq, sepConj_assoc]
  apply SepWPp.pure_left
  rintro ⟨htrf, hx0f⟩
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (hnext sf hpcf hrunf hspf' hcsf hclf (htrf.trans htr) hx0f)
  ac_rfl

/-! ## 2. Single Iteration of the `Polys` Loop (`+136..+216 -> +108..+132`) -/

set_option maxHeartbeats 800000 in
theorem polysLoop_step_placed_sepWPp [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (x : PolyNextChunkGhost) (polys : List LibsignalSpqrV1.Poly) (hlen_polys : polys.length = 16)
    (out_ptr : BitVec 64) (R : SepProp)
    {Q : State → SepProp → Prop}
    (i rem : Nat) (hrem_eq : i + (rem + 1) = 16)
    (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (blkPl_416).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1))
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hnext : ∀ sf : State,
      sf.pc = (if rem == 0 then
          (blkPl_416).base + 4484#64
        else
          (blkPl_416).base + 136#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * (i + 1) + 24) →
      sf.readReg64 .x22 = BitVec.ofNat 64 rem →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
        ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 (i + 1)) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPolysTag) ∗
       polyListOf A (x.encA + 8#64) polys ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
       localFrameRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hi16 : i < 16 := by omega
  have hi_len : i < polys.length := by omega
  have hcomp : subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 371) (withLsCodeLoaded lsmpl (computeAtPlacedSpec A)) :=
    ls_subroutine_ok_of_block
      (computeAt_placed_ok A ext hA.handle_error hA.shim hA.alloc hA.realloc hA.dealloc)
  clear hA
  rw [polyListOf_split_idx A (x.encA + 8#64) polys i hi_len]
  apply SepWPp.fold (polyOf_unfold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len)) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_left; intro cap
  apply sepWPp_exists_left; intro ptr
  have hpure_pull :
      ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
        (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest =
          ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_pull]
  apply SepWPp.pure_left; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [polyBufBody_eq_slice_rest A cap ptr (polys[i]'hi_len) hlen_cap]
  have hlen_bound : 2 * (polys[i]'hi_len).coefficients.length + 2 ≤ 2 ^ 63 :=
    polyCoefficients_len_bound_of_cap hlen_cap hcap_bound
  refine sepWPp_of_sepWP_lscl (mid := lsmpl.base 371) hcl ?_
  wp_steps 3
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl_call
  rw [stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
  have hsp_al : s0.sp - 1200#64 &&& 15#64 = 0#64 := by revert hsp0; bv_bits
  refine call_computeAt_placed_sepWPp hcomp hcl_call
    (ret_pc := (blkPl_416).base + 148#64)
    (x_gf := GF16.new (x.enc.idx.setWidth 16))
    ?_ ?_ ?_ hsp_al ?_ ?_ ?_ ?_ ?_ hlen_bound
    (computeAt_pre_split_placed ptr (polys[i]'hi_len) (s0.sp - 1200#64) A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    ?_
  · wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using htr
  · wp_norm_lhs
  · wp_norm_lhs
  · simp [GF16.new, arm64_norm, wp_norm, hx27]
  intro sf1 hpc1 hrun1 hsp1' hcs1 hcl1 htr1' hx0_1
  rcases hcs1 with ⟨_, _, hx21_cs, hx22_cs, _, hx24_cs, _, _, hx27_cs, _, _, hvregs_cs⟩
  have hvregs_1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by
    rw [hvregs_cs]; simpa [arm64_norm, wp_norm] using hvregs
  have hx21_1 : sf1.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24) := by
    rw [Reg.x21, hx21_cs]; simpa [arm64_norm, wp_norm] using hx21
  have hx22_1 : sf1.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) := by
    rw [Reg.x22, hx22_cs]; simpa [arm64_norm, wp_norm] using hx22
  have hx24_1 : sf1.readReg64 .x24 = x.encA := by
    rw [Reg.x24, hx24_cs]; simpa [arm64_norm, wp_norm] using hx24
  have hx27_1 : sf1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 := by
    rw [Reg.x27, hx27_cs]; simpa [arm64_norm, wp_norm] using hx27
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_sub_one_beq_zero (rem := rem) (by omega) with ⟨hsubs_z1, hsubs_z2⟩
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  refine sepWPp_of_sepWP_lscl
    (mid := if rem == 0 then (blkPl_416).base + 4484#64 else (blkPl_416).base + 136#64) hcl1 ?_
  apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
  apply sepWP_exists_left_sep; intro b0
  apply sepWP_exists_left_sep; intro b1
  wp_steps 20
  have hb0_eq :
      BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5))) >>> 8) =
        BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8) :=
    lsr8_trunc8_of_trunc16 hx0_1
  have hb1_eq :
      BitVec.zeroExtend 8 (sf1.readReg64 (Reg.gpr 0#5)) =
        BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value :=
    trunc8_of_trunc16 hx0_1
  wp_conv_pre => rw [hb0_eq, hb1_eq]
  have hfold_bytes :
      (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value) ⊢
        (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 (i + 1)) := by
    rw [chunkPolysBytes_zero_succ (x.enc.idx.setWidth 16) polys i hi_len]
    exact pointsToBytes_append_two_bytes out_ptr
      (chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) i
      (chunkPolysBytes_length (x.enc.idx.setWidth 16) polys 0 i) _ _
  apply SepWP.fold hfold_bytes (by sep_focus)
  have hfold_poly :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (polys[i]'hi_len).coefficients.length) ∗
        gf16SliceAt ptr (polys[i]'hi_len).coefficients ∗
        polyBufRest A cap ptr (polys[i]'hi_len) ⊢
        polyOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len) :=
    polyOf_fold A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) cap ptr (polys[i]'hi_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_poly (by sep_focus)
  have hfold_list :
      polyListOf A (x.encA + 8#64) (polys.take i) ∗
        polyOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len) ∗
        polyListOf A ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (polys.drop (i + 1)) ⊢
        polyListOf A (x.encA + 8#64) polys := by
    rw [← polyListOf_split_idx A (x.encA + 8#64) polys i hi_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  have hfold_stk :
      memRegion (s0.sp - 18432#64) 12880 ∗
        stackAt (s0.sp - 1200#64) computeAtStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    have hsub : s0.sp - 18432#64 = (s0.sp - 1200#64) - 17232#64 := by bv_omega
    rw [hsub, ← stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
    exact Entails.refl _
  apply SepWP.fold hfold_stk (by sep_focus)
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hsubs_z1, hsubs_z2])
    (by wp_norm_lhs) ?_
  intro hcl_end
  refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; ac_rfl))
    (hnext _ ?_ (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1')
      (by simpa [arm64_norm, wp_norm] using htr1')
      (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hvregs_1])
      hcl_end
      (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx21_1])
      (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx22_1])
      (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx24_1])
      (by simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hx27_1]))
  simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hsubs_z1, hsubs_z2]

/-! ## 3. Full 16-Iteration `Polys` Loop and `EncoderState::Polys` Path -/

theorem polysLoop_placed_sepWPp [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (x : PolyNextChunkGhost) (polys : List LibsignalSpqrV1.Poly) (hlen_polys : polys.length = 16)
    (out_ptr : BitVec 64) (R : SepProp)
    {Q : State → SepProp → Prop}
    (s0 : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64) :
    ∀ (rem i : Nat) (hrem_eq : i + (rem + 1) = 16) (s : State),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_416).base + 136#64 →
      s.status = .Running →
      s.sp = s0.sp - 1200#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24) →
      s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x24 = x.encA →
      s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      (∀ sf : State,
        sf.pc = (blkPl_416).base + 4484#64 →
        sf.status = .Running →
        sf.sp = s0.sp - 1200#64 →
        sf.trace = s0.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.readReg64 .x20 = 32#64 →
        sf.readReg64 .x24 = x.encA →
        sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
          ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 16) ∗
           A.live out_ptr 32 1 ∗
           memRegion x.outA chunkSize ∗
           (x.encA ↦₆₄ polyEncoderPolysTag) ∗
           polyListOf A (x.encA + 8#64) polys ∗
           ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
           memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
           (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
           (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
           (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
           (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
           localFrameRest (s0.sp - 1200#64) ∗
           savedCells s0 ∗
           tokenInitPlacedAt ∗
           reduceTablePlacedAt ∗
           A.pool ∗
           stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
        ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
  | 0, i, hrem_eq, s, hcl, hpc, hrun, hsp, htr, hvregs, hx21, hx22, hx24, hx27, hdone => by
    have hi15 : i = 15 := by omega
    subst hi15
    refine polysLoop_step_placed_sepWPp A ext hA x polys hlen_polys out_ptr R 15 0 hrem_eq
      s0 s hcl hsp0 hpc hrun hsp htr hvregs hx21 hx22 hx24 hx27 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hcl_f hx20_f _hx21_f _hx22_f hx24_f hx27_f
    simp only [beq_self_eq_true, ite_true] at hpc_f
    change sf.readReg64 .x20 = 32#64 at hx20_f
    refine SepWPp.weaken_pre ?_ (hdone sf hpc_f hrun_f hsp_f htr_f hvregs_f hcl_f hx20_f hx24_f hx27_f)
    rw [show 32 - 2 * (15 + 1) = 0 from rfl, memRegion_zero,
        show BitVec.ofNat 64 (2 * (15 + 1)) = 32#64 from rfl]
    exact Entails.of_eq (by ac_rfl)
  | r + 1, i, hrem_eq, s, hcl, hpc, hrun, hsp, htr, hvregs, hx21, hx22, hx24, hx27, hdone => by
    refine polysLoop_step_placed_sepWPp A ext hA x polys hlen_polys out_ptr R i (r + 1) hrem_eq
      s0 s hcl hsp0 hpc hrun hsp htr hvregs hx21 hx22 hx24 hx27 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hcl_f _hx20_f hx21_f hx22_f hx24_f hx27_f
    have hne0 : (r + 1 == 0) = false := rfl
    simp only [hne0, Bool.false_eq_true, ite_false] at hpc_f
    exact polysLoop_placed_sepWPp A ext hA x polys hlen_polys out_ptr R s0 hsp0
      r (i + 1) (by omega) sf hcl_f hpc_f hrun_f hsp_f htr_f hvregs_f hx21_f hx22_f hx24_f hx27_f hdone

set_option maxHeartbeats 800000 in
theorem nextChunk_polys_placed_sepWPp [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (x : PolyNextChunkGhost) (polys : List LibsignalSpqrV1.Poly)
    (hs_polys : x.enc.s = .polys polys)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       polyEncoderAt A x.encA x.enc ∗
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
  unfold polyEncoderAt encoderStateAt
  rw [hs_polys]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ P_list ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; intro hlen_polys
  have hlen16 : polys.length = 16 := hlen_polys
  have henc_eq : x.enc = { idx := x.enc.idx, s := .polys polys } := by
    cases h : x.enc; simp_all
  have hnc := nextChunk_polys_eq (idx := x.enc.idx) hlen16
  rw [← henc_eq] at hnc
  rw [hnc, Except.ok.injEq, Prod.mk.injEq] at hnext
  rcases hnext with ⟨henc'_eq, hchunk_eq⟩
  have hdata_eq : x.chunk.data.toList = chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 16 := by
    rw [← hchunk_eq]; rfl
  have hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16 := by
    rw [← hchunk_eq]
  have hidx_enc' : x.enc'.idx = x.enc.idx + 1#32 := by
    rw [← henc'_eq]
  have hs_enc' : x.enc'.s = .polys polys := by
    rw [← henc'_eq]
  refine prologue_lscl_placed_sepWPp A ext hA x polyEncoderPolysTag
    (polyListOf A (x.encA + polyEncoderVecsOff) polys) R s0 hcl0 hpc hrun hsp0 hx0 hx8 ?_
  intro s1 out_ptr hout_ne hpc1 hrun1 hsp1 htr1 hvregs1 hcl1 hx9_1 _hx19_1 hx24_1 hx27_1 _hx29_1
  change s1.readReg64 .x9 = 1#64 at hx9_1
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 136#64) hcl1 ?_
  wp_steps 4
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl2
  have hinit_buf :
      memRegion out_ptr 32 =
        (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 0) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (32 - 2 * 0) := by
    simp [chunkPolysBytes, pointsToBytes_nil, emp_sepConj]
  refine SepWPp.weaken_pre (Entails.of_eq (by rw [hinit_buf, sepConj_assoc])) ?_
  refine polysLoop_placed_sepWPp A ext hA x polys hlen16 out_ptr R s0 hsp0 15 0 rfl _ hcl2
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp1
  · simpa [arm64_norm, wp_norm] using htr1
  · simpa [arm64_norm, wp_norm] using hvregs1
  · simp [arm64_norm, wp_norm, hx24_1]
  · rfl
  · simpa [arm64_norm, wp_norm] using hx24_1
  · simpa [arm64_norm, wp_norm] using hx27_1
  intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _hcl_f hx20_f hx24_f hx27_f
  apply SepWPp.of_sepWP_ret
  have henc'_state :
      (x.encA ↦₆₄ polyEncoderPolysTag) ∗ polyListOf A (x.encA + 8#64) polys ⊢
        encoderStateAt A x.encA x.enc'.s := by
    rw [hs_enc']
    unfold encoderStateAt
    dsimp only [polyEncoderVecsOff]
    have htrue : (polys.length = NUM_POLYS) = True := propext ⟨fun _ => trivial, fun _ => hlen_polys⟩
    rw [htrue, pure_true, emp_sepConj]
    exact Entails.refl _
  apply SepWP.fold henc'_state (by sep_focus)
  rw [← hdata_eq]
  refine SepWP.weaken_pre (Entails.of_eq (by
    simp only [arm64_norm]
    ac_rfl))
    (epilogue_placed_sepWP A ext hA x R s0 sf out_ptr hout_ne hidx_chunk hidx_enc'
      hpc_f hrun_f hsp_f hsp0 htr_f hx20_f hx24_f ?_ hvregs_f)
  rw [hx27_f, BitVec.setWidth_setWidth_of_le (x.enc.idx.setWidth 16) (by decide)]
  rfl

end CryptoVerification.SpqrV1.Poly.NextChunk
