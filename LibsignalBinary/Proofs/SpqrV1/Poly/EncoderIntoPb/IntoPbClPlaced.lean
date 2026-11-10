/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.OuterPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbClPlaced
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder>::into_pb` (Block `375`): `withLsCodeLoaded` Proof

Relocatable `[LibsignalPlacement]` verification of `<PolyEncoder>::into_pb` threading
`withLsCodeLoaded lsmpl` across both `drop_glue::<[Poly; 16]>` (Block `265`) and Block `375`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.EncoderIntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
  (vecGF16Of vecGF16ListOf pointListOf_eq_vecGF16ListOf polyListOf_eq_vecGF16ListOf
   dropGluePoly16Stack DropGluePoly16Ghost dropGluePoly16Spec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  bv384_toNat bv8_toNat
  off_8_add_8 off_16_add_8 off_24_add_8 off_32_add_8 off_40_add_8
  off_48_add_8 off_56_add_8 off_64_add_8 off_72_add_8 off_80_add_8 off_88_add_8
  off_96_add_8 off_104_add_8 off_112_add_8 off_120_add_8 off_128_add_8
  off_136_add_8 off_144_add_8 off_152_add_8 off_160_add_8 off_168_add_8
  off_176_add_8 off_184_add_8 off_192_add_8 off_200_add_8 off_208_add_8
  sub_224_add_224 truncate_32_zeroExtend_64 setWidth_32_setWidth_64
  fp_sub_48 fp_sub_32 fp_sub_24 fp_sub_16 fp_sub_8 fp_sub_40
  fp_sub_48_int fp_sub_32_int fp_sub_24_int fp_sub_16_int fp_sub_8_int fp_sub_40_int
  sp_add_56_add_8 sp_add_80_add_8 sp_add_104_add_8
  ofNat_add_one madd_24_eq

private def withSaved19_20_setLr (s0 : State) (encA out lr : BitVec 64) : State :=
  ((s0.writeReg64 .x19 encA).writeReg64 .x20 out).writeReg64 (Reg.gpr 30#5) lr

private theorem withSaved19_20_setLr_lr (s0 : State) (encA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 encA out lr).readReg64 (Reg.gpr 30#5) = lr := by
  simp [withSaved19_20_setLr, wp_norm]

private theorem withSaved19_20_setLr_x19 (s0 : State) (encA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 encA out lr).readReg64 .x19 = encA := by
  simp [withSaved19_20_setLr, wp_norm]

private theorem withSaved19_20_setLr_x20 (s0 : State) (encA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 encA out lr).readReg64 .x20 = out := by
  simp [withSaved19_20_setLr, wp_norm]

private theorem withSaved19_20_setLr_trace (s0 : State) (encA out lr : BitVec 64) :
    (withSaved19_20_setLr s0 encA out lr).trace = s0.trace := rfl

private theorem withSaved19_20_setLr_vregs (s0 : State) (encA out lr : BitVec 64) :
    calleeSavedVRegs (withSaved19_20_setLr s0 encA out lr) = calleeSavedVRegs s0 := rfl

private theorem withSaved19_20_setLr_onPanic (s0 sf : State) (encA out lr : BitVec 64) :
    intoPbOnPanic (withSaved19_20_setLr s0 encA out lr) sf = intoPbOnPanic s0 sf := rfl

private theorem sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q_mid : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem →
      Q_mid sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hent, hqm⟩ hclm =>
      SepWPp.weaken_pre hent (h2 sm hpcm hrunm hclm hqm))

/-- Placed epilogue of `<PolyEncoder>::into_pb` (`+616` to `s0.lr`) with `withLsCodeLoaded` on `hdrop`. -/
theorem into_pb_epilogue_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec A)))
    (s0 : State) (fsp out encA : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 224#64))
    (idx hi48 : BitVec 32) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (vecs : List (List GF16)) (hvecs : vecs.length = NUM_POLYS)
    (w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w11 w12 w13 w14 w15 d0 d1 d2 d3 d4 d5 d6 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_375).base + 616#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = encA) (hx20 : s.readReg64 .x20 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      ((fsp ↦₆₄ w0) ∗ ((fsp + 8#64) ↦₆₄ w1) ∗ ((fsp + 16#64) ↦₆₄ w2) ∗
        ((fsp + 24#64) ↦₆₄ w3) ∗ ((fsp + 32#64) ↦₆₄ w4) ∗ ((fsp + 40#64) ↦₆₄ w5) ∗
        ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ hi48) ∗ ((fsp + 56#64) ↦₆₄ w7) ∗
        ((fsp + 64#64) ↦₆₄ w8) ∗ ((fsp + 72#64) ↦₆₄ w9) ∗ ((fsp + 80#64) ↦₆₄ w10) ∗
        ((fsp + 88#64) ↦₆₄ w11) ∗ ((fsp + 96#64) ↦₆₄ w12) ∗ ((fsp + 104#64) ↦₆₄ w13) ∗
        ((fsp + 112#64) ↦₆₄ w14) ∗ ((fsp + 120#64) ↦₆₄ w15) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        memRegion encA 8 ∗ vecGF16ListOf A (encA + 8#64) vecs ∗ memRegion (encA + 392#64) 8 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sf P' =>
        (P' ⊢
          (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
          ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
          ((out + 48#64) ↦₃₂ idx) ∗ memRegion (out + 52#64) 4 ∗ memRegion encA 400 ∗
          A.pool ∗ stackAt s0.sp encoderIntoPbStack ∗ Frame) ∧
        sf.sp = s0.sp ∧
        sf.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) ∧
        sf.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
        sf.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
        sf.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
        sf.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
        sf.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
        sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
        sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
        sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
        sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
        sf.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5) ∧
        sf.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) := by
  conv => arg 4; rw [← sepConj_assoc ((fsp + 48#64) ↦₃₂ idx) ((fsp + 52#64) ↦₃₂ hi48),
    pointsTo32_off48_merge64 fsp idx hi48]
  wp_steps_lscl (lsmpl.base 265)
  have hdrop_call := DecoderPb.subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop ‹LibsignalCodeLoaded lsmpl _›
  simp only [withMemEq, dropGluePoly16Spec, BitVec.ofNat_eq_ofNat] at hdrop_call
  wp_call hdrop_call (⟨encA + 8#64, vecs⟩ : DropGluePoly16Ghost)
  wp_steps
  have hsp_ret : fsp + 224#64 = s0.sp := by rw [hfsp.eq]; bv_omega
  conv => arg 3; rw [hsp_ret]
  conv => arg 4; rw [hsp]
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (by ac_rfl))
      (into_pb_epilogue_post_entails A s0.sp fsp out encA hfsp.eq idx hi48
        w0 w1 w2 w3 w4 w5 w7 w8 w9 w10 w11 w12 w13 w14 w15
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
        (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
        Frame)) ?_
  wp_done

/-- Placed prologue of `<PolyEncoder>::into_pb` (`+0 -> +88`, or OOM panic at `+692`)
    threading `LibsignalCodeLoaded lsmpl`. -/
theorem into_pb_prologue_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop} {R : SepProp}
    (s0 : State) (fsp out encA : BitVec 64) (hfsp : HiddenEq fsp (s0.sp - 224#64))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (idx : BitVec 32)
    (v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : BitVec 64) (Frame : SepProp)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_375).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = out) (hx1 : s0.readReg64 .x1 = encA)
    (hnext : ∀ (sm : State) (ptr_points ptr_polys : BitVec 64),
      LibsignalCodeLoaded lsmpl sm.mem →
      ptr_points ≠ 0 → ptr_polys ≠ 0 →
      sm.pc = (blkPl_375).base + 88#64 → sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x29 = fsp + 128#64 → sm.readReg64 .x19 = encA → sm.readReg64 .x20 = out →
      sm.readReg64 .x21 = ptr_points → sm.readReg64 .x0 = ptr_polys →
      sm.readReg64 .x22 = idx.zeroExtend 64 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (Frame ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
          memRegion (encA + 392#64) 8 ∗
          A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
          A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
          A.pool ∗ stackAt fsp allocHookStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s0
      (((fsp + 128#64) ↦₆₄ v16) ∗ ((fsp + 136#64) ↦₆₄ v17) ∗
        ((fsp + 144#64) ↦₆₄ v18) ∗ ((fsp + 152#64) ↦₆₄ v19) ∗
        ((fsp + 160#64) ↦₆₄ v20) ∗ ((fsp + 168#64) ↦₆₄ v21) ∗
        ((fsp + 176#64) ↦₆₄ v22) ∗ ((fsp + 184#64) ↦₆₄ v23) ∗
        ((fsp + 192#64) ↦₆₄ v24) ∗ ((fsp + 200#64) ↦₆₄ v25) ∗
        ((fsp + 208#64) ↦₆₄ v26) ∗ ((fsp + 216#64) ↦₆₄ v27) ∗
        ((encA + 392#64) ↦₃₂ idx) ∗ memRegion (encA + 396#64) 4 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  simp only [sessionShimSpec] at hshim
  simp only [rustAllocSpec] at halloc
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay384 : LayoutOk 384 8 := ⟨by decide, hpow8, by decide⟩
  dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hnext ⊢
  refine SepWPp.seq_frozen (mid := (blkPl_375).base + 60#64)
    (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl0 ?_
  wp_step
  conv => arg 3; simp only [← hfsp.eq]
  wp_steps
  wp_apply
  wp_steps
  conv => arg 4; simp only [← h_1]
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl_sf1
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun htr_oom => ?_
    refine SepWPp.seq_clean (mid := (blkPl_375).base + 692#64)
      (P_mid :=
        A.pool ∗ stackAt sf.sp allocHookStack ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        ((encA + 392#64) ↦₃₂ idx) ∗ memRegion (encA + 396#64) 4 ∗ Frame)
      (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
      (by wp_steps; wp_done)
      (fun sm hpcm hrunm htrm => into_pb_panic_692_placed h_panic s0 sm _ R hpcm hrunm htrm)
  · have hoom1_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hoom1
    conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨_, htr_ok1⟩ => ?_
    let ptr_points := sf_1.readReg64 (Reg.gpr 0#5)
    refine SepWPp.seq_frozen (mid := (blkPl_375).base + 84#64)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl_sf1 ?_
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl_sf3
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      refine sepWPp_pure_mid fun htr_oom2 => ?_
      refine SepWPp.seq_clean (mid := (blkPl_375).base + 692#64)
        (P_mid :=
          A.pool ∗ stackAt sf_2.sp allocHookStack ∗
          A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
          ((encA + 392#64) ↦₃₂ idx) ∗ memRegion (encA + 396#64) 4 ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent])
        (by wp_steps; wp_done)
        (fun sm hpcm hrunm htrm => into_pb_panic_692_placed h_panic s0 sm _ R hpcm hrunm htrm)
    · have hoom2_beq : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom2
      conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨_, htr_ok2⟩ => ?_
      have hsp_sf2 : sf_2.sp = fsp := h_23.trans (hsp_sf.trans h_1)
      conv => arg 4; simp only [hsp_sf2]
      let ptr_polys := sf_3.readReg64 (Reg.gpr 0#5)
      refine sepWPp_seq_clean_lscl (mid := (blkPl_375).base + 88#64)
        (P_mid :=
          Frame ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
          memRegion (encA + 392#64) 8 ∗
          A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
          A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
          A.pool ∗ stackAt fsp allocHookStack)
        (Q_mid := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x29 = fsp + 128#64 ∧
          sm.readReg64 .x19 = encA ∧
          sm.readReg64 .x20 = out ∧
          sm.readReg64 .x21 = ptr_points ∧
          sm.readReg64 .x0 = ptr_polys ∧
          sm.readReg64 .x22 = idx.zeroExtend 64 ∧
          sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        hcl_sf3 ?_ ?_
      · wp_steps
        have htail := encA_tail_rejoin_8 encA idx
        refine SepWP.weaken_pre (P' := (((encA + 392#64) ↦₃₂ idx) ∗ memRegion (encA + 396#64) 4) ∗
          (Frame ∗ ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
            A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
            A.pool ∗ stackAt fsp allocHookStack)) (Entails.of_eq (by ac_rfl)) ?_
        refine SepWP.weaken_pre (Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))) ?_
        wp_done
      · intro sm hpcm hrunm hclm ⟨hspm, hx29m, hx19m, hx20m, hx21m, hx0m, hx22m, htrm, hvregsm⟩
        exact hnext sm ptr_points ptr_polys hclm hoom1 hoom2 hpcm hrunm hspm hx29m hx19m hx20m hx21m hx0m hx22m htrm hvregsm

/-- Relocatable `withLsCodeLoaded` verification of `<PolyEncoder>::into_pb` (Block `375`). -/
theorem encoder_into_pb_cl_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdrop : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec A))) :
    subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (blkPl_375).base (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)) := by
  have hshim_raw : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hshim_sat
  have halloc_raw : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem halloc_sat
  apply subroutine_ok_of_sepWPp
  intro ⟨out, encA, ⟨idx, encState⟩⟩ R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [encoderIntoPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion out protoPolynomialEncoderSize ∗
      polyEncoderAt A encA { idx := idx, s := encState } ∗
      A.pool ∗ stackAt s0.sp encoderIntoPbStack,
    R, by simpa [sepConj_assoc] using hmem, ?_⟩
  dsimp only [withLsCodeLoaded, encoderIntoPbSpec, polyEncoderAt, polyEncoderIdxOff, polyEncoderPadOff,
    polyEncoderPadSize, protoPolynomialEncoderSize, polyEncoderSize, BitVec.ofNat_eq_ofNat] at *
  let fsp := s0.sp - 224#64
  have hfsp : HiddenEq fsp (s0.sp - 224#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 224#64 hsp0 (by decide)
  conv => arg 4; rw [stackAt_encoderIntoPb_split s0.sp, ← hfsp.eq, stackAt_dropGluePoly16_split_bottom fsp]
  refine SepWPp.weaken_pre (P' :=
      memRegion out 56 ∗ cells fsp 28 ∗
      encoderStateAt A encA encState ∗ ((encA + 392#64) ↦₃₂ idx) ∗ memRegion (encA + 396#64) 4 ∗
      A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack)
    (Entails.of_eq (by ac_rfl)) ?_
  conv => arg 4; simp only [memRegion_56_split out, cells28_fsp_eq fsp, sepConj_assoc, sepExists_sepConj_left]
  conv => arg 4; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun d3 => SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 =>
    SepWPp.exists_elim fun d6 => SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 =>
    SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 => SepWPp.exists_elim fun v4 =>
    SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
    SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 => SepWPp.exists_elim fun v10 =>
    SepWPp.exists_elim fun v11 => SepWPp.exists_elim fun v12 => SepWPp.exists_elim fun v13 =>
    SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v18 => SepWPp.exists_elim fun v19 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v21 => SepWPp.exists_elim fun v22 =>
    SepWPp.exists_elim fun v23 => SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v25 =>
    SepWPp.exists_elim fun v26 => SepWPp.exists_elim fun v27 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (into_pb_prologue_cl_placed hshim_raw halloc_raw h_panic s0 fsp out encA hfsp hfsp_align idx
      v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
      (encoderStateAt A encA encState ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
        ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗ ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        memRegion (fsp - 4128#64) 32)
      hcl0 ‹_› ‹_› ‹_› ‹_› ?_)
  intro s1 ptr_points ptr_polys hcl1 hptr_pts hptr_polys hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx0_1 hx22_1 htr1 hvregs1
  let s_ref616 := withSaved19_20_setLr s0 encA out ((blkPl_375).base + 616#64)
  cases encState with
  | points points =>
    dsimp only [encoderStateAt, polyEncoderPointsTag, polyEncoderVecsOff, BitVec.ofNat_eq_ofNat]
    conv => arg 4; simp only [sepConj_assoc]
    refine sepWPp_elim_pure fun ⟨hpts_len, _⟩ => ?_
    rw [pointListOf_eq_vecGF16ListOf]
    have hrem_len : (points.map Point.value).length = 16 := by
      simp [hpts_len, NUM_POLYS, CHUNK_SIZE]
    have hrem_ne : points.map Point.value ≠ [] := by
      intro h; simp [h] at hrem_len
    have hdisp := into_pb_dispatch_points_placed (ext := ext)
      s0 fsp out encA ptr_points ptr_polys hfsp_align idx v0 v1 v2 v3 v4 v5 v6 s1
      (((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗
        ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        vecGF16ListOf A (encA + 8#64) (points.map Point.value) ∗
        memRegion (encA + 392#64) 8 ∗
        A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
        A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx0_1 hx22_1 htr1 hvregs1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean_lscl hcl1 hdisp ?_)
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, htr2, hvregs2⟩
    let Frame_pts : SepProp :=
      ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
        ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗
        ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        memRegion encA 8 ∗ memRegion (encA + 392#64) 8 ∗
        A.live ptr_points 384 8 ∗
        A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
        memRegion (fsp - 4128#64) 32
    let Q616_pts : State → SepProp → Prop := fun s3 P3 =>
      ∃ w56 w64 w72 : BitVec 64,
        (P3 ⊢
          (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
            ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
            arrayAt (fun cs addr => vecGF16Of A addr cs) 24 (encA + 8#64) (points.map Point.value) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_points
              ((points.map Point.value).map serializeGF16List) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame_pts) ∧
        s3.sp = fsp ∧ s3.readReg64 .x29 = fsp + 128#64 ∧
        s3.readReg64 .x19 = encA ∧ s3.readReg64 .x20 = out ∧
        s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0
    have hloop := points_outer_loop_placed (R := R) (Q := Q616_pts)
      hshim_raw halloc_raw h_panic s_ref616 fsp ptr_points hfsp_align
      (points.map Point.value) hrem_ne 0 (by omega) v7 v8 v9 s2 Frame_pts
      hpc2 hrun2 hsp2 hx29_2
      (by simpa [s_ref616, withSaved19_20_setLr_x19] using hx19_2)
      (by simpa [s_ref616, withSaved19_20_setLr_x20] using hx20_2)
      (by simpa [s_ref616, withSaved19_20_setLr_x19] using hx22_2)
      hx23_2 hx24_2 hx25_2
      (by simpa [s_ref616, withSaved19_20_setLr_trace] using htr2)
      (by simpa [s_ref616, withSaved19_20_setLr_vregs] using hvregs2)
    dsimp only [s_ref616] at hloop
    simp only [withSaved19_20_setLr_lr, withSaved19_20_setLr_x19, withSaved19_20_setLr_x20,
      withSaved19_20_setLr_trace, withSaved19_20_setLr_vregs, withSaved19_20_setLr_onPanic,
      Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrem_len] at hloop
    change _ → SepWPp _ _ _ _ _ _ at hloop
    refine DecoderPb.sepWPp_seq_mid_lscl hcl2
      (SepWPp.weaken_pre (by dsimp only [vecGF16ListOf, Frame_pts]; exact Entails.of_eq (by ac_rfl))
        (hloop fun s3 w56 w64 w72 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3 =>
          SepWPp.done hpc3 hrun3 ⟨w56, w64, w72, Entails.refl _, hsp3, hx29_3, hx19_3, hx20_3, htr3, hvregs3⟩))
      ?_
    intro s3 P3 hpc3 hrun3 hcl3 ⟨w56, w64, w72, hent3, hsp3, hx29_3, hx19_3, hx20_3, htr3, hvregs3⟩
    refine SepWPp.weaken_pre hent3 ?_
    have hep := into_pb_epilogue_cl_placed hdrop s0 fsp out encA hfsp idx (v6.extractLsb' 32 32)
      hfsp_align (points.map Point.value) (by simp [hpts_len])
      16#64 ptr_points 16#64 16#64 ptr_polys 0#64 w56 w64 w72 v10 v11 v12 v13 v14 v15
      d0 d1 d2 d3 d4 d5 d6 s3
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_points
          ((points.map Point.value).map serializeGF16List) ∗
        A.live ptr_points 384 8 ∗
        A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384)
      hcl3 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3
    refine SepWPp.weaken_pre (by
      dsimp only [Frame_pts, vecGF16ListOf]
      rw [stackAt_dropGluePoly16_split_bottom fsp]
      exact Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hep ?_)
    intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
    have hpost_pts := protoPolynomialEncoderAt_points_entails A out ptr_points ptr_polys idx points
      hpts_len hptr_pts hptr_polys
    refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
      hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩⟩
    exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans (sepConj_mono_left (Q := memRegion encA 400 ∗ A.pool ∗ stackAt s0.sp encoderIntoPbStack) hpost_pts)
        (Entails.of_eq (by ac_rfl))))
  | polys polys =>
    dsimp only [encoderStateAt, polyEncoderPolysTag, polyEncoderVecsOff, BitVec.ofNat_eq_ofNat]
    conv => arg 4; simp only [sepConj_assoc]
    refine sepWPp_elim_pure fun hpolys_len => ?_
    rw [polyListOf_eq_vecGF16ListOf]
    have hrem_len : (polys.map LibsignalSpqrV1.Poly.coefficients).length = 16 := by
      simp [hpolys_len, NUM_POLYS, CHUNK_SIZE]
    have hrem_ne : polys.map LibsignalSpqrV1.Poly.coefficients ≠ [] := by
      intro h; simp [h] at hrem_len
    have hdisp := into_pb_dispatch_polys_placed (ext := ext)
      s0 fsp out encA ptr_points ptr_polys hfsp_align idx v0 v1 v2 v3 v4 v5 v6 s1
      (((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗
        ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        vecGF16ListOf A (encA + 8#64) (polys.map LibsignalSpqrV1.Poly.coefficients) ∗
        memRegion (encA + 392#64) 8 ∗
        A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
        A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx0_1 hx22_1 htr1 hvregs1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean_lscl hcl1 hdisp ?_)
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx28_2, hx24_2, hx25_2, hx26_2, htr2, hvregs2⟩
    let Frame_polys : SepProp :=
      (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
        ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
        ((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        memRegion encA 8 ∗ memRegion (encA + 392#64) 8 ∗
        A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
        A.live ptr_polys 384 8 ∗
        memRegion (fsp - 4128#64) 32
    let Q616_polys : State → SepProp → Prop := fun s3 P3 =>
      ∃ w80 w88 w96 w104 w112 w120 : BitVec 64,
        (P3 ⊢
          ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 16#64) ∗
            ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 88#64) ↦₆₄ w88) ∗ ((fsp + 96#64) ↦₆₄ w96) ∗
            ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
            arrayAt (fun cs addr => vecGF16Of A addr cs) 24 (encA + 8#64)
              (polys.map LibsignalSpqrV1.Poly.coefficients) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_polys
              ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame_polys) ∧
        s3.sp = fsp ∧ s3.readReg64 .x29 = fsp + 128#64 ∧
        s3.readReg64 .x19 = encA ∧ s3.readReg64 .x20 = out ∧
        s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0
    have hloop := polys_outer_loop_placed (R := R) (Q := Q616_polys)
      hshim_raw halloc_raw h_panic s_ref616 fsp ptr_polys hfsp_align
      (polys.map LibsignalSpqrV1.Poly.coefficients) hrem_ne 0 (by omega) v10 v11 v12 v13 v14 v15 s2 Frame_polys
      hpc2 hrun2 hsp2 hx29_2
      (by simpa [s_ref616, withSaved19_20_setLr_x19] using hx19_2)
      (by simpa [s_ref616, withSaved19_20_setLr_x20] using hx20_2)
      (by simpa [s_ref616, withSaved19_20_setLr_x19] using hx22_2)
      hx23_2 hx28_2 hx24_2 hx25_2 hx26_2
      (by simpa [s_ref616, withSaved19_20_setLr_trace] using htr2)
      (by simpa [s_ref616, withSaved19_20_setLr_vregs] using hvregs2)
    dsimp only [s_ref616] at hloop
    simp only [withSaved19_20_setLr_lr, withSaved19_20_setLr_x19, withSaved19_20_setLr_x20,
      withSaved19_20_setLr_trace, withSaved19_20_setLr_vregs, withSaved19_20_setLr_onPanic,
      Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrem_len] at hloop
    change _ → SepWPp _ _ _ _ _ _ at hloop
    refine DecoderPb.sepWPp_seq_mid_lscl hcl2
      (SepWPp.weaken_pre (by dsimp only [vecGF16ListOf, Frame_polys]; exact Entails.of_eq (by ac_rfl))
        (hloop fun s3 w80 w88 w96 w104 w112 w120 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3 =>
          SepWPp.done hpc3 hrun3 ⟨w80, w88, w96, w104, w112, w120, Entails.refl _, hsp3, hx29_3, hx19_3, hx20_3, htr3, hvregs3⟩))
      ?_
    intro s3 P3 hpc3 hrun3 hcl3 ⟨w80, w88, w96, w104, w112, w120, hent3, hsp3, hx29_3, hx19_3, hx20_3, htr3, hvregs3⟩
    refine SepWPp.weaken_pre hent3 ?_
    have hep := into_pb_epilogue_cl_placed hdrop s0 fsp out encA hfsp idx (v6.extractLsb' 32 32)
      hfsp_align (polys.map LibsignalSpqrV1.Poly.coefficients) (by simp [hpolys_len])
      16#64 ptr_points 0#64 16#64 ptr_polys 16#64 v7 v8 v9 w80 w88 w96 w104 w112 w120
      d0 d1 d2 d3 d4 d5 d6 s3
      (A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_polys
          ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List) ∗
        A.live ptr_polys 384 8)
      hcl3 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3
    refine SepWPp.weaken_pre (by
      dsimp only [Frame_polys, vecGF16ListOf]
      rw [stackAt_dropGluePoly16_split_bottom fsp]
      exact Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hep ?_)
    intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
    have hpost_polys := protoPolynomialEncoderAt_polys_entails A out ptr_points ptr_polys idx polys
      hpolys_len hptr_pts hptr_polys
    refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
      hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩⟩
    exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans (sepConj_mono_left (Q := memRegion encA 400 ∗ A.pool ∗ stackAt s0.sp encoderIntoPbStack) hpost_polys)
        (Entails.of_eq (by ac_rfl))))

/-- `withLsCodeLoaded lsmpl (encoderIntoPbSpec A)` entails
    `withLsCodeLoaded lsmpl (encoderIntoPbSpecX A)` by framing the unused bottom stack region. -/
theorem encoderIntoPbSpecX_cl_of_encoderIntoPbSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (encoderIntoPbSpec A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (encoderIntoPbSpecX A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : encoderIntoPbStack ≤ encoderIntoPbStackX := by decide
  have hsplit : stackAt s0.sp encoderIntoPbStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encoderIntoPbStackX)
        (encoderIntoPbStackX - encoderIntoPbStack) ∗
        stackAt s0.sp encoderIntoPbStack := by
    have h1 := stackAt_split_bottom s0.sp encoderIntoPbStack
      (encoderIntoPbStackX - encoderIntoPbStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encoderIntoPbStackX)
      (encoderIntoPbStackX - encoderIntoPbStack) ∗ R
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded, encoderIntoPbSpecX, encoderIntoPbSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encoderIntoPbSpecX, encoderIntoPbSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [withLsCodeLoaded, encoderIntoPbSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `<spqr::encoding::polynomial::PolyEncoder>::into_pb` (Block `375`)
    satisfies `withLsCodeLoaded lsmpl (encoderIntoPbSpecX A)` under `[LibsignalPlacement]`. -/
theorem encoder_into_pb_cl_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdrop : subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec A))) :
    subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (blkPl_375).base (withLsCodeLoaded lsmpl (encoderIntoPbSpecX A)) :=
  encoderIntoPbSpecX_cl_of_encoderIntoPbSpec
    (encoder_into_pb_cl_placed_ok_ext h_panic hshim_sat halloc_sat hdrop)

end CryptoVerification.SpqrV1.Poly.EncoderIntoPb
