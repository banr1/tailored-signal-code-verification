/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoopExt
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack `.polys` Outer Loop for `<PolyEncoder>::from_pb`

Lifts `polys_alloc_12_15`, `polys_init_zero_headers`, `polys_elem_even_nonempty_step`,
`polys_elem_finish_step`, and `polys_outer_loop` to `AllocContracts4K`.
-/

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
  ofNat_succ_sub_one ofNat_succ_add_neg_one zeroExtend_setWidth32_setWidth8
  add_neg_64_eq_sub_64 add_neg_48_eq_sub_48 add_neg_32_eq_sub_32
  add_neg_24_eq_sub_24 add_neg_16_eq_sub_16
  fsp_928_sub_64 fsp_928_sub_48 fsp_928_sub_32 fsp_928_sub_24 fsp_928_sub_16
  fsp_896_add_9 fsp_896_add_16 fsp_864_add_7 fsp_864_add_23
  madd_24_eq mul_24_eq exists_pow_two_eq_two

local macro "polys_alloc_call" mid:term : tactic => `(tactic| (
  apply SepWPp.of_sepWP (mid := $mid)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
))

local macro "polys_oom_exit" hoom:ident hpanic:ident : tactic => `(tactic| (
  conv => arg 4; simp only [$hoom:ident, ↓reduceIte, sepConj_assoc]
  apply sepWPp_pure_mid; intro _
  refine $hpanic:ident _ _ ?_
  wp_steps
  exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, *])
))

/-! ## `.polys` Allocations 12..15 and Combined 16-Slot Initialization (`+556 -> +1204`) -/

theorem polys_alloc_12_15_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 848#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p12 p13 p14 p15 : BitVec 64),
      p12 ≠ 0#64 → p13 ≠ 0#64 → p14 ≠ 0#64 → p15 ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 940#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x0 = p15 → sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = p12 → sm.readReg64 .x26 = p13 →
      sm.readReg64 .x27 = p14 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
          A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk 2 2 := ⟨by omega, hpow2, by omega⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1696 := fun (s : State) (P : SepProp) => @sepWPp_panic_of_sepWP_1696 b ext Q s0 s P R
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 848 96
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1696 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  polys_alloc_call (entry + 864#64)
  by_cases hoom12 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · polys_oom_exit hoom12 hpanic1696
  · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr12⟩
    have hbeq12 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom12
    polys_alloc_call (entry + 888#64)
    by_cases hoom13 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · polys_oom_exit hoom13 hpanic1696
    · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; rintro ⟨_, htr13⟩
      have hbeq13 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom13
      polys_alloc_call (entry + 912#64)
      by_cases hoom14 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · polys_oom_exit hoom14 hpanic1696
      · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; rintro ⟨_, htr14⟩
        have hbeq14 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom14
        polys_alloc_call (entry + 936#64)
        by_cases hoom15 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · polys_oom_exit hoom15 hpanic1696
        · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; rintro ⟨_, htr15⟩
          have hbeq15 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom15
          apply SepWPp.of_sepWP (mid := entry + 940#64)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine SepWPp.weaken_pre
            (by simp only [h_1, h_23, h_45, h_67, hsp_sf, hsp_sf_1, hsp_sf_2, hsp_sf_3, hsp]; exact Entails.of_eq (by ac_rfl))
            (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
              (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
              hoom12 hoom13 hoom14 hoom15
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x0, *])
              (by simp only [arm64_norm, wp_norm, Reg.x19, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
              (by simp only [arm64_norm, wp_norm, Reg.x21, *]) (by simp only [arm64_norm, wp_norm, Reg.x23, *])
              (by simp only [arm64_norm, wp_norm, Reg.x24, *]) (by simp only [arm64_norm, wp_norm, Reg.x25, *])
              (by simp only [arm64_norm, wp_norm, Reg.x26, *]) (by simp only [arm64_norm, wp_norm, Reg.x27, *])
              (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, *])
              (by simp only [arm64_norm, wp_norm, *]))

theorem polys_init_zero_headers_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp out pbA polysPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 556#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1204#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x22 = 0#64 → sm.readReg64 .x23 = fsp + 864#64 →
      sm.readReg64 .x24 = polysPtr → sm.readReg64 .x28 = 0#64 →
      sm.readReg64 .x29 = fsp + 928#64 → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (cells fsp 7 ∗
          ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
          ((pbA + 32#64) ↦₆₄ polysPtr) ∗
          zeroPolySlotsAt A (fsp + 480#64) 16 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 4 ∗ cells (fsp + 32#64) 5 ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        cells (fsp + 480#64) 48 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (polys_alloc_0_3_4k hA s0 s fsp out pbA hfsp_align
      (cells fsp 4 ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗ Frame)
      R hpc hrun hsp hx0 hx1 htrace hvregs ?_)
  intro s1 p0 p1 p2 p3 hp0 hp1 hp2 hp3 hpc1 hrun1 hsp1 hx20_1 hx29_1 htr1 hvregs1
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (polys_alloc_4_7_4k hA s0 s1 fsp hfsp_align
      (((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗ Frame)
      R hpc1 hrun1 hsp1 htr1 hvregs1 ?_)
  intro s2 p4 p5 p6 p7 hp4 hp5 hp6 hp7 hpc2 hrun2 hsp2 hx20_2 hx29_2 htr2 hvregs2
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (polys_alloc_8_11_4k hA s0 s2 fsp hfsp_align
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗ Frame)
      R hpc2 hrun2 hsp2 htr2 hvregs2 ?_)
  intro s3 p8 p9 p10 p11 hp8 hp9 hp10 hp11 hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx29_3 htr3 hvregs3
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (polys_alloc_12_15_4k hA s0 s3 fsp hfsp_align
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗ Frame)
      R hpc3 hrun3 hsp3 htr3 hvregs3 ?_)
  intro s4 p12 p13 p14 p15 hp12 hp13 hp14 hp15 hpc4 hrun4 hsp4
    hx0_4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 htr4 hvregs4
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (sepWPp_seq_clean
      (polys_init_scatter (A := A) (b := b) (ext := ext) s4 fsp out pbA polysPtr
        p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
        hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
        hfsp_align (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc4 hrun4 hsp4 hx0_4
        (by rw [hx19_4, hx19_3])
        (by rw [hx20_4, hx20_3, hx20_2, hx20_1])
        (by rw [hx21_4, hx21_3])
        (by rw [hx23_4, hx23_3])
        (by rw [hx24_4, hx24_3])
        hx25_4 hx26_4 hx27_4
        (by rw [hx29_4, hx29_3, hx29_2, hx29_1, hx29]))
      ?_)
  intro s5 hpc5 hrun5 ⟨hsp5, hx22_5, hx23_5, hx24_5, hx28_5, hx29_5, htr5, hvregs5⟩
  exact hcont s5 hpc5 hrun5 hsp5 hx22_5 hx23_5 hx24_5 hx28_5 hx29_5 (by rw [htr5, htr4]) (by rw [hvregs5, hvregs4])

/-! ## `.polys` Non-Empty Even-Slice Step, Finish Step, and Outer Loop (`+1204 -> +1496 / +1548`) -/

theorem polys_elem_even_nonempty_step_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext) (j m : Nat) (bs : List (BitVec 8))
    (s0 s : State) (fsp polysPtr bsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame R : SepProp)
    (hlen : bs.length = 2 * (m + 1)) (hmax : bs.length < 2 ^ 63)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = fsp + 864#64)
    (hx24 : s.readReg64 .x24 = polysPtr)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (24 * j))
    (hx29 : s.readReg64 .x29 = fsp + 928#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (outPtr : BitVec 64),
      outPtr ≠ 0#64 →
      sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1356#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x20 = BitVec.ofNat 64 (j + 1) →
      sm.readReg64 .x22 = BitVec.ofNat 64 j →
      sm.readReg64 .x23 = fsp + 864#64 →
      sm.readReg64 .x24 = polysPtr →
      sm.readReg64 .x28 = BitVec.ofNat 64 (24 * (j + 1)) →
      sm.readReg64 .x29 = fsp + 928#64 →
      sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗
          ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
          ((fsp + 904#64) ↦₆₄ outPtr) ∗
          ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
          vecBuf A 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗
        cells (fsp + 896#64) 3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R)) := by
  have heven : bs.length % 2 = 0 := by omega
  have hpos : 0 < bs.length := by omega
  have hn64 : bs.length < 2 ^ 64 := by omega
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlayout : LayoutOk bs.length 2 := ⟨by omega, hpow2, by omega⟩
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbit32 := bit0_and_32_eq_zero_of_even_63 heven hmax
  have hbit64 := bit0_and_64_eq_zero_of_even_63 heven hmax
  have hne0 := ofNat_ne_zero_of_pos hpos hn64
  have hbeq0 := ofNat_beq_zero_false_of_pos hpos hn64
  have hlsr1 : BitVec.ofNat 64 bs.length >>> 1#64 = BitVec.ofNat 64 (m + 1) := by
    rw [shiftRight_1_eq_div_2_63 hmax]; congr 1; omega
  have hlsr2 : BitVec.ofNat 64 bs.length >>> 1 = BitVec.ofNat 64 (m + 1) := by
    rw [shiftRight_1_nat_eq_div_2_63 hmax]; congr 1; omega
  have hlen_fn : True → bs.length = 2 * (m + 1) := fun _ => hlen
  clear hlen
  have hshim := hA.shim_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_alloc")); simp only [rustAllocSpec] at halloc
  have hpanic1708 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_1708 b ext Q s0 s P R
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 1204 80
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic1708 hcont ⊢
  generalize hentry : (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1244#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro _
    refine hpanic1708 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, *])
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; rintro ⟨_, htr0⟩
    have hbeq_oom : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    rw [cells_896_eq fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro v0
    apply SepWPp.exists_elim; intro v1
    apply SepWPp.exists_elim; intro v2
    apply SepWPp.of_sepWP (mid := entry + 1308#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hlen := hlen_fn trivial
    set outPtr := sf_1.readReg64 (Reg.gpr 0#5)
    refine SepWPp.weaken_pre
      (by dsimp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]; simp only [BitVec.add_zero, h_1, hsp_sf, hsp]; exact Entails.of_eq (by ac_rfl))
      (sepWPp_seq_clean
        (polys_inner_loop (b := b) (ext := ext) m bs 0 (m + 1) _ fsp bsPtr outPtr 0#64 hfsp_align
          (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ((fsp + 904#64) ↦₆₄ outPtr) ∗
            A.live outPtr bs.length 2 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hlen (by omega) (by omega)
          (by dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat]; simp only [arm64_norm, wp_norm, hentry, *])
          (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
          (by simp only [arm64_norm, wp_norm, Reg.x0, outPtr, *])
          (by simp only [arm64_norm, wp_norm, Reg.x19, *])
          (by rw [← hlen]; simp only [arm64_norm, wp_norm, Reg.x21, *])
          (by simp only [arm64_norm, wp_norm, Reg.x26, *])
          (by simp only [arm64_norm, wp_norm, Reg.x27, *])
          (by simp only [arm64_norm, wp_norm, Reg.x29, *]))
        ?_)
    intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx28_3, hx29_3, htr3, hvregs3⟩
    dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc3
    rw [hentry] at hpc3
    have hj_step : BitVec.ofNat 64 (24 * j + 24) = BitVec.ofNat 64 (24 * (j + 1)) := by rfl
    refine SepWPp.weaken_pre ?_
      (hcont s3 outPtr hoom hpc3 hrun3 hsp3
        (by rw [hx20_3]; simp only [arm64_norm, wp_norm, Reg.x20, *])
        (by rw [hx22_3]; simp only [arm64_norm, wp_norm, Reg.x22, *])
        (by rw [hx23_3]; simp only [arm64_norm, wp_norm, Reg.x23, *])
        (by rw [hx24_3]; simp only [arm64_norm, wp_norm, Reg.x24, *])
        (by rw [hx28_3]; simp only [arm64_norm, wp_norm, Reg.x28, hj_step, *])
        hx29_3
        (by simp only [arm64_norm, wp_norm, htr3, *])
        (by simp only [arm64_norm, wp_norm, hvregs3, *]))
    have hpts_len := bytesToGF16ListTotal_length (m + 1) bs hlen
    have hm64 : m + 1 < 2 ^ 64 := by omega
    have hcap_toNat : (BitVec.ofNat 64 (m + 1)).toNat = m + 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
    have hcap_ne : BitVec.ofNat 64 (m + 1) ≠ 0 := ofNat_ne_zero_of_pos (by omega) hm64
    dsimp only [Nat.mul_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat]
    simp only [BitVec.add_zero]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (A.live outPtr bs.length 2 ∗
         arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs)) ∗
        (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
         ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
         (bsPtr ↦ₛ bs) ∗
         ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
         ((fsp + 904#64) ↦₆₄ outPtr) ∗
         ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
         A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_left
        (show A.live outPtr bs.length 2 ∗ arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs) ⊢
          vecBuf A 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs) by
          unfold vecBuf
          rw [hpts_len, hcap_toNat]
          simp only [hcap_ne, ↓reduceIte, Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp]
          have hm2 : (m + 1) * 2 = bs.length := by omega
          rw [hm2]
          exact Entails.pure_right ⟨by omega, by omega, hoom⟩ (Entails.of_eq (by ac_rfl))))
      (Entails.of_eq (by ac_rfl))

theorem polys_elem_finish_step_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (j m : Nat) (hj : j < 16) (hm : 2 * (m + 1) < 2 ^ 63)
    (bs : List (BitVec 8)) (hlen : bs.length = 2 * (m + 1))
    (s : State) (fsp polysPtr outPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1356#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (j + 1))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = fsp + 864#64)
    (hx24 : s.readReg64 .x24 = polysPtr)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (24 * (j + 1)))
    (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP (contractProg b ext)
      (if j + 1 < 16 then (contractProg b ext).fnAddr encoderFromPbName + 1204#64
       else (contractProg b ext).fnAddr encoderFromPbName + 1548#64)
      s
      (zeroPolySlotAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
        ((fsp + 904#64) ↦₆₄ outPtr) ∗
        ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
        vecBuf A 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs) ∗
        cells (fsp + 864#64) 4 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs) ∗
          cells (fsp + 864#64) 4 ∗
          cells (fsp + 896#64) 3 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x23 = fsp + 864#64 ∧
        sm.readReg64 .x24 = polysPtr ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 (24 * (j + 1)) ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hdealloc := hA.dealloc_ok_at encoderFromPbName (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::from_pb" "__rustc::__rust_dealloc"))
  simp only [rustDeallocSpec] at hdealloc
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hcmn1 := cmn_one_ne_zero (m := m) (by omega)
  have hcmn2 := cmn_one_bne_zero (m := m) (by omega)
  have hneg1 := neg_one_beq_false (m := m) (by omega)
  have hneg2 := neg_one_beq_false' (m := m) (by omega)
  have hmadd := madd_24_eq j (fsp + 480#64)
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 1168 36
  encoder_from_pb_fetches_range b (Rust.withPanics ext) 1356 92
  dsimp only [contractProg, tripleRatchetProgAtExt, encoderFromPbName, BitVec.ofNat_eq_ofNat] at hpc hdealloc ⊢
  generalize hentry : (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder>::from_pb" = entry at *
  examples_hide_fetches
  unfold zeroPolySlotAt
  rw [cells_864_eq fsp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u0
  apply ProofLib.SepWP.exists_left; intro u1
  apply ProofLib.SepWP.exists_left; intro u2
  apply ProofLib.SepWP.exists_left; intro u3
  apply ProofLib.SepWP.exists_left; intro oldPtr
  wp_simp_pre [sepConj_pure_left_comm]
  refine SepWP.weaken_pre (Entails.pure_left fun _ => Entails.refl _) ?_
  let slotAddr := fsp + 480#64 + BitVec.ofNat 64 (24 * j)
  let len := BitVec.ofNat 64 (m + 1)
  wp_simp_pre [sepConj_assoc]
  wp_conv_pre => rw [fsp_904_split_at_1_rest fsp outPtr len]; dsimp only [slotAddr, len]
  wp_step; wp_step; wp_step; wp_step
  wp_conv_pre => rw [← fsp_904_split_at_1_rest fsp outPtr len]; dsimp only [slotAddr, len]
  wp_step; wp_step; wp_step
  wp_conv_pre => rw [fsp_864_split_at_7_rest fsp (midWord1 outPtr len) u1]; dsimp only [slotAddr, len]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre => rw [fsp_864_after_write_rest fsp outPtr len (u1.extractLsb' 56 8)]; dsimp only [slotAddr, len]
  wp_step; wp_step
  wp_conv_pre => rw [fsp_880_split_at_7_rest fsp (midWord1 outPtr len) u3]; dsimp only [slotAddr, len]
  wp_steps; wp_apply; wp_step
  wp_conv_pre => rw [fsp_880_after_write_rest fsp outPtr len (u3.extractLsb' 56 8)]; dsimp only [slotAddr, len]
  wp_step
  wp_conv_pre =>
    rw [fsp_880_split_at_7_rest fsp (midWord1 outPtr len) (shiftedWord7 len (u3.extractLsb' 56 8)),
        midWord7_midWord1_shiftedWord7, extractLsb56_shiftedWord7]
    dsimp only [slotAddr, len]
  wp_step
  wp_conv_pre => rw [fsp_880_after_write_rest fsp outPtr len (u3.extractLsb' 56 8)]; dsimp only [slotAddr, len]
  wp_step; wp_step; wp_step
  wp_conv_pre => rw [slot_split_at_1_rest slotAddr oldPtr 0#64]; dsimp only [slotAddr, len]
  wp_step; wp_step
  wp_conv_pre => rw [slot_after_write_rest slotAddr outPtr len 0#64]; dsimp only [slotAddr, len]
  wp_step
  have hpts_len := bytesToGF16ListTotal_length (m + 1) bs hlen
  by_cases hlt : j + 1 < 16
  · simp only [hlt, ↓reduceIte]
    have h24_lt : 24 * (j + 1) < 384 := by omega
    have hne384 : (BitVec.ofNat 64 (24 * (j + 1)) != 384#64) = true := bne_of_lt h24_lt (by decide)
    have hne384' : (384#64 != BitVec.ofNat 64 (24 * (j + 1))) = true := bne_of_gt h24_lt (by decide)
    have hbeq384 : (BitVec.ofNat 64 (24 * (j + 1)) == 384#64) = false := beq_false_of_lt h24_lt (by decide)
    have hbeq384' : (384#64 == BitVec.ofNat 64 (24 * (j + 1))) = false := beq_false_of_gt h24_lt (by decide)
    wp_steps
    refine align_pre ?_ ?_
    · unfold vecGF16Of vecOf vecAt vecHeader
      rw [hpts_len, cells_896_eq fsp, hsp]
      dsimp only [slotAddr, len, gf16Stride, gf16Align]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ outPtr) ∗
           ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           vecBuf A 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs)) ∗
          (((fsp + 864#64) ↦₆₄ midWord1 outPtr (BitVec.ofNat 64 (m + 1))) ∗
           ((fsp + 872#64) ↦₆₄ shiftedWord7 (BitVec.ofNat 64 (m + 1)) (u1.extractLsb' 56 8)) ∗
           ((fsp + 880#64) ↦₆₄ midWord1 outPtr (BitVec.ofNat 64 (m + 1))) ∗
           ((fsp + 888#64) ↦₆₄ shiftedWord7 (BitVec.ofNat 64 (m + 1)) (u3.extractLsb' 56 8))) ∗
          (((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           ((fsp + 904#64) ↦₆₄ outPtr) ∗
           ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1))) ∗
          (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      refine sepConj_mono ?_ (sepConj_mono ?_ (sepConj_mono_left ?_))
      · exact Entails.sepExists_right len (Entails.sepExists_right outPtr (Entails.of_eq (by ac_rfl)))
      · exact Entails.sepExists_right (midWord1 outPtr len)
          (Entails.sepExists_right (shiftedWord7 len (u1.extractLsb' 56 8))
            (Entails.sepExists_right (midWord1 outPtr len)
              (Entails.sepExists_right (shiftedWord7 len (u3.extractLsb' 56 8))
                (Entails.of_eq (by ac_rfl)))))
      · exact Entails.sepExists_right len (Entails.sepExists_right outPtr
          (Entails.sepExists_right len (Entails.of_eq (by ac_rfl))))
    · wp_done
  · simp only [hlt, ↓reduceIte]
    have hj15 : j = 15 := by omega
    subst hj15
    wp_steps
    refine align_pre ?_ ?_
    · unfold vecGF16Of vecOf vecAt vecHeader
      rw [hpts_len, cells_896_eq fsp, hsp]
      dsimp only [slotAddr, len, gf16Stride, gf16Align]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((fsp + 480#64 + BitVec.ofNat 64 (24 * 15)) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           ((fsp + 480#64 + BitVec.ofNat 64 (24 * 15) + 8#64) ↦₆₄ outPtr) ∗
           ((fsp + 480#64 + BitVec.ofNat 64 (24 * 15) + 16#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           vecBuf A 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs)) ∗
          (((fsp + 864#64) ↦₆₄ midWord1 outPtr (BitVec.ofNat 64 (m + 1))) ∗
           ((fsp + 872#64) ↦₆₄ shiftedWord7 (BitVec.ofNat 64 (m + 1)) (u1.extractLsb' 56 8)) ∗
           ((fsp + 880#64) ↦₆₄ midWord1 outPtr (BitVec.ofNat 64 (m + 1))) ∗
           ((fsp + 888#64) ↦₆₄ shiftedWord7 (BitVec.ofNat 64 (m + 1)) (u3.extractLsb' 56 8))) ∗
          (((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           ((fsp + 904#64) ↦₆₄ outPtr) ∗
           ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1))) ∗
          (A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      refine sepConj_mono ?_ (sepConj_mono ?_ (sepConj_mono_left ?_))
      · exact Entails.sepExists_right len (Entails.sepExists_right outPtr (Entails.of_eq (by ac_rfl)))
      · exact Entails.sepExists_right (midWord1 outPtr len)
          (Entails.sepExists_right (shiftedWord7 len (u1.extractLsb' 56 8))
            (Entails.sepExists_right (midWord1 outPtr len)
              (Entails.sepExists_right (shiftedWord7 len (u3.extractLsb' 56 8))
                (Entails.of_eq (by ac_rfl)))))
      · exact Entails.sepExists_right len (Entails.sepExists_right outPtr
          (Entails.sepExists_right len (Entails.of_eq (by ac_rfl))))
    · wp_done

theorem polys_outer_loop_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts4K b A ext)
    (s0 : State) (fsp polysPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (j : Nat) (acc : List (List GF16))
      (s : State) (Frame R : SepProp),
      rem ≠ [] →
      j + rem.length = 16 →
      acc.length = j →
      s.pc = (contractProg b ext).fnAddr encoderFromPbName + 1204#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x22 = BitVec.ofNat 64 j →
      s.readReg64 .x23 = fsp + 864#64 →
      s.readReg64 .x24 = polysPtr →
      s.readReg64 .x28 = BitVec.ofNat 64 (24 * j) →
      s.readReg64 .x29 = fsp + 928#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ sm (tail : List LibsignalSpqrV1.Poly),
        decodePbPolysTotal rem = .ok tail →
        sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1548#64 →
        sm.status = .Running →
        sm.sp = fsp →
        sm.readReg64 .x29 = fsp + 928#64 →
        sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A (fsp + 480#64) (acc ++ tail.map LibsignalSpqrV1.Poly.coefficients) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) →
      (∀ sm (errPolys : List (List GF16)),
        decodePbPolysTotal rem = .error .serializationInvalid →
        errPolys.length = 16 →
        sm.pc = (contractProg b ext).fnAddr encoderFromPbName + 1496#64 →
        sm.status = .Running →
        sm.sp = fsp →
        sm.readReg64 .x19 = 2#64 →
        sm.readReg64 .x29 = fsp + 928#64 →
        sm.trace = s0.trace →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A (fsp + 480#64) errPolys ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))) →
      SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s
        (vecGF16ListOf A (fsp + 480#64) acc ∗
          zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) rem.length ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j)) rem ∗
          cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encoderFromPbOnPanic s0 sf ∗ R))
  | [], _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => (hne rfl).elim
  | bs :: rest, j, acc, s, Frame, R, _, hj_rem, hacc_len, hpc, hrun, hsp,
    hx22, hx23, hx24, hx28, hx29, htrace, hvregs, hcont_ok, hcont_err => by
    have hj_lt : j < 16 := by simp only [List.length_cons] at hj_rem; omega
    dsimp only [List.length_cons, zeroPolySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_left (vecU8_open A (polysPtr + BitVec.ofNat 64 (24 * j)) bs))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap
    apply SepWPp.exists_elim; intro bsPtr
    refine SepWPp.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          (vecGF16ListOf A (fsp + 480#64) acc ∗
           zeroPolySlotAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
           zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
           ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
           ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           (bsPtr ↦ₛ bs) ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
           cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
           A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl))
        (Entails.trans
          (sepConj_mono_left (vecU8Rest_entails_len_lt A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs))
          (Entails.of_eq (show _ =
            ⌜bs.length < 2 ^ 63⌝ ∗
            (vecGF16ListOf A (fsp + 480#64) acc ∗
             zeroPolySlotAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
             zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
             ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
             cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
             A.pool ∗ stackAt fsp allocHookStack ∗ Frame) by ac_rfl)))) ?_
    apply SepWPp.pure_left; intro hbs_max
    cases bs with
    | nil =>
      have hdec_err : decodePbPolysTotal ([] :: rest) = .error .serializationInvalid := rfl
      have hstep := polys_elem_empty_step (b := b) (ext := ext) j s fsp polysPtr hfsp_align
        (vecGF16ListOf A (fsp + 480#64) acc ∗
          zeroPolySlotAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ []) ∗
          vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr [] ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc hrun hsp hx24 hx28
      refine SepWPp.weaken_pre
        (by dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl))
        (sepWPp_seq_clean hstep ?_)
      intro sm hpcm hrunm ⟨hspm, hx19m, hx29m, htrm, hvregsm⟩
      have herr_len : (acc ++ List.replicate (rest.length + 1) ([] : List GF16)).length = 16 := by
        simp only [List.length_cons] at hj_rem
        rw [List.length_append, List.length_replicate, hacc_len]
        omega
      refine SepWPp.weaken_pre ?_
        (hcont_err sm (acc ++ List.replicate (rest.length + 1) []) hdec_err herr_len
          hpcm hrunm hspm hx19m (hx29m.trans hx29) (htrm.trans htrace) (hvregsm.trans hvregs))
      have heq_pre :
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
          vecGF16ListOf A (fsp + 480#64) acc ∗
          zeroPolySlotAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ []) ∗
          vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr [] ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame =
          (vecGF16ListOf A (fsp + 480#64) acc ∗
           zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (rest.length + 1)) ∗
          (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
           ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
           (bsPtr ↦ₛ []) ∗
           vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr []) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame := by
        dsimp only [zeroPolySlotsAt, List.length_nil, BitVec.ofNat_eq_ofNat]
        ac_rfl
      rw [heq_pre]
      have hslots := zeroPolySlotsAt_entails_vecGF16ListOf A (rest.length + 1)
        (fsp + 480#64 + BitVec.ofNat 64 (24 * j))
      have happ := vecGF16ListOf_append A acc (List.replicate (rest.length + 1) []) (fsp + 480#64)
      rw [hacc_len] at happ
      have hclose := vecU8_close A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr []
      dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]
      refine Entails.trans
        (sepConj_mono (Entails.trans (sepConj_mono_right hslots) (Entails.of_eq happ.symm))
          (sepConj_mono_left hclose))
        (Entails.of_eq (by ac_rfl))
    | cons b0 bs' =>
      set bs := b0 :: bs'
      have hbs_ne_zero : (bs.length == 0) = false := by simp [bs]
      by_cases hodd_bool : (bs.length % 2 != 0) = true
      · have hodd : bs.length % 2 ≠ 0 := bne_iff_ne.mp hodd_bool
        have hdec_err : decodePbPolysTotal (bs :: rest) = .error .serializationInvalid := by
          have h1 : (bs.length % 2 == 1) = true := by rw [beq_iff_eq]; omega
          simp [decodePbPolysTotal, polyDeserializeTotal, h1]
        have hstep := polys_elem_odd_step (b := b) (ext := ext) j bs s fsp polysPtr hfsp_align
          (vecGF16ListOf A (fsp + 480#64) acc ∗
            zeroPolySlotAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
            zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
            (bsPtr ↦ₛ bs) ∗
            vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          hodd hbs_max hpc hrun hsp hx24 hx28
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hstep ?_)
        intro sm hpcm hrunm ⟨hspm, hx19m, hx29m, htrm, hvregsm⟩
        have herr_len : (acc ++ List.replicate (rest.length + 1) ([] : List GF16)).length = 16 := by
          simp only [List.length_cons] at hj_rem
          rw [List.length_append, List.length_replicate, hacc_len]
          omega
        refine SepWPp.weaken_pre ?_
          (hcont_err sm (acc ++ List.replicate (rest.length + 1) []) hdec_err herr_len
            hpcm hrunm hspm hx19m (hx29m.trans hx29) (htrm.trans htrace) (hvregsm.trans hvregs))
        have heq_pre :
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            vecGF16ListOf A (fsp + 480#64) acc ∗
            zeroPolySlotAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
            zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
            (bsPtr ↦ₛ bs) ∗
            vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame =
            (vecGF16ListOf A (fsp + 480#64) acc ∗
             zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (rest.length + 1)) ∗
            (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame := by
          dsimp only [zeroPolySlotsAt]
          ac_rfl
        rw [heq_pre]
        have hslots := zeroPolySlotsAt_entails_vecGF16ListOf A (rest.length + 1)
          (fsp + 480#64 + BitVec.ofNat 64 (24 * j))
        have happ := vecGF16ListOf_append A acc (List.replicate (rest.length + 1) []) (fsp + 480#64)
        rw [hacc_len] at happ
        have hclose := vecU8_close A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
        dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]
        refine Entails.trans
          (sepConj_mono (Entails.trans (sepConj_mono_right hslots) (Entails.of_eq happ.symm))
            (sepConj_mono_left hclose))
          (Entails.of_eq (by ac_rfl))
      · have heven : bs.length % 2 = 0 := by
          simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd_bool
          exact hodd_bool
        set m := bs.length / 2 - 1
        have hlen_m : bs.length = 2 * (m + 1) := by
          have hpos : 0 < bs.length := by simp [bs]
          omega
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (polys_elem_even_nonempty_step_4k hA j m bs s0 s fsp polysPtr bsPtr hfsp_align
            (vecGF16ListOf A (fsp + 480#64) acc ∗
              zeroPolySlotAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
              zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
              vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
              arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
              cells (fsp + 864#64) 4 ∗ Frame)
            R hlen_m hbs_max hpc hrun hsp hx22 hx23 hx24 hx28 hx29 htrace hvregs ?_)
        intro s1 outPtr houtPtr hpc1 hrun1 hsp1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 hx29_1 htr1 hvregs1
        have hfin := polys_elem_finish_step_4k (A := A) (b := b) (ext := ext) hA j m hj_lt
          (by omega) bs hlen_m s1 fsp polysPtr outPtr hfsp_align
          (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            (bsPtr ↦ₛ bs) ∗
            vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            vecGF16ListOf A (fsp + 480#64) acc ∗
            zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            Frame)
          hpc1 hrun1 hsp1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 hx29_1
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hfin ?_)
        intro s2 hpc2 hrun2 ⟨hsp2, hx22_2, hx23_2, hx24_2, hx28_2, hx29_2, htr2, hvregs2⟩
        have hclose := vecU8_close A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
        have happ := vecGF16ListOf_append A acc [bytesToGF16ListTotal bs] (fsp + 480#64)
        rw [hacc_len] at happ
        have hsingle : vecGF16ListOf A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) [bytesToGF16ListTotal bs] =
            vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs) := by
          dsimp only [vecGF16ListOf, arrayAt]; simp only [sepConj_emp]
        rw [hsingle] at happ
        have hpoly_ok : polyDeserializeTotal bs = .ok { coefficients := bytesToGF16ListTotal bs } := by
          have h1 : bs.isEmpty = false := rfl
          have h2 : (bs.length % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
          simp [polyDeserializeTotal, h1, h2]
        cases rest with
        | nil =>
          have hj15 : j = 15 := by simp only [List.length_cons, List.length_nil] at hj_rem; omega
          have hlt_false : ¬(j + 1 < 16) := by omega
          simp only [hlt_false, ↓reduceIte] at hpc2
          have hdec_ok : decodePbPolysTotal [bs] = .ok [{ coefficients := bytesToGF16ListTotal bs }] := by
            simp [decodePbPolysTotal, hpoly_ok]
          refine SepWPp.weaken_pre ?_
            (hcont_ok s2 [{ coefficients := bytesToGF16ListTotal bs }] hdec_ok hpc2 hrun2 hsp2
              hx29_2 (htr2.trans htr1) (hvregs2.trans hvregs1))
          dsimp only [List.map, List.length_nil, zeroPolySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
          simp only [sepConj_emp]
          refine Entails.trans
            (Entails.of_eq (show _ =
              (vecGF16ListOf A (fsp + 480#64) acc ∗
               vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
              (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
               ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
               (bsPtr ↦ₛ bs) ∗
               vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
              cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
            (Entails.of_eq (by ac_rfl))
        | cons bs2 rest' =>
          have hlt_true : j + 1 < 16 := by simp only [List.length_cons] at hj_rem; omega
          simp only [hlt_true, ↓reduceIte] at hpc2
          have hj_addr1 : fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64 =
              fsp + 480#64 + BitVec.ofNat 64 (24 * (j + 1)) := by
            rw [bv_add_lit_add_lit]; rfl
          have hj_addr2 : polysPtr + BitVec.ofNat 64 (24 * j) + 24#64 =
              polysPtr + BitVec.ofNat 64 (24 * (j + 1)) := by
            rw [bv_add_lit_add_lit]; rfl
          refine SepWPp.weaken_pre ?_
            (polys_outer_loop_4k hA s0 fsp polysPtr hfsp_align (bs2 :: rest') (j + 1)
              (acc ++ [bytesToGF16ListTotal bs]) s2
              (vecU8 A (polysPtr + BitVec.ofNat 64 (24 * j)) bs ∗ Frame) R
              (List.cons_ne_nil _ _)
              (by simp only [List.length_cons] at hj_rem ⊢; omega)
              (by rw [List.length_append, hacc_len]; rfl)
              hpc2 hrun2 hsp2 hx22_2 hx23_2 hx24_2 hx28_2 hx29_2 (htr2.trans htr1)
              (hvregs2.trans hvregs1)
              (fun sm tail hdec_tail hpcm hrunm hspm hx29m htrm hvregsm => ?_)
              (fun sm errPolys hdec_err herr_len hpcm hrunm hspm hx19m hx29m htrm hvregsm => ?_))
          · rw [← hj_addr1, ← hj_addr2]
            refine Entails.trans
              (Entails.of_eq (show _ =
                (vecGF16ListOf A (fsp + 480#64) acc ∗
                 vecGF16Of A (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
                (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
                 ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
                 (bsPtr ↦ₛ bs) ∗
                 vecU8Rest A (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
                zeroPolySlotsAt A (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) (bs2 :: rest').length ∗
                arrayAt (fun bs addr => vecU8 A addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) (bs2 :: rest') ∗
                cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl)) ?_
            exact Entails.trans
              (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
              (Entails.of_eq (by ac_rfl))
          · have hdec_cons : decodePbPolysTotal (bs :: bs2 :: rest') =
                .ok ({ coefficients := bytesToGF16ListTotal bs } :: tail) := by
              change (match polyDeserializeTotal bs with
                | Except.error e => Except.error e
                | Except.ok p => match decodePbPolysTotal (bs2 :: rest') with
                  | Except.error e => Except.error e
                  | Except.ok tail => Except.ok (p :: tail)) = _
              simp only [hpoly_ok, hdec_tail]
            have happ_assoc : (acc ++ [bytesToGF16ListTotal bs]) ++ tail.map LibsignalSpqrV1.Poly.coefficients =
                acc ++ ({ coefficients := bytesToGF16ListTotal bs } :: tail).map LibsignalSpqrV1.Poly.coefficients := by
              simp [List.append_assoc]
            rw [happ_assoc, ← hj_addr2]
            refine SepWPp.weaken_pre
              (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl))
              (hcont_ok sm ({ coefficients := bytesToGF16ListTotal bs } :: tail) hdec_cons
                hpcm hrunm hspm hx29m htrm hvregsm)
          · have hdec_cons : decodePbPolysTotal (bs :: bs2 :: rest') = .error .serializationInvalid := by
              change (match polyDeserializeTotal bs with
                | Except.error e => Except.error e
                | Except.ok p => match decodePbPolysTotal (bs2 :: rest') with
                  | Except.error e => Except.error e
                  | Except.ok tail => Except.ok (p :: tail)) = _
              simp only [hpoly_ok, hdec_err]
            rw [← hj_addr2]
            refine SepWPp.weaken_pre
              (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl))
              (hcont_err sm errPolys hdec_cons herr_len
                hpcm hrunm hspm hx19m hx29m htrm hvregsm)

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
