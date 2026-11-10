/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<Poly>::lagrange_interpolate_prepare`: Binary Verification

Verifies `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` (`0x61c1c`,
Block `372`) against `lagrangePrepareSpec` and `lagrangePreparePlacedSpec`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.LagrangePrepare

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  ofNat_shl_two truncate32_sext64_16 sbfx64_one_eq
  truncate32_if_all_ones truncate32_zext64 zext64_zext32_16
  and_65535_zext64_16 prepare_polyReduce_xor_eq

open Lean Elab Tactic in
scoped elab "lagrangePrepare_fetches " b:term:max H:term:max st:num ln:num : tactic => do
  let codeName := `CryptoVerification.libsignalSessionCode
  let eOff ← ProofLib.CodeLookup.lookup codeName .fnOff
    "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches_range $(mkCIdent codeName) $(mkIdent `lagrangePrepareBin) $b $H $hfn
      $offLit $st $ln))


set_option maxHeartbeats 1600000 in
private theorem innerLoop_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (sp0 ptr : BitVec 64) (hptr_al : ptr &&& 1#64 = 0#64)
    (n : Nat) (hn_bound : n + 1 < 2 ^ 63)
    (yv : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (rem' k : Nat) (cs : List GF16)
      (_hk1 : 1 ≤ k) (_hk_rem : k + rem' = n) (_hcs_len : cs.length = n + 1)
      (s : State) (F : SepProp),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 212#64 →
      s.status = .Running →
      s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * (k - 1)) →
      s.readReg64 .x20 = BitVec.ofNat 64 n →
      s.readReg64 .x21 = sbfxMask64 yv 6 →
      s.readReg64 .x22 = sbfxMask64 yv 7 →
      s.readReg64 .x23 = b + bv% reduceBytesOff →
      s.readReg64 .x24 = ptr + BitVec.ofNat 64 (2 * (k - 1)) →
      s.readReg64 .x25 = sxth32Zext64 yv →
      s.readReg64 .x26 = sbfxMask64 yv 8 →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (rem' + 1) →
      s.readReg64 .x28 = sbfxMask64 yv 9 →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 568#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        sf.trace = s.trace →
        sf.readReg64 .x20 = BitVec.ofNat 64 n →
        sf.readReg64 .x23 = b + bv% reduceBytesOff →
        sf.readReg64 .x29 = sp0 - 96#64 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
          (tokenInitAt b ∗
           ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
           ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
           ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
           ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
           ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
           gf16SliceAt ptr (multXdiffLoopPure ⟨yv⟩ k (rem' + 1) cs) ∗
           reduceTableAt b ∗ F) Q) →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
        (tokenInitAt b ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 yv 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 yv 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 yv 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 yv 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 yv 14) ∗
         gf16SliceAt ptr cs ∗
         reduceTableAt b ∗ F) Q := by
  intro rem'
  induction rem' with
  | zero =>
    intro k cs hk1 hk_rem hcs_len s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hk : k < cs.length := by omega
    have hk_prev : k - 1 < cs.length := by omega
    apply innerStep_sepWP b ext hb sp0 ptr hptr_al n hn_bound yv 0 k cs hk1 hk_rem hcs_len hk hk_prev
      ret_pc Q s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 hpstate1 _hx19_1 hx20_1 _hx21_1 _hx22_1 hx23_1 _hx24_1 _hx25_1 _hx26_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    lagrangePrepare_fetches b (Rust.withPanics ext) 0x234 4
    have hcarry := adds_neg_one_carry
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
    examples_hide_fetches
    wp_steps 1
    rw [multXdiffLoopPure_succ yv k 0 cs hk hk_prev] at hnext
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htrace1) (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1) (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r ih =>
    intro k cs hk1 hk_rem hcs_len s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hnext
    have hk : k < cs.length := by omega
    have hk_prev : k - 1 < cs.length := by omega
    apply innerStep_sepWP b ext hb sp0 ptr hptr_al n hn_bound yv (r + 1) k cs hk1 hk_rem hcs_len hk hk_prev
      ret_pc Q s F hpc hrun hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 hpstate1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    lagrangePrepare_fetches b (Rust.withPanics ext) 0x234 4
    have hcarry := neg_succ_ule_add_one (r := r) (by omega)
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
    examples_hide_fetches
    wp_steps 1
    rw [← hentry]
    apply ih (k + 1)
      (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^ unaccelerated.mul (cs[k]'hk).value yv⟩)
      (by omega) (by omega) (by simp [List.length_set, hcs_len]) _ F
      (by rw [hentry]; wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx21_1)
      (by simpa [arm64_norm, wp_norm] using hx22_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx26_1)
      (by simpa [arm64_norm, wp_norm, neg_succ_add_one (r + 1)] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro sf hpc_f hrun_f hsp_f htrace_f hx20_f hx23_f hx29_f hvregs_f
    rw [multXdiffLoopPure_succ yv k (r + 1) cs hk hk_prev] at hnext
    exact hnext sf hpc_f hrun_f
      (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp1)
      (by rw [htrace_f]; simpa [arm64_norm, wp_norm] using htrace1)
      hx20_f hx23_f hx29_f
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
private theorem outerStep_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (sp0 ptr ptsPtr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (pts : List Pt) (hn_bound : pts.length + 1 < 2 ^ 63)
    (r_out i : Nat) (p : Poly)
    (hi_rem : i + (r_out + 1) = pts.length) (hp_len : p.coefficients.length = pts.length + 1)
    (hi : i < pts.length)
    (v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 208#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 pts.length)
    (hx23 : s.readReg64 .x23 = b + bv% reduceBytesOff)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1))
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 588#64 →
      sf.status = .Running →
      sf.sp = sp0 - 208#64 →
      sf.trace = s.trace →
      sf.pstate = subsPState64 (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 pts.length) →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out) - 2#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 pts.length →
      sf.readReg64 .x23 = b + bv% reduceBytesOff →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1) - 1#64 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
        (tokenInitAt b ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 14) ∗
         gf16SliceAt ptr
           (multXdiffLoopPure (pts[i]'hi).x (r_out + 1) (i + 1) p.coefficients) ∗
         reduceTableAt b ∗
         ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
         ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         ((sp0 - 152#64) ↦₆₄ (0#64 - BitVec.ofNat 64 (i + 1))) ∗
         ((sp0 - 144#64) ↦₆₄ (ptr + BitVec.ofNat 64 (2 * r_out))) ∗
         ptSliceAt ptsPtr pts ∗ F) Q) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
      (tokenInitAt b ∗
       ((sp0 - 132#64) ↦₃₂ w132) ∗
       ((sp0 - 128#64) ↦₃₂ w128) ∗
       ((sp0 - 124#64) ↦₃₂ w124) ∗
       ((sp0 - 120#64) ↦₃₂ w120) ∗
       ((sp0 - 116#64) ↦₃₂ w116) ∗
       gf16SliceAt ptr p.coefficients ∗
       reduceTableAt b ∗
       ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
       ((sp0 - 160#64) ↦₆₄ v160) ∗
       ((sp0 - 152#64) ↦₆₄ v152) ∗
       ((sp0 - 144#64) ↦₆₄ v144) ∗
       ptSliceAt ptsPtr pts ∗ F) Q := by
  lagrangePrepare_fetches b (Rust.withPanics ext) 0x84 80
  lagrangePrepare_fetches b (Rust.withPanics ext) 0x238 20
  have hi_succ : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add]
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [ptSliceAt_focus_x_assoc hi ptsPtr]
  wp_steps 20
  wp_conv_pre =>
    rw [← ptSliceAt_focus_x_assoc hi ptsPtr]
  rw [← hentry]
  apply innerLoop_sepWP b ext hb sp0 ptr hptr_al pts.length hn_bound (pts[i]'hi).x.value
    ret_pc Q i (r_out + 1) p.coefficients (by omega) (by omega) hp_len _
    (((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
     ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
     ((sp0 - 152#64) ↦₆₄ (0#64 - BitVec.ofNat 64 (i + 1))) ∗
     ((sp0 - 144#64) ↦₆₄ (ptr + BitVec.ofNat 64 (2 * r_out))) ∗
     ptSliceAt ptsPtr pts ∗ F)
    (by rw [hentry]; wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx19)
    (by simpa [arm64_norm, wp_norm] using hx20)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx23)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx27)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx29)
  intro s1 hpc1 hrun1 hsp1 htrace1 hx20_1 hx23_1 hx29_1 hvregs1
  have hsp1' : s1.sp = sp0 - 208#64 := by
    rw [hsp1]; simpa [arm64_norm, wp_norm] using hsp
  have htrace1' : s1.trace = s.trace := by
    simpa [arm64_norm, wp_norm] using htrace1
  have hvregs1' : calleeSavedVRegs s1 = calleeSavedVRegs s := by
    simpa [arm64_norm, wp_norm] using hvregs1
  rw [hentry] at hpc1
  wp_steps 5
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp1')
    (by simpa [arm64_norm, wp_norm] using htrace1')
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx20_1)
    (by simpa [arm64_norm, wp_norm] using hx23_1)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx29_1)
    (by simpa [arm64_norm, wp_norm] using hvregs1')

set_option maxHeartbeats 1600000 in
private theorem outerLoop_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (sp0 ptr ptsPtr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (pts : List Pt) (hn_bound : pts.length + 1 < 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r_out i : Nat) (p : Poly)
      (_hi_rem : i + (r_out + 1) = pts.length) (_hp_len : p.coefficients.length = pts.length + 1)
      (v160 v152 v144 : BitVec 64)
      (w132 w128 w124 w120 w116 : BitVec 32)
      (s : State) (F : SepProp),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 132#64 →
      s.status = .Running →
      s.sp = sp0 - 208#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 i →
      s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out) →
      s.readReg64 .x20 = BitVec.ofNat 64 pts.length →
      s.readReg64 .x23 = b + bv% reduceBytesOff →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1) →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ (v160' v152' v144' : BitVec 64) (w132' w128' w124' w120' w116' : BitVec 32) (sf : State),
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName + 608#64 →
        sf.status = .Running →
        sf.sp = sp0 - 208#64 →
        sf.trace = s.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
          (tokenInitAt b ∗
           ((sp0 - 132#64) ↦₃₂ w132') ∗
           ((sp0 - 128#64) ↦₃₂ w128') ∗
           ((sp0 - 124#64) ↦₃₂ w124') ∗
           ((sp0 - 120#64) ↦₃₂ w120') ∗
           ((sp0 - 116#64) ↦₃₂ w116') ∗
           gf16SliceAt ptr (prepareLoopPure pts pts.length i (r_out + 1) p).coefficients ∗
           reduceTableAt b ∗
           ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
           ((sp0 - 160#64) ↦₆₄ v160') ∗
           ((sp0 - 152#64) ↦₆₄ v152') ∗
           ((sp0 - 144#64) ↦₆₄ v144') ∗
           ptSliceAt ptsPtr pts ∗ F) Q) →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
        (tokenInitAt b ∗
         ((sp0 - 132#64) ↦₃₂ w132) ∗
         ((sp0 - 128#64) ↦₃₂ w128) ∗
         ((sp0 - 124#64) ↦₃₂ w124) ∗
         ((sp0 - 120#64) ↦₃₂ w120) ∗
         ((sp0 - 116#64) ↦₃₂ w116) ∗
         gf16SliceAt ptr p.coefficients ∗
         reduceTableAt b ∗
         ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
         ((sp0 - 160#64) ↦₆₄ v160) ∗
         ((sp0 - 152#64) ↦₆₄ v152) ∗
         ((sp0 - 144#64) ↦₆₄ v144) ∗
         ptSliceAt ptsPtr pts ∗ F) Q := by
  intro r_out
  induction r_out with
  | zero =>
    intro i p hi_rem hp_len v160 v152 v144 w132 w128 w124 w120 w116 s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29 hnext
    have hi : i < pts.length := by omega
    apply outerStep_sepWP b ext hb sp0 ptr ptsPtr hsp0 hptr_al pts hn_bound
      0 i p hi_rem hp_len hi v160 v152 v144 w132 w128 w124 w120 w116 ret_pc Q s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 hpstate1 _hx9_1 _hx19_1 _hx20_1 _hx23_1 _hx27_1 _hx29_1 hvregs1
    lagrangePrepare_fetches b (Rust.withPanics ext) 0x24c 8
    have heq_len : i + 1 = pts.length := by omega
    rw [heq_len] at hpstate1
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
    examples_hide_fetches
    wp_steps 2
    rw [prepareLoopPure_succ pts i 0 p hi_rem hp_len hi] at hnext
    dsimp only [prepareLoopPure] at hnext
    exact hnext
      (BitVec.ofNat 64 (i + 1)) (0#64 - BitVec.ofNat 64 (i + 1)) (ptr + BitVec.ofNat 64 (2 * 0))
      (sbfxMask32 (pts[i]'hi).x.value 10) (sbfxMask32 (pts[i]'hi).x.value 11)
      (sbfxMask32 (pts[i]'hi).x.value 12) (sbfxMask32 (pts[i]'hi).x.value 13)
      (sbfxMask32 (pts[i]'hi).x.value 14) _
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htrace1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r_out' ih =>
    intro i p hi_rem hp_len v160 v152 v144 w132 w128 w124 w120 w116 s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29 hnext
    have hi : i < pts.length := by omega
    apply outerStep_sepWP b ext hb sp0 ptr ptsPtr hsp0 hptr_al pts hn_bound
      (r_out' + 1) i p hi_rem hp_len hi v160 v152 v144 w132 w128 w124 w120 w116 ret_pc Q s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 hpstate1 hx9_1 hx19_1 hx20_1 hx23_1 hx27_1 hx29_1 hvregs1
    lagrangePrepare_fetches b (Rust.withPanics ext) 0x24c 4
    have hne_len := ofNat_bne_true_of_lt (a := i + 1) (b := pts.length) (by omega) (by omega)
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
    examples_hide_fetches
    wp_steps 1
    rw [← hentry]
    apply ih (i + 1) ⟨multXdiffLoopPure (pts[i]'hi).x (r_out' + 1 + 1) (i + 1) p.coefficients⟩
      (by omega) (by simp [multXdiffLoopPure_length, hp_len])
      (BitVec.ofNat 64 (i + 1)) (0#64 - BitVec.ofNat 64 (i + 1)) (ptr + BitVec.ofNat 64 (2 * (r_out' + 1)))
      (sbfxMask32 (pts[i]'hi).x.value 10) (sbfxMask32 (pts[i]'hi).x.value 11)
      (sbfxMask32 (pts[i]'hi).x.value 12) (sbfxMask32 (pts[i]'hi).x.value 13)
      (sbfxMask32 (pts[i]'hi).x.value 14) _ F
      (by rw [hentry]; wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx9_1)
      (by simpa [arm64_norm, wp_norm, ptr_sub_two_succ ptr r_out'] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm, neg_sub_one (i + 1)] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro v160' v152' v144' w132' w128' w124' w120' w116' sf hpc_f hrun_f hsp_f htrace_f hvregs_f
    rw [prepareLoopPure_succ pts i (r_out' + 1) p hi_rem hp_len hi] at hnext
    exact hnext v160' v152' v144' w132' w128' w124' w120' w116' sf hpc_f hrun_f hsp_f
      (by rw [htrace_f]; simpa [arm64_norm, wp_norm] using htrace1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

private theorem epilogue_sepWP
    (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State))
    (a : LagrangePrepareArgs) (R : SepProp) (s0 s : State)
    (ptr o0 o1 o2 : BitVec 64)
    (v168 v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (hsp_align : s0.sp &&& 0xf#64 = 0#64)
    (hptr_ne : ptr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr lagrangePrepareName + 608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        A.live ptr (2 * (a.pts.length + 1)) 2 ∗
        gf16SliceAt ptr (lagrangePreparePure a.pts).coefficients ∗
        (a.out ↦₆₄ o0) ∗ ((a.out + 8#64) ↦₆₄ o1) ∗ ((a.out + 16#64) ↦₆₄ o2) ∗
        ptSliceAt a.ptsPtr a.pts ∗
        reduceTableAt b ∗
        tokenInitAt b ∗
        memRegion (s0.sp - 208#64) 16 ∗
        ((s0.sp - 192#64) ↦₆₄ ptr) ∗
        ((s0.sp - 184#64) ↦₆₄ a.out) ∗
        ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 (a.pts.length + 1)) ∗
        ((s0.sp - 168#64) ↦₆₄ v168) ∗
        ((s0.sp - 160#64) ↦₆₄ v160) ∗
        ((s0.sp - 152#64) ↦₆₄ v152) ∗
        ((s0.sp - 144#64) ↦₆₄ v144) ∗
        memRegion (s0.sp - 136#64) 4 ∗
        ((s0.sp - 132#64) ↦₃₂ w132) ∗
        ((s0.sp - 128#64) ↦₃₂ w128) ∗
        ((s0.sp - 124#64) ↦₃₂ w124) ∗
        ((s0.sp - 120#64) ↦₃₂ w120) ∗
        ((s0.sp - 116#64) ↦₃₂ w116) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜sf.trace = s0.trace⌝ ∗
              polyOf A a.out (lagrangePreparePure a.pts) ∗
                ptSliceAt a.ptsPtr a.pts ∗
                  reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗ stackAt s0.sp lagrangePrepareStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  lagrangePrepare_fetches b (Rust.withPanics ext) 0x260 48
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
  examples_hide_fetches
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  wp_steps
  refine SepWP.fold
    (stackAt_lagrangePrepare_merge s0.sp (s0.sp - 208#64)
      ptr a.out (BitVec.ofNat 64 (a.pts.length + 1)) v168 v160 v152 v144
      w132 w128 w124 w120 w116
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
      rfl)
    (by sep_focus)
    ?_
  refine SepWP.fold
    (polyOf_of_exact_cap A a.out ptr (lagrangePreparePure a.pts) (a.pts.length + 1)
      (by omega) (lagrangePreparePure_length a.pts) (by omega) hptr_ne)
    (by sep_focus)
    ?_
  wp_done

/-- `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` satisfies
`lagrangePrepareSpec A b`. -/
theorem lagrangePrepare_ok (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64)
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangePrepareName)
      (lagrangePrepareSpec A b) := by
  have hshim := hA.shim_ok_at lagrangePrepareName
    (ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [lagrangePrepare_fnOff]; simp only [arm64_norm])
  have halloc := hA.alloc_ok_at lagrangePrepareName
    (ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
      "__rustc::__rust_alloc")
    (by rw [lagrangePrepare_fnOff]; simp only [arm64_norm])
  have hmemset := hA.session_memset_region_ok_at lagrangePrepareName
    (ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare" "memset")
    (by rw [lagrangePrepare_fnOff]; simp only [arm64_norm])
  have hpan_err :
      (tripleRatchetProgAtExt b ext).externAt?
        ((tripleRatchetProgAtExt b ext).fnAddr lagrangePrepareName +
          bv% (ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
            "alloc::raw_vec::handle_error")) =
        some Rust.panicked :=
    panic_at_handle_error_ext b ext lagrangePrepareName
      (ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
        "alloc::raw_vec::handle_error")
      (by rw [lagrangePrepare_fnOff]; simp only [arm64_norm])
  lagrangePrepare_fetches b (Rust.withPanics ext) 0x0 140
  lagrangePrepare_fetches b (Rust.withPanics ext) 0x254 12
  lagrangePrepare_fetches b (Rust.withPanics ext) 0x29c 12
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmemset hpan_err ⊢
  simp only [lagrangePrepareSpec]
  wpp_init a s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName := by
    rw [Program.fnAddr_rebase, lagrangePrepare_fnOff]; exact hpc
  clear hpc
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
  examples_hide_fetches
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  have hbit62 : (((BitVec.ofNat 64 a.pts.length + 1#64) &&& 4611686018427387904#64) != 0#64) = false :=
    len_succ_bit62_false a.pts.length hbound
  have hshl_succ : (BitVec.ofNat 64 a.pts.length + 1#64) <<< 1#64 = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one a.pts.length
  have hshl_succ_nat : (BitVec.ofNat 64 a.pts.length + 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one_nat a.pts.length
  have htoNat_succ : (BitVec.ofNat 64 (2 * (a.pts.length + 1))).toNat = 2 * (a.pts.length + 1) :=
    ofNat_two_mul_succ_toNat a.pts.length hbound
  have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  apply SepWPp.of_sepWP (mid := entry + 68#64)
  wp_simp_pre only [memRegion_24 a.out, stackAt_lagrangePrepare_split s0.sp]
  wp_pull_exists
  wp_steps 14
  wp_call hshim
  wp_steps 3
  wp_call halloc
  apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
  by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · -- OOM branch (`x0 = 0`): jump to `handle_error` at `+0x29c`
    have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hptr0
    wp_conv_pre => rw [alloc_post_pos hptr0]
    apply SepWPp.pure_left
    intro htr_fail
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
        "alloc::raw_vec::handle_error"))
    wp_steps 4
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have htr_panic_eq :
        (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 2#64).writeReg64 (Reg.gpr 1#5)
          (BitVec.ofNat 64 (2 * (a.pts.length + 1)))).writeReg64 (Reg.gpr 30#5)
          (entry + 680#64)).setPC
          (entry + bv% (ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
            "alloc::raw_vec::handle_error")))).trace = s0.trace ++ [allocFailedEvent] := by
      change sf_1.trace = s0.trace ++ [allocFailedEvent]
      rw [htr_fail, h_3]
    refine SepWPp.panic (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hpan_err)
      (fun hm => ?_)
    rw [← sepConj_assoc]
    refine allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _) ⟨?_, ?_⟩ hm
    · exact allocFailedIn_of_trace_eq htr_panic_eq
    · rw [htr_panic_eq]
      exact List.prefix_append s0.trace [allocFailedEvent]
  · -- Non-null allocation (`x0 ≠ 0`)
    have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
    wp_conv_pre => rw [alloc_post_neg hptr0]
    apply SepWPp.pure_left
    rintro ⟨hptr_mod, htr_ok⟩
    apply SepWPp.of_sepWP_ret
    have hptr_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
      and_one_of_mod_two hptr_mod
    have hlen_add1 : BitVec.ofNat 64 a.pts.length + 1#64 = BitVec.ofNat 64 (a.pts.length + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    wp_conv_pre => rw [h_4]
    wp_steps 4
    by_cases hpts_nil : a.pts = []
    · -- Empty input slice (`a.pts = []`): skip `memset` and outer loop
      have hx20_0 : (BitVec.ofNat 64 a.pts.length == 0#64) = true := by
        rw [hpts_nil]; rfl
      have hmem2 :
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
            ∃∗ v0 : BitVec 16, (sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ v0 := by
        rw [hpts_nil, List.length_nil, Nat.zero_add, Nat.mul_one, memRegion_two]
      wp_conv_pre => rw [hmem2]
      wp_pull_exists
      wp_steps 4
      have hslice_nil :
          ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16) =
            gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (lagrangePreparePure a.pts).coefficients := by
        rw [hpts_nil]
        simp [lagrangePreparePure, prepareLoopPure, gf16SliceAt, arrayAt, gf16At, GF16.ONE]
      wp_conv_pre => rw [hslice_nil]
      refine epilogue_sepWP A b ext a R s0 _ (sf_1.readReg64 (Reg.gpr 0#5))
        _ _ _ a.ptsPtr _ _ _ _ _ _ _ _ hsp0 hptr0 ?_ ?_ ?_ ?_ ?_
      · dsimp only [tripleRatchetProgAtExt]; rw [hentry]; wp_norm_lhs
      · wp_norm_lhs
      · change sf_1.sp = s0.sp - 208#64; rw [hsp_sf, h_4]
      · change sf_1.trace = s0.trace; rw [htr_ok, h_3]
      · change calleeSavedVRegs sf_1 = calleeSavedVRegs s0; rw [hvregs_1, hvregs]
    · -- Non-empty input slice (`a.pts ≠ []`): `memset` buffer and run outer loop
      have hlen_pos : 0 < a.pts.length := List.length_pos_iff.mpr hpts_nil
      have hx20_ne0 : (BitVec.ofNat 64 a.pts.length == 0#64) = false := by
        rw [beq_eq_false_iff_ne]
        intro h0
        have ht := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
        change a.pts.length = 0 at ht
        omega
      have hsub_shl :
          (BitVec.ofNat 64 (a.pts.length + 1) + 0xffffffff_ffffffff#64) <<< (1 : Nat) =
            BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_succ_sub_one_shl_one a.pts.length
      have htoNat_len : (BitVec.ofNat 64 (2 * a.pts.length)).toNat = 2 * a.pts.length :=
        ofNat_two_mul_toNat a.pts.length hbound
      have hsplit_alloc :
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
            memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * a.pts.length) ∗
              (∃∗ v_last : BitVec 16,
                (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) ↦₁₆ v_last) :=
        memRegion_alloc_split (sf_1.readReg64 (Reg.gpr 0#5)) a.pts.length (by omega)
      wp_conv_pre => rw [hsplit_alloc]
      wp_pull_exists
      wp_steps 5
      wp_call hmemset
      have hrep_zero :
          (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ
            List.replicate (BitVec.ofNat 64 (2 * (a.pts.length + 1)) - 2#64).toNat 0#8) =
            gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (List.replicate a.pts.length GF16.ZERO) := by
        rw [sub_two_toNat_eq a.pts.length hbound, gf16SliceAt_replicate_zero]
      have hadrp_c90 :
          (entry + 116#64) &&& 0xfffffffffffff000#64 =
            b + bv% (page% (ls_off% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare")) := by
        rw [← hentry]; exact fnAddr_adrp_61c90 hb
      have hshl_len : BitVec.ofNat 64 a.pts.length <<< (1 : Nat) = BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_shl_one_nat a.pts.length
      have hshl_len' : BitVec.ofNat 64 a.pts.length <<< 1#64 = BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_shl_one a.pts.length
      have hal_last :
          MemWidth.isAligned .W16
            (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) = true :=
        aligned16_add_mul_two (sf_1.readReg64 (Reg.gpr 0#5)) hptr_al a.pts.length
      wp_conv_pre => rw [hrep_zero]
      wp_steps 7
      wp_conv_pre => rw [combine_init_slice, outerLoop_frame_eq]
      have hx19_init :
          sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length) - 2#64 =
            sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * (a.pts.length - 1)) := by
        have hlen_eq : a.pts.length = (a.pts.length - 1) + 1 := by omega
        conv => lhs; arg 1; arg 2; rw [hlen_eq]
        exact ptr_sub_two_succ (sf_1.readReg64 (Reg.gpr 0#5)) (a.pts.length - 1)
      apply outerLoop_sepWP b ext hb s0.sp (sf_1.readReg64 (Reg.gpr 0#5)) a.ptsPtr
        hsp0 hptr_al a.pts (by omega) (s0.readReg64 Reg.lr) _
        (a.pts.length - 1) 0 ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩
        (by omega) (by simp)
        _ _ _ _ _ _ _ _ _ _
        (by rw [hentry]; wp_norm_lhs)
        (by wp_norm_lhs)
        (by change sf_2.sp = s0.sp - 208#64; rw [hsp_sf_1, hsp_sf, h_4])
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hx19_init)
        (by simp only [arm64_norm, wp_norm, h_26, h_16, h_6])
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hcs_sf_1, hcs_sf, hpost_sf])
      intro v160' v152' v144' w132' w128' w124' w120' w116' sf_loop hpc_loop hrun_loop hsp_loop htr_loop hvregs_loop
      have hloop_eq :
          prepareLoopPure a.pts a.pts.length 0 (a.pts.length - 1 + 1)
            ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩ =
            lagrangePreparePure a.pts := by
        rw [Nat.sub_add_cancel hlen_pos]
        rfl
      wp_conv_pre => rw [hloop_eq, ← outerLoop_frame_eq]
      exact epilogue_sepWP A b ext a R s0 sf_loop (sf_1.readReg64 (Reg.gpr 0#5))
        _ _ _ a.ptsPtr v160' v152' v144' w132' w128' w124' w120' w116' hsp0 hptr0
        hpc_loop hrun_loop hsp_loop
        (by
          rw [htr_loop]
          change sf_2.trace = s0.trace
          rw [hpost, htr_ok, h_3])
        (by
          rw [hvregs_loop]
          change calleeSavedVRegs sf_2 = calleeSavedVRegs s0
          rw [hvregs_2, hvregs_1, hvregs])

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `372`) -/

set_option maxHeartbeats 1600000 in
private theorem outerStep_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 ptr ptsPtr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (pts : List Pt) (hn_bound : pts.length + 1 < 2 ^ 63)
    (r_out i : Nat) (p : Poly)
    (hi_rem : i + (r_out + 1) = pts.length) (hp_len : p.coefficients.length = pts.length + 1)
    (hi : i < pts.length)
    (v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (blkPl_372).base + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 208#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out))
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 pts.length)
    (hx23 : s.readReg64 .x23 = lsρ reduceTableSym)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1))
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_372).base + 588#64 →
      sf.status = .Running →
      sf.sp = sp0 - 208#64 →
      sf.trace = s.trace →
      sf.pstate = subsPState64 (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 pts.length) →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out) - 2#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 pts.length →
      sf.readReg64 .x23 = lsρ reduceTableSym →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1) - 1#64 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 10) ∗
         ((sp0 - 128#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 11) ∗
         ((sp0 - 124#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 12) ∗
         ((sp0 - 120#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 13) ∗
         ((sp0 - 116#64) ↦₃₂ sbfxMask32 (pts[i]'hi).x.value 14) ∗
         gf16SliceAt ptr
           (multXdiffLoopPure (pts[i]'hi).x (r_out + 1) (i + 1) p.coefficients) ∗
         reduceTablePlacedAt ∗
         ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
         ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         ((sp0 - 152#64) ↦₆₄ (0#64 - BitVec.ofNat 64 (i + 1))) ∗
         ((sp0 - 144#64) ↦₆₄ (ptr + BitVec.ofNat 64 (2 * r_out))) ∗
         ptSliceAt ptsPtr pts ∗ F) Q) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
      (tokenInitPlacedAt ∗
       ((sp0 - 132#64) ↦₃₂ w132) ∗
       ((sp0 - 128#64) ↦₃₂ w128) ∗
       ((sp0 - 124#64) ↦₃₂ w124) ∗
       ((sp0 - 120#64) ↦₃₂ w120) ∗
       ((sp0 - 116#64) ↦₃₂ w116) ∗
       gf16SliceAt ptr p.coefficients ∗
       reduceTablePlacedAt ∗
       ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
       ((sp0 - 160#64) ↦₆₄ v160) ∗
       ((sp0 - 152#64) ↦₆₄ v152) ∗
       ((sp0 - 144#64) ↦₆₄ v144) ∗
       ptSliceAt ptsPtr pts ∗ F) Q := by
  have hi_succ : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add]
  wp_conv_pre => rw [ptSliceAt_focus_x_assoc hi ptsPtr]
  wp_steps 20
  wp_conv_pre => rw [← ptSliceAt_focus_x_assoc hi ptsPtr]
  apply innerLoop_placed_sepWP ext sp0 ptr hptr_al pts.length hn_bound (pts[i]'hi).x.value
    ret_pc Q i (r_out + 1) p.coefficients (by omega) (by omega) hp_len _
    (((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
     ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
     ((sp0 - 152#64) ↦₆₄ (0#64 - BitVec.ofNat 64 (i + 1))) ∗
     ((sp0 - 144#64) ↦₆₄ (ptr + BitVec.ofNat 64 (2 * r_out))) ∗
     ptSliceAt ptsPtr pts ∗ F)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx19)
    (by simpa [arm64_norm, wp_norm] using hx20)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx23)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx27)
    (by simp only [arm64_norm, wp_norm]; exact sbfxMask64_from_if _ _)
    (by simpa [arm64_norm, wp_norm] using hx29)
  intro s1 hpc1 hrun1 hsp1 htrace1 hx20_1 hx23_1 hx29_1 hvregs1
  have hsp1' : s1.sp = sp0 - 208#64 := by rw [hsp1]; simpa [arm64_norm, wp_norm] using hsp
  have htrace1' : s1.trace = s.trace := by simpa [arm64_norm, wp_norm] using htrace1
  have hvregs1' : calleeSavedVRegs s1 = calleeSavedVRegs s := by simpa [arm64_norm, wp_norm] using hvregs1
  wp_steps 5
  apply hnext _ (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp1')
    (by simpa [arm64_norm, wp_norm] using htrace1')
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx20_1)
    (by simpa [arm64_norm, wp_norm] using hx23_1)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hx29_1)
    (by simpa [arm64_norm, wp_norm] using hvregs1')

set_option maxHeartbeats 1600000 in
private theorem outerLoop_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 ptr ptsPtr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64) (hptr_al : ptr &&& 1#64 = 0#64)
    (pts : List Pt) (hn_bound : pts.length + 1 < 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r_out i : Nat) (p : Poly)
      (_hi_rem : i + (r_out + 1) = pts.length) (_hp_len : p.coefficients.length = pts.length + 1)
      (v160 v152 v144 : BitVec 64)
      (w132 w128 w124 w120 w116 : BitVec 32)
      (s : State) (F : SepProp),
      s.pc = (blkPl_372).base + 132#64 →
      s.status = .Running →
      s.sp = sp0 - 208#64 →
      s.readReg64 .x9 = BitVec.ofNat 64 i →
      s.readReg64 .x19 = ptr + BitVec.ofNat 64 (2 * r_out) →
      s.readReg64 .x20 = BitVec.ofNat 64 pts.length →
      s.readReg64 .x23 = lsρ reduceTableSym →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 (i + 1) →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ (v160' v152' v144' : BitVec 64) (w132' w128' w124' w120' w116' : BitVec 32) (sf : State),
        sf.pc = (blkPl_372).base + 608#64 →
        sf.status = .Running →
        sf.sp = sp0 - 208#64 →
        sf.trace = s.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc sf
          (tokenInitPlacedAt ∗
           ((sp0 - 132#64) ↦₃₂ w132') ∗
           ((sp0 - 128#64) ↦₃₂ w128') ∗
           ((sp0 - 124#64) ↦₃₂ w124') ∗
           ((sp0 - 120#64) ↦₃₂ w120') ∗
           ((sp0 - 116#64) ↦₃₂ w116') ∗
           gf16SliceAt ptr (prepareLoopPure pts pts.length i (r_out + 1) p).coefficients ∗
           reduceTablePlacedAt ∗
           ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
           ((sp0 - 160#64) ↦₆₄ v160') ∗
           ((sp0 - 152#64) ↦₆₄ v152') ∗
           ((sp0 - 144#64) ↦₆₄ v144') ∗
           ptSliceAt ptsPtr pts ∗ F) Q) →
      SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) ret_pc s
        (tokenInitPlacedAt ∗
         ((sp0 - 132#64) ↦₃₂ w132) ∗
         ((sp0 - 128#64) ↦₃₂ w128) ∗
         ((sp0 - 124#64) ↦₃₂ w124) ∗
         ((sp0 - 120#64) ↦₃₂ w120) ∗
         ((sp0 - 116#64) ↦₃₂ w116) ∗
         gf16SliceAt ptr p.coefficients ∗
         reduceTablePlacedAt ∗
         ((sp0 - 168#64) ↦₆₄ ptsPtr) ∗
         ((sp0 - 160#64) ↦₆₄ v160) ∗
         ((sp0 - 152#64) ↦₆₄ v152) ∗
         ((sp0 - 144#64) ↦₆₄ v144) ∗
         ptSliceAt ptsPtr pts ∗ F) Q := by
  intro r_out
  induction r_out with
  | zero =>
    intro i p hi_rem hp_len v160 v152 v144 w132 w128 w124 w120 w116 s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29 hnext
    have hi : i < pts.length := by omega
    apply outerStep_placed_sepWP ext sp0 ptr ptsPtr hsp0 hptr_al pts hn_bound
      0 i p hi_rem hp_len hi v160 v152 v144 w132 w128 w124 w120 w116 ret_pc Q s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 hpstate1 _hx9_1 _hx19_1 _hx20_1 _hx23_1 _hx27_1 _hx29_1 hvregs1
    have heq_len : i + 1 = pts.length := by omega
    rw [heq_len] at hpstate1
    wp_steps 2
    rw [prepareLoopPure_succ pts i 0 p hi_rem hp_len hi] at hnext
    dsimp only [prepareLoopPure] at hnext
    exact hnext
      (BitVec.ofNat 64 (i + 1)) (0#64 - BitVec.ofNat 64 (i + 1)) (ptr + BitVec.ofNat 64 (2 * 0))
      (sbfxMask32 (pts[i]'hi).x.value 10) (sbfxMask32 (pts[i]'hi).x.value 11)
      (sbfxMask32 (pts[i]'hi).x.value 12) (sbfxMask32 (pts[i]'hi).x.value 13)
      (sbfxMask32 (pts[i]'hi).x.value 14) _
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htrace1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r_out' ih =>
    intro i p hi_rem hp_len v160 v152 v144 w132 w128 w124 w120 w116 s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29 hnext
    have hi : i < pts.length := by omega
    apply outerStep_placed_sepWP ext sp0 ptr ptsPtr hsp0 hptr_al pts hn_bound
      (r_out' + 1) i p hi_rem hp_len hi v160 v152 v144 w132 w128 w124 w120 w116 ret_pc Q s F
      hpc hrun hsp hx9 hx19 hx20 hx23 hx27 hx29
    intro s1 hpc1 hrun1 hsp1 htrace1 hpstate1 hx9_1 hx19_1 hx20_1 hx23_1 hx27_1 hx29_1 hvregs1
    have hne_len := ofNat_bne_true_of_lt (a := i + 1) (b := pts.length) (by omega) (by omega)
    wp_steps 1
    apply ih (i + 1) ⟨multXdiffLoopPure (pts[i]'hi).x (r_out' + 1 + 1) (i + 1) p.coefficients⟩
      (by omega) (by simp [multXdiffLoopPure_length, hp_len])
      (BitVec.ofNat 64 (i + 1)) (0#64 - BitVec.ofNat 64 (i + 1)) (ptr + BitVec.ofNat 64 (2 * (r_out' + 1)))
      (sbfxMask32 (pts[i]'hi).x.value 10) (sbfxMask32 (pts[i]'hi).x.value 11)
      (sbfxMask32 (pts[i]'hi).x.value 12) (sbfxMask32 (pts[i]'hi).x.value 13)
      (sbfxMask32 (pts[i]'hi).x.value 14) _ F
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx9_1)
      (by simpa [arm64_norm, wp_norm, ptr_sub_two_succ ptr r_out'] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm, neg_sub_one (i + 1)] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
    intro v160' v152' v144' w132' w128' w124' w120' w116' sf hpc_f hrun_f hsp_f htrace_f hvregs_f
    rw [prepareLoopPure_succ pts i (r_out' + 1) p hi_rem hp_len hi] at hnext
    exact hnext v160' v152' v144' w132' w128' w124' w120' w116' sf hpc_f hrun_f hsp_f
      (by rw [htrace_f]; simpa [arm64_norm, wp_norm] using htrace1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

private theorem epilogue_placed_sepWP [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (a : LagrangePrepareArgs) (R : SepProp) (s0 s : State)
    (ptr o0 o1 o2 : BitVec 64)
    (v168 v160 v152 v144 : BitVec 64)
    (w132 w128 w124 w120 w116 : BitVec 32)
    (hsp_align : s0.sp &&& 0xf#64 = 0#64)
    (hptr_ne : ptr ≠ 0#64)
    (hpc : s.pc = (blkPl_372).base + 608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        A.live ptr (2 * (a.pts.length + 1)) 2 ∗
        gf16SliceAt ptr (lagrangePreparePure a.pts).coefficients ∗
        (a.out ↦₆₄ o0) ∗ ((a.out + 8#64) ↦₆₄ o1) ∗ ((a.out + 16#64) ↦₆₄ o2) ∗
        ptSliceAt a.ptsPtr a.pts ∗
        reduceTablePlacedAt ∗
        tokenInitPlacedAt ∗
        memRegion (s0.sp - 208#64) 16 ∗
        ((s0.sp - 192#64) ↦₆₄ ptr) ∗
        ((s0.sp - 184#64) ↦₆₄ a.out) ∗
        ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 (a.pts.length + 1)) ∗
        ((s0.sp - 168#64) ↦₆₄ v168) ∗
        ((s0.sp - 160#64) ↦₆₄ v160) ∗
        ((s0.sp - 152#64) ↦₆₄ v152) ∗
        ((s0.sp - 144#64) ↦₆₄ v144) ∗
        memRegion (s0.sp - 136#64) 4 ∗
        ((s0.sp - 132#64) ↦₃₂ w132) ∗
        ((s0.sp - 128#64) ↦₃₂ w128) ∗
        ((s0.sp - 124#64) ↦₃₂ w124) ∗
        ((s0.sp - 120#64) ↦₃₂ w120) ∗
        ((s0.sp - 116#64) ↦₃₂ w116) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜sf.trace = s0.trace⌝ ∗
              polyOf A a.out (lagrangePreparePure a.pts) ∗
                ptSliceAt a.ptsPtr a.pts ∗
                  reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗ stackAt s0.sp lagrangePrepareStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  wp_steps
  refine SepWP.fold
    (stackAt_lagrangePrepare_merge s0.sp (s0.sp - 208#64)
      ptr a.out (BitVec.ofNat 64 (a.pts.length + 1)) v168 v160 v152 v144
      w132 w128 w124 w120 w116
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
      rfl)
    (by sep_focus) ?_
  refine SepWP.fold
    (polyOf_of_exact_cap A a.out ptr (lagrangePreparePure a.pts) (a.pts.length + 1)
      (by omega) (lagrangePreparePure_length a.pts) (by omega) hptr_ne)
    (by sep_focus) ?_
  wp_done

/-- Relocatable (`[LibsignalPlacement]`) `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare`
(Block `372`) satisfies `lagrangePreparePlacedSpec A`. -/
theorem lagrangePrepare_placed_ok [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) SpqrV1.Alloc.spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ SpqrV1.Alloc.spqrRustNoAllocShimSym) sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ SpqrV1.Alloc.spqrRustAllocSym) (rustAllocSpec A))
    (hmemset : subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (lsρ memsetName) sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (blkPl_372).base (lagrangePreparePlacedSpec A) := by
  have hpan_err :
      ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext)).externAt?
        (lsρ SpqrV1.Alloc.spqrHandleErrorSym) = some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  simp only [lagrangePreparePlacedSpec]
  wpp_init a s0
  have hsp0 : s0.sp &&& 0xf#64 = 0#64 := beq_iff_eq.mp hsp_align
  have hbound : 4 * (a.pts.length + 1) < 2 ^ 63 := a.hlen_bound
  have hbit62 : (((BitVec.ofNat 64 a.pts.length + 1#64) &&& 4611686018427387904#64) != 0#64) = false :=
    len_succ_bit62_false a.pts.length hbound
  have hshl_succ : (BitVec.ofNat 64 a.pts.length + 1#64) <<< 1#64 = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one a.pts.length
  have hshl_succ_nat : (BitVec.ofNat 64 a.pts.length + 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one_nat a.pts.length
  have htoNat_succ : (BitVec.ofNat 64 (2 * (a.pts.length + 1))).toNat = 2 * (a.pts.length + 1) :=
    ofNat_two_mul_succ_toNat a.pts.length hbound
  have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  apply SepWPp.of_sepWP (mid := (blkPl_372).base + 68#64)
  wp_simp_pre only [memRegion_24 a.out, stackAt_lagrangePrepare_split s0.sp]
  wp_pull_exists
  wp_steps 14
  wp_call hshim
  wp_steps 3
  wp_call halloc
  apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
  by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hptr0
    wp_conv_pre => rw [alloc_post_pos hptr0]
    apply SepWPp.pure_left
    intro htr_fail
    apply SepWPp.of_sepWP (mid := lsρ SpqrV1.Alloc.spqrHandleErrorSym)
    wp_steps 4
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have htr_panic_eq :
        (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 2#64).writeReg64 (Reg.gpr 1#5)
          (BitVec.ofNat 64 (2 * (a.pts.length + 1)))).writeReg64 (Reg.gpr 30#5)
          ((blkPl_372).base + 680#64)).setPC
          (lsρ SpqrV1.Alloc.spqrHandleErrorSym))).trace = s0.trace ++ [allocFailedEvent] := by
      change sf_1.trace = s0.trace ++ [allocFailedEvent]
      rw [htr_fail, h_3]
    refine SepWPp.panic (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hpan_err)
      (fun hm => ?_)
    rw [← sepConj_assoc]
    refine allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _) ⟨?_, ?_⟩ hm
    · exact allocFailedIn_of_trace_eq htr_panic_eq
    · rw [htr_panic_eq]; exact List.prefix_append s0.trace [allocFailedEvent]
  · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
    wp_conv_pre => rw [alloc_post_neg hptr0]
    apply SepWPp.pure_left
    rintro ⟨hptr_mod, htr_ok⟩
    apply SepWPp.of_sepWP_ret
    have hptr_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
      and_one_of_mod_two hptr_mod
    have hlen_add1 : BitVec.ofNat 64 a.pts.length + 1#64 = BitVec.ofNat 64 (a.pts.length + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    wp_conv_pre => rw [h_4]
    wp_steps 4
    by_cases hpts_nil : a.pts = []
    · have hx20_0 : (BitVec.ofNat 64 a.pts.length == 0#64) = true := by rw [hpts_nil]; rfl
      have hmem2 :
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
            ∃∗ v0 : BitVec 16, (sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ v0 := by
        rw [hpts_nil, List.length_nil, Nat.zero_add, Nat.mul_one, memRegion_two]
      wp_conv_pre => rw [hmem2]
      wp_pull_exists
      wp_steps 4
      have hslice_nil :
          ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16) =
            gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (lagrangePreparePure a.pts).coefficients := by
        rw [hpts_nil]
        simp [lagrangePreparePure, prepareLoopPure, gf16SliceAt, arrayAt, gf16At, GF16.ONE]
      wp_conv_pre => rw [hslice_nil]
      refine epilogue_placed_sepWP A ext a R s0 _ (sf_1.readReg64 (Reg.gpr 0#5))
        _ _ _ a.ptsPtr _ _ _ _ _ _ _ _ hsp0 hptr0 ?_ ?_ ?_ ?_ ?_
      · wp_norm_lhs
      · wp_norm_lhs
      · change sf_1.sp = s0.sp - 208#64; rw [hsp_sf, h_4]
      · change sf_1.trace = s0.trace; rw [htr_ok, h_3]
      · change calleeSavedVRegs sf_1 = calleeSavedVRegs s0; rw [hvregs_1, hvregs]
    · have hlen_pos : 0 < a.pts.length := List.length_pos_iff.mpr hpts_nil
      have hx20_ne0 : (BitVec.ofNat 64 a.pts.length == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; intro h0
        have ht := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
        change a.pts.length = 0 at ht; omega
      have hsub_shl :
          (BitVec.ofNat 64 (a.pts.length + 1) + 0xffffffff_ffffffff#64) <<< (1 : Nat) =
            BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_succ_sub_one_shl_one a.pts.length
      have htoNat_len : (BitVec.ofNat 64 (2 * a.pts.length)).toNat = 2 * a.pts.length :=
        ofNat_two_mul_toNat a.pts.length hbound
      have hsplit_alloc :
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * (a.pts.length + 1)) =
            memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * a.pts.length) ∗
              (∃∗ v_last : BitVec 16,
                (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) ↦₁₆ v_last) :=
        memRegion_alloc_split (sf_1.readReg64 (Reg.gpr 0#5)) a.pts.length (by omega)
      wp_conv_pre => rw [hsplit_alloc]
      wp_pull_exists
      wp_steps 5
      wp_call hmemset
      have hrep_zero :
          (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ
            List.replicate (BitVec.ofNat 64 (2 * (a.pts.length + 1)) - 2#64).toNat 0#8) =
            gf16SliceAt (sf_1.readReg64 (Reg.gpr 0#5)) (List.replicate a.pts.length GF16.ZERO) := by
        rw [sub_two_toNat_eq a.pts.length hbound, gf16SliceAt_replicate_zero]
      have hshl_len : BitVec.ofNat 64 a.pts.length <<< (1 : Nat) = BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_shl_one_nat a.pts.length
      have hshl_len' : BitVec.ofNat 64 a.pts.length <<< 1#64 = BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_shl_one a.pts.length
      have hal_last :
          MemWidth.isAligned .W16
            (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) = true :=
        aligned16_add_mul_two (sf_1.readReg64 (Reg.gpr 0#5)) hptr_al a.pts.length
      wp_conv_pre => rw [hrep_zero]
      wp_steps 7
      wp_conv_pre => rw [combine_init_slice, outerLoop_frame_eq]
      have hx19_init :
          sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length) - 2#64 =
            sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * (a.pts.length - 1)) := by
        have hlen_eq : a.pts.length = (a.pts.length - 1) + 1 := by omega
        conv => lhs; arg 1; arg 2; rw [hlen_eq]
        exact ptr_sub_two_succ (sf_1.readReg64 (Reg.gpr 0#5)) (a.pts.length - 1)
      apply outerLoop_placed_sepWP ext s0.sp (sf_1.readReg64 (Reg.gpr 0#5)) a.ptsPtr
        hsp0 hptr_al a.pts (by omega) (s0.readReg64 Reg.lr) _
        (a.pts.length - 1) 0 ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩
        (by omega) (by simp)
        _ _ _ _ _ _ _ _ _ _
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by change sf_2.sp = s0.sp - 208#64; rw [hsp_sf_1, hsp_sf, h_4])
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hx19_init)
        (by simp only [arm64_norm, wp_norm, h_26, h_16, h_6])
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simp only [arm64_norm, wp_norm, hcs_sf_1, hcs_sf, hpost_sf])
      intro v160' v152' v144' w132' w128' w124' w120' w116' sf_loop hpc_loop hrun_loop hsp_loop htr_loop hvregs_loop
      have hloop_eq :
          prepareLoopPure a.pts a.pts.length 0 (a.pts.length - 1 + 1)
            ⟨List.replicate a.pts.length GF16.ZERO ++ [GF16.ONE]⟩ =
            lagrangePreparePure a.pts := by
        rw [Nat.sub_add_cancel hlen_pos]; rfl
      wp_conv_pre => rw [hloop_eq, ← outerLoop_frame_eq]
      exact epilogue_placed_sepWP A ext a R s0 sf_loop (sf_1.readReg64 (Reg.gpr 0#5))
        _ _ _ a.ptsPtr v160' v152' v144' w132' w128' w124' w120' w116' hsp0 hptr0
        hpc_loop hrun_loop hsp_loop
        (by rw [htr_loop]; change sf_2.trace = s0.trace; rw [hpost, htr_ok, h_3])
        (by rw [hvregs_loop]; change calleeSavedVRegs sf_2 = calleeSavedVRegs s0; rw [hvregs_2, hvregs_1, hvregs])

theorem lagrangePrepare_placed_ok_of_hookSat [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) SpqrV1.Alloc.spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) SpqrV1.Alloc.spqrRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat (Rust.withPanics ext) SpqrV1.Alloc.spqrRustAllocSym (rustAllocSpec A))
    (hmemset : HookSat (Rust.withPanics ext) memsetName sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_372).rebase (blkPl_372).base (Rust.withPanics ext))
      (blkPl_372).base (lagrangePreparePlacedSpec A) :=
  lagrangePrepare_placed_ok A ext h_panic
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hshim)
    (SpqrV1.Alloc.spqr_hook_ok_of_mem halloc)
    (SpqrV1.Alloc.spqr_hook_ok_of_mem hmemset)

end CryptoVerification.SpqrV1.Poly.LagrangePrepare
