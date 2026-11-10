/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<Poly>::lagrange_interpolate_prepare`: `AllocContracts4K` Verification

Lifts `lagrangePrepare_ok` to `AllocContracts4K b A ext` (`withStack sessionMemsetRegionSpec
allocHookStack`) at the unchanged stack budget `lagrangePrepareStack = 0xd0 + allocHookStack`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocFailedEvent allocFailedIn allocHookStack arrayAt)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.LibsignalTripleRatchet (panic_at_handle_error_ext
  subroutine_ok_inImage_of_subroutine_ok tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceBytesOff reduceTableAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt zeroExtend_16_truncate_32_64)
open CryptoVerification.SpqrV1.Poly (gf16At gf16SliceAt polyOf ptSliceAt)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (LagrangePrepareArgs adds_neg_one_carry
  aligned16_add_mul_two and_65535_zext64_16 and_one_of_mod_two fnAddr_adrp_61c90
  gf16SliceAt_append_singleton gf16SliceAt_replicate_zero innerStep_sepWP
  lagrangePrepareName lagrangePreparePure lagrangePreparePure_length lagrangePrepareSpec
  lagrangePrepareStack lagrangePrepare_fnOff memRegion_24 memRegion_alloc_split
  multXdiffLoopPure multXdiffLoopPure_length multXdiffLoopPure_succ neg_sub_one neg_succ_add_one
  neg_succ_ule_add_one ofNat_bne_true_of_lt ofNat_shl_two polyOf_of_exact_cap prepareLoopPure
  prepareLoopPure_succ prepare_polyReduce_xor_eq ptSliceAt_focus_x_assoc ptr_sub_two_succ
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre sbfx64_one_eq sbfxMask32 sbfxMask64
  sbfxMask64_from_if sp_setMem_setPC_pre sp_setPC_pre stackAt_lagrangePrepare_merge
  stackAt_lagrangePrepare_split sxth32Zext64 truncate32_if_all_ones truncate32_sext64_16
  truncate32_zext64 zext64_zext32_16)

namespace LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofExt

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
local elab "lagrangePrepare_fetches_ext " b:term:max H:term:max st:num ln:num : tactic => do
  let codeName := `CryptoVerification.libsignalSessionCode
  let binName := `CryptoVerification.SpqrV1.Poly.LagrangePrepare.lagrangePrepareBin
  let eOff ← ProofLib.CodeLookup.lookup codeName .fnOff
    "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches_range $(mkCIdent codeName) $(mkIdent binName) $b $H $hfn
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
    intro s1 hpc1 hrun1 hsp1 htrace1 _hpstate1 _hx19_1 hx20_1 _hx21_1 _hx22_1 hx23_1 _hx24_1 _hx25_1 _hx26_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x234 4
    have _hcarry := adds_neg_one_carry
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
    intro s1 hpc1 hrun1 hsp1 htrace1 _hpstate1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1
    lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x234 4
    have _hcarry := neg_succ_ule_add_one (r := r) (by omega)
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
    examples_hide_fetches
    wp_steps 1
    rw [← hentry]
    apply ih (k + 1)
      (cs.set (k - 1) ⟨(cs[k - 1]'hk_prev).value ^^^
        CryptoVerification.LibsignalSpqrV1.unaccelerated.mul (cs[k]'hk).value yv⟩)
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
  lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x84 80
  lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x238 20
  have _hi_succ : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
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
    lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x24c 8
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
    intro s1 hpc1 hrun1 hsp1 htrace1 _hpstate1 hx9_1 hx19_1 hx20_1 hx23_1 hx27_1 hx29_1 hvregs1
    lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x24c 4
    have _hne_len := ofNat_bne_true_of_lt (a := i + 1) (b := pts.length) (by omega) (by omega)
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
  lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x260 48
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry _hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr lagrangePrepareName = entry
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

private theorem len_succ_bit62_false (n : Nat) (h : 4 * (n + 1) < 2 ^ 63) :
    (((BitVec.ofNat 64 n + 1#64) &&& 4611686018427387904#64) != 0#64) = false := by
  have h1 : BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  rw [h1, bne_eq_false_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have h62 : n + 1 < 2 ^ 62 := by omega
  have h64 : n + 1 < 2 ^ 64 := by omega
  have hlt : (BitVec.ofNat 64 (n + 1)).toNat < 2 ^ 62 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
    exact h62
  have hpow : (4611686018427387904#64).toNat = 2 ^ 62 := rfl
  rw [hpow]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hk : 62 = k
  · subst hk
    rw [Nat.testBit_lt_two_pow hlt]
    rfl
  · simp [hk]

private theorem ofNat_shl_one_nat (n : Nat) :
    BitVec.ofNat 64 n <<< (1 : Nat) = BitVec.ofNat 64 (2 * n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 1 = BitVec.ofNat 64 2 from rfl,
    ← BitVec.ofNat_mul, Nat.mul_comm]

private theorem ofNat_shl_one (n : Nat) :
    BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 (2 * n) :=
  ofNat_shl_one_nat n

private theorem ofNat_add_one_shl_one (n : Nat) :
    (BitVec.ofNat 64 n + 1#64) <<< 1#64 = BitVec.ofNat 64 (2 * (n + 1)) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  exact ofNat_shl_one (n + 1)

private theorem ofNat_add_one_shl_one_nat (n : Nat) :
    (BitVec.ofNat 64 n + 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (n + 1)) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  exact ofNat_shl_one_nat (n + 1)

private theorem ofNat_succ_sub_one_shl_one (r : Nat) :
    (BitVec.ofNat 64 (r + 1) + 0xffffffff_ffffffff#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * r) := by
  have hsub : BitVec.ofNat 64 (r + 1) + 0xffffffff_ffffffff#64 = BitVec.ofNat 64 r := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    exact BitVec.add_zero _
  rw [hsub]
  exact ofNat_shl_one_nat r

private theorem ofNat_two_mul_succ_toNat (n : Nat) (h : 4 * (n + 1) < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * (n + 1))).toNat = 2 * (n + 1) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem ofNat_two_mul_toNat (n : Nat) (h : 4 * (n + 1) < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem allocFailedIn_of_trace_eq_lp {s0 sf : State}
    (ht : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn
  rw [ht, List.drop_left]
  exact List.Mem.head []

private theorem pull_pure_after_two (P1 P2 : SepProp) (φ : Prop) (Rest : SepProp) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  rw [← sepConj_assoc P2 ⌜φ⌝ Rest, sepConj_comm P2 ⌜φ⌝, sepConj_assoc ⌜φ⌝ P2 Rest,
      ← sepConj_assoc P1 ⌜φ⌝ (P2 ∗ Rest), sepConj_comm P1 ⌜φ⌝, sepConj_assoc ⌜φ⌝ P1 (P2 ∗ Rest)]

private theorem alloc_post_pos {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ : Prop} {Q : SepProp}
    (h0 : x0 = 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else Q) ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  have h0' : x0 = 0 := h0
  simp only [h0', ↓reduceIte]
  exact pull_pure_after_two P1 P2 φ Rest

private theorem alloc_post_neg {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ ψ : Prop} {Q : SepProp}
    (h0 : x0 ≠ 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else ⌜ψ⌝ ∗ Q) ∗ Rest = ⌜ψ⌝ ∗ P1 ∗ P2 ∗ Q ∗ Rest := by
  have h0' : x0 ≠ 0 := h0
  simp only [h0', ↓reduceIte]
  rw [sepConj_assoc ⌜ψ⌝ Q Rest]
  exact pull_pure_after_two P1 P2 ψ (Q ∗ Rest)

private theorem sub_two_toNat_eq (n : Nat) (h : 4 * (n + 1) < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * (n + 1)) - 2#64).toNat = 2 * n := by
  have h1 : BitVec.ofNat 64 (2 * (n + 1)) - 2#64 = BitVec.ofNat 64 (2 * n) := by
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem combine_init_slice (ptr : BitVec 64) (n : Nat) (P1 P2 P3 Rest : SepProp) :
    gf16SliceAt ptr (List.replicate n GF16.ZERO) ∗ P1 ∗ P2 ∗ P3 ∗
      ((ptr + BitVec.ofNat 64 (2 * n)) ↦₁₆ 1#16) ∗ Rest =
      P1 ∗ P2 ∗ P3 ∗ gf16SliceAt ptr (List.replicate n GF16.ZERO ++ [GF16.ONE]) ∗ Rest := by
  have h1 : gf16SliceAt ptr (List.replicate n GF16.ZERO) ∗
      ((ptr + BitVec.ofNat 64 (2 * n)) ↦₁₆ 1#16) =
      gf16SliceAt ptr (List.replicate n GF16.ZERO ++ [GF16.ONE]) := by
    have hlen : (List.replicate n GF16.ZERO).length = n := List.length_replicate
    have h := gf16SliceAt_append_singleton (List.replicate n GF16.ZERO) GF16.ONE ptr
    rw [hlen] at h
    exact h.symm
  rw [← h1]
  exact ProofLib.sepProp_eq_of_entails (by sep_frame) (by sep_frame)

private theorem memset_post_reorder
    {sp_call sp_dst : BitVec 64} (hsp_eq : sp_call = sp_dst)
    (P_slice P_pool P_live Rest : SepProp) :
    P_slice ∗ stackAt sp_call allocHookStack ∗ P_pool ∗ P_live ∗ Rest =
      P_slice ∗ P_pool ∗ stackAt sp_dst allocHookStack ∗ P_live ∗ Rest := by
  rw [hsp_eq]
  exact ProofLib.sepProp_eq_of_entails (by sep_frame) (by sep_frame)

private theorem outerLoop_frame_eq
    (P_pool P_stk P_live P_slice P_o0 P_o1 P_o2 P_pts P_red P_tok
     P_m208 P_192 P_184 P_176 P_168 P_160 P_152 P_144
     P_m136 P_132 P_128 P_124 P_120 P_116 Tail : SepProp) :
    P_pool ∗ P_stk ∗ P_live ∗ P_slice ∗ P_o0 ∗ P_o1 ∗ P_o2 ∗
      P_pts ∗ P_red ∗ P_tok ∗
      P_m208 ∗ P_192 ∗ P_184 ∗ P_176 ∗ P_168 ∗ P_160 ∗ P_152 ∗ P_144 ∗
      P_m136 ∗ P_132 ∗ P_128 ∗ P_124 ∗ P_120 ∗ P_116 ∗ Tail =
    P_tok ∗ P_132 ∗ P_128 ∗ P_124 ∗ P_120 ∗ P_116 ∗ P_slice ∗ P_red ∗
      P_168 ∗ P_160 ∗ P_152 ∗ P_144 ∗ P_pts ∗
      (P_pool ∗ P_stk ∗ P_live ∗ P_o0 ∗ P_o1 ∗ P_o2 ∗
       P_m208 ∗ P_192 ∗ P_184 ∗ P_176 ∗ P_m136 ∗ Tail) :=
  ProofLib.sepProp_eq_of_entails (by sep_frame) (by sep_frame)

/-- `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare` satisfies
`lagrangePrepareSpec A b` under 4 KB `AllocContracts4K b A ext`. -/
theorem lagrangePrepare_ok_4k (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64)
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts4K b A ext) :
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
    allocHookStack (by decide) (by decide)
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
  lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x0 140
  lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x254 12
  lagrangePrepare_fetches_ext b (Rust.withPanics ext) 0x29c 12
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
  have _hbit62 : (((BitVec.ofNat 64 a.pts.length + 1#64) &&& 4611686018427387904#64) != 0#64) = false :=
    len_succ_bit62_false a.pts.length hbound
  have _hshl_succ : (BitVec.ofNat 64 a.pts.length + 1#64) <<< 1#64 = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one a.pts.length
  have _hshl_succ_nat : (BitVec.ofNat 64 a.pts.length + 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (a.pts.length + 1)) :=
    ofNat_add_one_shl_one_nat a.pts.length
  have _htoNat_succ : (BitVec.ofNat 64 (2 * (a.pts.length + 1))).toNat = 2 * (a.pts.length + 1) :=
    ofNat_two_mul_succ_toNat a.pts.length hbound
  have _hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
  apply SepWPp.of_sepWP (mid := entry + 68#64)
  wp_simp_pre only [memRegion_24 a.out, stackAt_lagrangePrepare_split s0.sp]
  wp_pull_exists
  wp_steps 14
  wp_call hshim
  wp_steps 3
  wp_call halloc
  apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
  by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · have _hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hptr0
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
    · exact allocFailedIn_of_trace_eq_lp htr_panic_eq
    · rw [htr_panic_eq]
      exact List.prefix_append s0.trace [allocFailedEvent]
  · have _hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
    wp_conv_pre => rw [alloc_post_neg hptr0]
    apply SepWPp.pure_left
    rintro ⟨hptr_mod, htr_ok⟩
    apply SepWPp.of_sepWP_ret
    have hptr_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
      and_one_of_mod_two hptr_mod
    have _hlen_add1 : BitVec.ofNat 64 a.pts.length + 1#64 = BitVec.ofNat 64 (a.pts.length + 1) := by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    have hsp_sf1 : sf_1.sp = s0.sp - 208#64 := by
      rw [hsp_sf, h_4]
    wp_conv_pre => rw [h_4]
    wp_steps 4
    by_cases hpts_nil : a.pts = []
    · have _hx20_0 : (BitVec.ofNat 64 a.pts.length == 0#64) = true := by
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
      · exact hsp_sf1
      · change sf_1.trace = s0.trace; rw [htr_ok, h_3]
      · change calleeSavedVRegs sf_1 = calleeSavedVRegs s0; rw [hvregs_1, hvregs]
    · have hlen_pos : 0 < a.pts.length := List.length_pos_iff.mpr hpts_nil
      have _hx20_ne0 : (BitVec.ofNat 64 a.pts.length == 0#64) = false := by
        rw [beq_eq_false_iff_ne]
        intro h0
        have ht := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
        change a.pts.length = 0 at ht
        omega
      have _hsub_shl :
          (BitVec.ofNat 64 (a.pts.length + 1) + 0xffffffff_ffffffff#64) <<< (1 : Nat) =
            BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_succ_sub_one_shl_one a.pts.length
      have _htoNat_len : (BitVec.ofNat 64 (2 * a.pts.length)).toNat = 2 * a.pts.length :=
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
      have _hadrp_c90 :
          (entry + 116#64) &&& 0xfffffffffffff000#64 =
            b + bv% (page% (ls_off% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare")) := by
        rw [← hentry]; exact fnAddr_adrp_61c90 hb
      have _hshl_len : BitVec.ofNat 64 a.pts.length <<< (1 : Nat) = BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_shl_one_nat a.pts.length
      have _hshl_len' : BitVec.ofNat 64 a.pts.length <<< 1#64 = BitVec.ofNat 64 (2 * a.pts.length) :=
        ofNat_shl_one a.pts.length
      have _hal_last :
          MemWidth.isAligned .W16
            (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (2 * a.pts.length)) = true :=
        aligned16_add_mul_two (sf_1.readReg64 (Reg.gpr 0#5)) hptr_al a.pts.length
      wp_conv_pre =>
        rw [hrep_zero, memset_post_reorder hsp_sf1]
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
        (by change sf_2.sp = s0.sp - 208#64; rw [hsp_sf_1]; simpa [arm64_norm, wp_norm] using hsp_sf1)
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

/-- `.inImage img` corollary of `lagrangePrepare_ok_4k` under `AllocContracts4K img.base A ext`. -/
theorem lagrangePrepare_ok_inImage_4k {img : Obj.Image} (hb : img.base &&& 0xfff#64 = 0#64)
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr lagrangePrepareName)
      ((lagrangePrepareSpec A img.base).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (lagrangePrepare_ok_4k img.base hb A ext hA)

end LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.Poly.LagrangePrepare
export LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofExt (
  lagrangePrepare_ok_4k
  lagrangePrepare_ok_inImage_4k
)
end CryptoVerification.SpqrV1.Poly.LagrangePrepare
-- AUTO-BRIDGE END
