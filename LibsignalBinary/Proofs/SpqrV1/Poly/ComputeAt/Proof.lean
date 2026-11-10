/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Phase
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.GrowOneExt
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::Poly>::compute_at`: Top-Level Proof

Proves `computeAt_ok` (`0x61914`) and `computeAt_placed_ok` (Block `371`) by composing prologue
allocation / `grow_one` dispatch with the `Phase.lean` loop and epilogue lemmas.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.ComputeAt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.GrowOneExt
  (grow_one_gf16_zero_ok_at_4k grow_one_gf16_one_ok_at_4k)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre
attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  ofNat_shl_one ofNat_shl_one_bv truncate16_zext64_trunc32 zext16_xor_trunc32
  Arm64.Obj.pageOf_add_lo12Of
attribute [local simp] growOneGF16ZeroSpec growOneGF16OneSpec

/-! ## Top-Level Theorem: `computeAt_ok` -/

set_option maxHeartbeats 1600000 in
private theorem computeAt_ok_core (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64)
    (A : RustAlloc) (ext : String → Option (State → State))
    (halloc0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hdealloc0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A))
    (hshim0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (hgrow0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName +
        bv% (2 ^ 64 +
          ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one" -
          ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
      (growOneGF16ZeroSpec A))
    (hgrow1 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName +
        bv% (2 ^ 64 +
          ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one" -
          ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
      (growOneGF16OneSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName)
      (computeAtSpec A b) := by
  have hfn : libsignalSessionCode.fnOff computeAtName =
      num% (ls_off% "<spqr::encoding::polynomial::Poly>::compute_at") := computeAt_fnOff
  have hshim := sub_ok_at_of_fnAddr hshim0 computeAtName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
    (by rw [computeAt_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := sub_ok_at_of_fnAddr halloc0 computeAtName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
    (by rw [computeAt_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  have hpan_err :
      (tripleRatchetProgAtExt b ext).externAt?
        ((tripleRatchetProgAtExt b ext).fnAddr computeAtName +
          bv% (ls_off% "alloc::raw_vec::handle_error" -
            ls_off% "<spqr::encoding::polynomial::Poly>::compute_at")) =
        some Rust.panicked :=
    panic_at_handle_error_ext b ext computeAtName
      (num% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
      (by rw [computeAt_fnOff, (ls_stub% "alloc::raw_vec::handle_error")])
  code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
    (Rust.withPanics ext) hfn 0x5c51c 0x0 96
  code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
    (Rust.withPanics ext) hfn 0x5c51c 0x2a4 104
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hgrow0 hgrow1 hpan_err ⊢
  clear hfn
  simp only [computeAtSpec]
  wpp_init a s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName := by
    rw [Program.fnAddr_rebase, computeAt_fnOff]; exact hpc
  clear hpc
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName = entry
  examples_hide_fetches
  have hsp0 : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
  have _h_4 : True := trivial
  by_cases hnil : a.poly.coefficients = []
  · -- Empty polynomial (`a.poly.coefficients = []`)
    have hx1_0 : (BitVec.ofNat 64 a.poly.coefficients.length == 0#64) = true := by
      rw [hnil]; rfl
    apply SepWPp.of_sepWP
      (mid := entry + bv% (2 ^ 64 +
        ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one" -
        ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
    wp_simp_pre only [stackAt_computeAt_split s0.sp]
    wp_pull_exists
    wp_steps 17
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    apply SepWPp.call_panic_to_sepWP hgrow0
      (s0 := s0)
      (x := s0.sp - 136#64)
      (ret_pc := entry + 696#64)
      (φ := True)
      (T := ((s0.sp - 136#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 136#64 + 8#64) ↦₆₄ 2#64) ∗
            A.pool ∗
            stackAt (s0.sp - 144#64) growOneStack)
    · wp_norm_lhs
    · wp_norm_lhs
    · simp only [State.spAligned, arm64_norm, wp_norm, beq_iff_eq]
      revert hsp0; bv_bits
    · wp_norm_lhs
    · wp_norm_lhs
    · dsimp only [growOneGF16ZeroSpec]
      simp only [arm64_norm, wp_norm]
    · trivial
    · exact grow0_pre_split s0.sp A _ _ _ _ _ _
    · intro _; rfl
    · intro _ _ _ _ hm; simp [satisfies_pure_sepConj] at hm
    · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
    · intro sf_g hpc_g hrun_g hsp_g hcs_g
      wp_simp_pre only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v0_1
      apply SepWP.exists_elim; intro v1_1
      apply SepWP.exists_elim; intro v2_1
      apply SepWP.pure_elim; intro htr_g
      apply SepWP.pure_elim; rintro ⟨hp'_ne, hp'_mod⟩
      have hp'_al : v0_1 &&& 1#64 = 0#64 := and_one_of_mod_two hp'_mod
      have hal_p' : MemWidth.isAligned .W16 v0_1 = true := by
        simpa using aligned16_add_mul_two v0_1 hp'_al 0
      have h128_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_omega
      have hsp_g' : sf_g.sp = s0.sp - 144#64 := by
        simpa [arm64_norm, wp_norm] using hsp_g
      have hsp_g_al : (sf_g.sp &&& 15#64 == 0#64) = true := by
        rw [hsp_g', beq_iff_eq]; revert hsp0; bv_bits
      wp_conv_pre =>
        rw [h128_eq]
        simp only [arm64_norm, wp_norm]
        rw [grow0_post_rearrange]
      wp_steps 6
      refine from_61974_cap4_sepWP A b ext hb hdealloc0 a R s0 _
        (by simp [hnil]) v0_1 hp'_ne hp'_al v1_1 1#64 hsp0
        (by rw [hentry]; wp_norm_lhs)
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hsp_g')
        (by simpa [arm64_norm, wp_norm] using htr_g)
        (by simpa [arm64_norm, wp_norm] using hcs_g.2.2.2.2.2.2.2.2.2.2.2)
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm, h_1] using hcs_g.1)
        (by simpa [arm64_norm, wp_norm, hnil] using hcs_g.2.1)
        (by
          have hx21 := hcs_g.2.2.1
          simp only [arm64_norm, wp_norm] at hx21 ⊢
          rw [hx21]
          simpa [arm64_norm, wp_norm] using h_3)
  · -- Non-empty polynomial (`a.poly.coefficients ≠ []`)
    have hlen_pos : 0 < a.poly.coefficients.length := List.length_pos_iff.mpr hnil
    rcases ofNat_beq_false_of_lt hlen_pos (by omega) with ⟨_, _, hx1_ne0, _⟩
    have htoNat_2len :
        (BitVec.ofNat 64 (2 * a.poly.coefficients.length)).toNat =
          2 * a.poly.coefficients.length :=
      ofNat_two_mul_toNat a.poly.coefficients.length (by omega)
    have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
    apply SepWPp.of_sepWP (mid := entry + 68#64)
    wp_simp_pre only [stackAt_computeAt_split s0.sp, stackAt_growOne_eq_allocHook (s0.sp - 144#64)]
    wp_pull_exists
    wp_steps 14
    wp_call hshim
    wp_steps 3
    wp_call halloc
    apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
    by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · -- Allocation failed (x0 = 0): branch at 0x61958 to 0x61c10..0x61c18 (handle_error panic)
      have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hptr0
      wp_conv_pre => rw [alloc_post_pos hptr0]
      apply SepWPp.pure_left; intro htr_fail
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
      wp_steps 4
      apply SepWP.done (by rfl) (by wp_norm_lhs)
      have htr_panic_eq : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htr_fail, h_4]
      refine SepWPp.panic (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hpan_err)
        (fun hm => ?_)
      rw [← sepConj_assoc]
      refine allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _) ⟨?_, ?_⟩ hm
      · exact allocFailedIn_of_trace_eq htr_panic_eq
      · change s0.trace <+: sf_1.trace
        rw [htr_panic_eq]
        exact List.prefix_append s0.trace [allocFailedEvent]
    · -- Allocation succeeded (x0 ≠ 0)
      have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
      wp_conv_pre => rw [alloc_post_neg hptr0]
      apply SepWPp.pure_left; rintro ⟨hptr_mod, htr_ok⟩
      have hp0_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
        and_one_of_mod_two hptr_mod
      have hal_p0 : MemWidth.isAligned .W16 (sf_1.readReg64 (Reg.gpr 0#5)) = true := by
        simpa using aligned16_add_mul_two (sf_1.readReg64 (Reg.gpr 0#5)) hp0_al 0
      have hsp_sf1 : sf_1.sp = s0.sp - 144#64 := by
        rw [hsp_sf, h_5]
      have hsp_sf1_al : (sf_1.sp &&& 15#64 == 0#64) = true := by
        rw [hsp_sf1, beq_iff_eq]; revert hsp0; bv_bits
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr_ok, h_4]
      wp_conv_pre =>
        rw [h_5, merge_allocHook_after_alloc s0.sp]
      by_cases hlen1 : a.poly.coefficients.length = 1
      · -- `a.poly.coefficients.length = 1` (calls `grow_one` at 0x61be8)
        have hx20_1 : (BitVec.ofNat 64 a.poly.coefficients.length == 1#64) = true := by
          rw [hlen1]; rfl
        have hsub_1 : (BitVec.ofNat 64 a.poly.coefficients.length - 1#64 == 0#64) = true := by
          rw [hlen1]; rfl
        have hmem2 :
            memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * a.poly.coefficients.length) =
              ∃∗ w0 : BitVec 16, (sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ w0 := by
          rw [hlen1, Nat.mul_one, ProofLib.memRegion_two]
        apply SepWPp.of_sepWP
          (mid := entry + bv% (2 ^ 64 +
            ls_off% "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one" -
            ls_off% "<spqr::encoding::polynomial::Poly>::compute_at"))
        wp_conv_pre =>
          rw [hmem2, hlen1, show 2 * 1 = 2 from rfl]
        wp_pull_exists
        wp_steps 9
        apply SepWP.done (by rfl) (by wp_norm_lhs)
        apply SepWPp.call_panic_to_sepWP hgrow1
          (s0 := s0)
          (x := (s0.sp - 136#64, sf_1.readReg64 (Reg.gpr 0#5)))
          (ret_pc := entry + 728#64)
          (φ := sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64)
          (T := ((s0.sp - 136#64) ↦₆₄ 1#64) ∗
                ((s0.sp - 136#64 + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 2 2 ∗
                ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16) ∗
                A.pool ∗
                stackAt (s0.sp - 144#64) growOneStack)
        · wp_norm_lhs
        · wp_norm_lhs
        · simp only [State.spAligned, arm64_norm, wp_norm, hsp_sf1_al]
        · wp_norm_lhs
        · simpa [arm64_norm, wp_norm] using htr_sf1
        · dsimp only [growOneGF16OneSpec]
          simp only [arm64_norm, wp_norm, hsp_sf1]
        · exact hptr0
        · exact grow1_pre_split s0.sp (sf_1.readReg64 (Reg.gpr 0#5)) A _ _ _ _ _ _ _ _ _
        · intro _; rfl
        · intro _ _ _ _ hm; simp [satisfies_pure_sepConj] at hm
        · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
        · intro sf_g hpc_g hrun_g hsp_g hcs_g
          wp_simp_pre only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro v0_2
          apply SepWP.exists_elim; intro v1_1
          apply SepWP.pure_elim; intro htr_g
          apply SepWP.pure_elim; rintro ⟨hp'_ne, hp'_mod⟩
          have hp'_al : v0_2 &&& 1#64 = 0#64 := and_one_of_mod_two hp'_mod
          have h128_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_omega
          have hsp_g' : sf_g.sp = s0.sp - 144#64 := by
            rw [hsp_g]; simpa [arm64_norm, wp_norm] using hsp_sf1
          have hsp_g_al : (sf_g.sp &&& 15#64 == 0#64) = true := by
            rw [hsp_g', beq_iff_eq]; revert hsp0; bv_bits
          wp_conv_pre =>
            rw [h128_eq]
            simp only [arm64_norm, wp_norm, hsp_sf1]
            rw [grow0_post_rearrange]
          wp_steps 2
          refine from_61974_cap4_sepWP A b ext hb hdealloc0 a R s0 _
            (by omega) v0_2 hp'_ne hp'_al v1_1 1#64 hsp0
            (by rw [hentry]; wp_norm_lhs)
            (by wp_norm_lhs)
            (by simpa [arm64_norm, wp_norm] using hsp_g')
            (by
              have htr_g' : sf_g.trace = sf_1.trace := by simpa [arm64_norm, wp_norm] using htr_g
              simpa [arm64_norm, wp_norm, htr_sf1] using htr_g')
            (by
              have hv_g := hcs_g.2.2.2.2.2.2.2.2.2.2.2
              simp only [arm64_norm, wp_norm] at hv_g ⊢
              rw [hv_g, hvregs_1, hvregs])
            (by wp_norm_lhs)
            (by
              have hx19 := hcs_g.1
              simp only [arm64_norm, wp_norm] at hx19 ⊢
              rw [hx19, h_16, h_6])
            (by
              have hx20 := hcs_g.2.1
              simp only [arm64_norm, wp_norm] at hx20 ⊢
              rw [hx20, h_17, h_7])
            (by
              have hx21 := hcs_g.2.2.1
              simp only [arm64_norm, wp_norm] at hx21 ⊢
              rw [hx21, h_18, h_8]
              simpa [arm64_norm, wp_norm] using h_3)
      · -- `2 ≤ a.poly.coefficients.length` (falls through to 0x61974)
        have hlen_ge2 : 2 ≤ a.poly.coefficients.length := by omega
        rcases subs_succ_one_ne_zero (r := a.poly.coefficients.length - 2) (by omega) with
          ⟨hsub1_ne0, hlen_ne1⟩
        rw [show a.poly.coefficients.length - 2 + 1 + 1 = a.poly.coefficients.length by omega]
          at hsub1_ne0 hlen_ne1
        apply SepWPp.of_sepWP_ret
        wp_conv_pre =>
          rw [memRegion_ge2_split (sf_1.readReg64 (Reg.gpr 0#5)) a.poly.coefficients.length hlen_ge2 (by omega),
              sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
        wp_pull_exists
        wp_steps 7
        wp_conv_pre => rw [ge2_to_61974_rearrange]
        refine from_61974_ge2_sepWP A b ext hb hdealloc0 a R s0 _
          hlen_ge2 (by omega) (sf_1.readReg64 (Reg.gpr 0#5)) hptr0 hp0_al _ 1#64 hsp0
          (by rw [hentry]; wp_norm_lhs)
          (by wp_norm_lhs)
          (by simpa [arm64_norm, wp_norm] using hsp_sf1)
          (by simpa [arm64_norm, wp_norm] using htr_sf1)
          (by simp only [arm64_norm, wp_norm, hvregs_1, hvregs])
          (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm, h_16, h_6])
          (by simp only [arm64_norm, wp_norm, h_17, h_7])
          (by
            simp only [arm64_norm, wp_norm, h_18, h_8]
            simpa [arm64_norm, wp_norm] using h_3)

theorem computeAt_ok (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64)
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName)
      (computeAtSpec A b) :=
  computeAt_ok_core b hb A ext hA.alloc hA.dealloc hA.shim
    (grow_one_gf16_zero_ok_at hA) (grow_one_gf16_one_ok_at hA)

theorem computeAt_ok_4k (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64)
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName)
      (computeAtSpec A b) :=
  computeAt_ok_core b hb A ext hA.alloc hA.dealloc hA.shim
    (grow_one_gf16_zero_ok_at_4k hA) (grow_one_gf16_one_ok_at_4k hA)

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `371`) -/

set_option maxHeartbeats 1600000 in
theorem computeAt_placed_ok [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (blkPl_371).base
      (withLsCodeLoaded lsmpl (computeAtPlacedSpec A)) := by
  have hshim :
      subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
        (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
    spqr_hook_ok_of_mem hshim_sat
  have halloc :
      subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
        (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    spqr_hook_ok_of_mem halloc_sat
  have hdealloc :
      subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
        (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem hdealloc_sat
  have hpan_err :
      ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  simp only [withLsCodeLoaded, computeAtPlacedSpec]
  wpp_init a s0
  have hcl0 := h; have h := h_1; have h_1 := h_2; have h_2 := h_3; have h_3 := h_4; clear h_4
  have hsp0 : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
  have _h_4 : True := trivial
  by_cases hnil : a.poly.coefficients = []
  · -- Empty polynomial (`a.poly.coefficients = []`)
    have hx1_0 : (BitVec.ofNat 64 a.poly.coefficients.length == 0#64) = true := by
      rw [hnil]; rfl
    apply sepWPp_seq_lscl hcl0
      (mid := lsmpl.base 359)
    wp_simp_pre only [stackAt_computeAt_split s0.sp]
    wp_pull_exists
    wp_steps 17
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_pre_g0
    have hgrow0 := lscall_blk_cl
      (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (grow_one_gf16_zero_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat) hcl_pre_g0
    apply SepWPp.call_panic_to_sepWP_lscl hcl_pre_g0 hgrow0
      (s0 := s0)
      (x := s0.sp - 136#64)
      (ret_pc := (blkPl_371).base + 696#64)
      (φ := True)
      (T := ((s0.sp - 136#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 136#64 + 8#64) ↦₆₄ 2#64) ∗
            A.pool ∗
            stackAt (s0.sp - 144#64) growOneStack)
    · wp_norm_lhs
    · wp_norm_lhs
    · simp only [State.spAligned, arm64_norm, wp_norm, beq_iff_eq]
      revert hsp0; bv_bits
    · wp_norm_lhs
    · wp_norm_lhs
    · dsimp only [growOneGF16ZeroSpec]
      simp only [arm64_norm, wp_norm]
    · trivial
    · exact grow0_pre_split s0.sp A _ _ _ _ _ _
    · intro _; rfl
    · intro _ _ _ _ hm; simp [satisfies_pure_sepConj] at hm
    · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
    · intro sf_g hcl_g hpc_g hrun_g hsp_g hcs_g
      wp_simp_pre only [growOneGF16ZeroSpec, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v0_1
      apply SepWP.exists_elim; intro v1_1
      apply SepWP.exists_elim; intro v2_1
      apply SepWP.pure_elim; intro htr_g
      apply SepWP.pure_elim; rintro ⟨hp'_ne, hp'_mod⟩
      have hp'_al : v0_1 &&& 1#64 = 0#64 := and_one_of_mod_two hp'_mod
      have hal_p' : MemWidth.isAligned .W16 v0_1 = true := by
        simpa using aligned16_add_mul_two v0_1 hp'_al 0
      have h128_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_omega
      have hsp_g' : sf_g.sp = s0.sp - 144#64 := by
        simpa [arm64_norm, wp_norm] using hsp_g
      have hsp_g_al : (sf_g.sp &&& 15#64 == 0#64) = true := by
        rw [hsp_g', beq_iff_eq]; revert hsp0; bv_bits
      wp_conv_pre =>
        rw [h128_eq]
        simp only [arm64_norm, wp_norm]
        rw [grow0_post_rearrange]
      apply sepWP_seq_lscl (by exact hcl_g) (mid := (blkPl_371).base + 96#64)
      wp_steps 6
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      intro hcl_974
      refine from_61974_cap4_placed_sepWP A ext hdealloc a R s0 _
        (by simp [hnil]) v0_1 hp'_ne hp'_al v1_1 1#64 hsp0
        (by exact hcl_974)
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hsp_g')
        (by simpa [arm64_norm, wp_norm] using htr_g)
        (by simpa [arm64_norm, wp_norm] using hcs_g.2.2.2.2.2.2.2.2.2.2.2)
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm, h_1] using hcs_g.1)
        (by simpa [arm64_norm, wp_norm, hnil] using hcs_g.2.1)
        (by
          have hx21 := hcs_g.2.2.1
          simp only [arm64_norm, wp_norm] at hx21 ⊢
          rw [hx21]
          simpa [arm64_norm, wp_norm] using h_3)
  · -- Non-empty polynomial (`a.poly.coefficients ≠ []`)
    have hlen_pos : 0 < a.poly.coefficients.length := List.length_pos_iff.mpr hnil
    rcases ofNat_beq_false_of_lt hlen_pos (by omega) with ⟨_, _, hx1_ne0, _⟩
    have htoNat_2len :
        (BitVec.ofNat 64 (2 * a.poly.coefficients.length)).toNat =
          2 * a.poly.coefficients.length :=
      ofNat_two_mul_toNat a.poly.coefficients.length (by omega)
    have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
    apply sepWPp_seq_lscl hcl0 (mid := (blkPl_371).base + 68#64)
    wp_simp_pre only [stackAt_computeAt_split s0.sp, stackAt_growOne_eq_allocHook (s0.sp - 144#64)]
    wp_pull_exists
    wp_steps 14
    wp_call hshim
    wp_steps 3
    wp_call halloc
    apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
    intro hcl_sf1
    by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · -- Allocation failed (x0 = 0): branch at +0x44 to +0x2fc..+0x304 (handle_error panic)
      have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hptr0
      wp_conv_pre => rw [alloc_post_pos hptr0]
      apply SepWPp.pure_left; intro htr_fail
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps 4
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      have htr_panic_eq : sf_1.trace = s0.trace ++ [allocFailedEvent] := by
        rw [htr_fail, h_4]
      refine SepWPp.panic (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hpan_err)
        (fun hm => ?_)
      rw [← sepConj_assoc]
      refine allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _) ⟨?_, ?_⟩ hm
      · exact allocFailedIn_of_trace_eq htr_panic_eq
      · change s0.trace <+: sf_1.trace
        rw [htr_panic_eq]
        exact List.prefix_append s0.trace [allocFailedEvent]
    · -- Allocation succeeded (x0 ≠ 0)
      have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
      wp_conv_pre => rw [alloc_post_neg hptr0]
      apply SepWPp.pure_left; rintro ⟨hptr_mod, htr_ok⟩
      have hp0_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
        and_one_of_mod_two hptr_mod
      have hal_p0 : MemWidth.isAligned .W16 (sf_1.readReg64 (Reg.gpr 0#5)) = true := by
        simpa using aligned16_add_mul_two (sf_1.readReg64 (Reg.gpr 0#5)) hp0_al 0
      have hsp_sf1 : sf_1.sp = s0.sp - 144#64 := by
        rw [hsp_sf, h_5]
      have hsp_sf1_al : (sf_1.sp &&& 15#64 == 0#64) = true := by
        rw [hsp_sf1, beq_iff_eq]; revert hsp0; bv_bits
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr_ok, h_4]
      wp_conv_pre =>
        rw [h_5, merge_allocHook_after_alloc s0.sp]
      by_cases hlen1 : a.poly.coefficients.length = 1
      · -- `a.poly.coefficients.length = 1` (calls `grow_one` at +0x2d4)
        have hx20_1 : (BitVec.ofNat 64 a.poly.coefficients.length == 1#64) = true := by
          rw [hlen1]; rfl
        have hsub_1 : (BitVec.ofNat 64 a.poly.coefficients.length - 1#64 == 0#64) = true := by
          rw [hlen1]; rfl
        have hmem2 :
            memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * a.poly.coefficients.length) =
              ∃∗ w0 : BitVec 16, (sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ w0 := by
          rw [hlen1, Nat.mul_one, ProofLib.memRegion_two]
        apply sepWPp_seq_lscl hcl_sf1
          (mid := lsmpl.base 359)
        wp_conv_pre =>
          rw [hmem2, hlen1, show 2 * 1 = 2 from rfl]
        wp_pull_exists
        wp_steps 9
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        intro hcl_pre_g1
        have hgrow1 := lscall_blk_cl
          (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
          (grow_one_gf16_one_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat) hcl_pre_g1
        apply SepWPp.call_panic_to_sepWP_lscl hcl_pre_g1 hgrow1
          (s0 := s0)
          (x := (s0.sp - 136#64, sf_1.readReg64 (Reg.gpr 0#5)))
          (ret_pc := (blkPl_371).base + 728#64)
          (φ := sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64)
          (T := ((s0.sp - 136#64) ↦₆₄ 1#64) ∗
                ((s0.sp - 136#64 + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                A.live (sf_1.readReg64 (Reg.gpr 0#5)) 2 2 ∗
                ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16) ∗
                A.pool ∗
                stackAt (s0.sp - 144#64) growOneStack)
        · wp_norm_lhs
        · wp_norm_lhs
        · simp only [State.spAligned, arm64_norm, wp_norm, hsp_sf1_al]
        · wp_norm_lhs
        · simpa [arm64_norm, wp_norm] using htr_sf1
        · dsimp only [growOneGF16OneSpec]
          simp only [arm64_norm, wp_norm, hsp_sf1]
        · exact hptr0
        · exact grow1_pre_split s0.sp (sf_1.readReg64 (Reg.gpr 0#5)) A _ _ _ _ _ _ _ _ _
        · intro _; rfl
        · intro _ _ _ _ hm; simp [satisfies_pure_sepConj] at hm
        · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
        · intro sf_g hcl_g hpc_g hrun_g hsp_g hcs_g
          wp_simp_pre only [growOneGF16OneSpec, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro v0_2
          apply SepWP.exists_elim; intro v1_1
          apply SepWP.pure_elim; intro htr_g
          apply SepWP.pure_elim; rintro ⟨hp'_ne, hp'_mod⟩
          have hp'_al : v0_2 &&& 1#64 = 0#64 := and_one_of_mod_two hp'_mod
          have h128_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_omega
          have hsp_g' : sf_g.sp = s0.sp - 144#64 := by
            rw [hsp_g]; simpa [arm64_norm, wp_norm] using hsp_sf1
          have hsp_g_al : (sf_g.sp &&& 15#64 == 0#64) = true := by
            rw [hsp_g', beq_iff_eq]; revert hsp0; bv_bits
          wp_conv_pre =>
            rw [h128_eq]
            simp only [arm64_norm, wp_norm, hsp_sf1]
            rw [grow0_post_rearrange]
          wp_steps 2
          refine from_61974_cap4_placed_sepWP A ext hdealloc a R s0 _
            (by omega) v0_2 hp'_ne hp'_al v1_1 1#64 hsp0
            (by exact hcl_g)
            (by wp_norm_lhs)
            (by wp_norm_lhs)
            (by simpa [arm64_norm, wp_norm] using hsp_g')
            (by
              have htr_g' : sf_g.trace = sf_1.trace := by simpa [arm64_norm, wp_norm] using htr_g
              simpa [arm64_norm, wp_norm, htr_sf1] using htr_g')
            (by
              have hv_g := hcs_g.2.2.2.2.2.2.2.2.2.2.2
              simp only [arm64_norm, wp_norm] at hv_g ⊢
              rw [hv_g, hvregs_1, hvregs])
            (by wp_norm_lhs)
            (by
              have hx19 := hcs_g.1
              simp only [arm64_norm, wp_norm] at hx19 ⊢
              rw [hx19, h_16, h_6])
            (by
              have hx20 := hcs_g.2.1
              simp only [arm64_norm, wp_norm] at hx20 ⊢
              rw [hx20, h_17, h_7])
            (by
              have hx21 := hcs_g.2.2.1
              simp only [arm64_norm, wp_norm] at hx21 ⊢
              rw [hx21, h_18, h_8]
              simpa [arm64_norm, wp_norm] using h_3)
      · -- `2 ≤ a.poly.coefficients.length` (falls through to +0x60)
        have hlen_ge2 : 2 ≤ a.poly.coefficients.length := by omega
        rcases subs_succ_one_ne_zero (r := a.poly.coefficients.length - 2) (by omega) with
          ⟨hsub1_ne0, hlen_ne1⟩
        rw [show a.poly.coefficients.length - 2 + 1 + 1 = a.poly.coefficients.length by omega]
          at hsub1_ne0 hlen_ne1
        apply SepWPp.of_sepWP_ret
        wp_conv_pre =>
          rw [memRegion_ge2_split (sf_1.readReg64 (Reg.gpr 0#5)) a.poly.coefficients.length hlen_ge2 (by omega),
              sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
        wp_pull_exists
        apply sepWP_seq_lscl (by exact hcl_sf1) (mid := (blkPl_371).base + 96#64)
        wp_steps 7
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        intro hcl_974
        wp_conv_pre => rw [ge2_to_61974_rearrange]
        refine from_61974_ge2_placed_sepWP A ext hdealloc a R s0 _
          hlen_ge2 (by omega) (sf_1.readReg64 (Reg.gpr 0#5)) hptr0 hp0_al _ 1#64 hsp0
          (by exact hcl_974)
          (by wp_norm_lhs)
          (by wp_norm_lhs)
          (by simpa [arm64_norm, wp_norm] using hsp_sf1)
          (by simpa [arm64_norm, wp_norm] using htr_sf1)
          (by simp only [arm64_norm, wp_norm, hvregs_1, hvregs])
          (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm, h_16, h_6])
          (by simp only [arm64_norm, wp_norm, h_17, h_7])
          (by
            simp only [arm64_norm, wp_norm, h_18, h_8]
            simpa [arm64_norm, wp_norm] using h_3)

end CryptoVerification.SpqrV1.Poly.ComputeAt

