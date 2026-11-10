/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Constant Basis `n = 5` and Shared Loop Exit

**Checked by Lean.**

Verifies `basis_n5_sepWPp` (`+1136 -> +2608`) from `COMPLETE_POINTS_POLYS_5` and the shared
`accPtr` allocation exit block `basis_loop_exit_sepWPp` (`+2456 -> +2608`) for `n ∈ {30, 34, 36}`.
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
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two' :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight' :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

private theorem add_page_mask_6a000 (b off : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hoff : (0x64f8c#64 + off) &&& 0xfff#64 = (0x64f8c#64 + off) - 0x65000#64) :
    ((b + 0x64f8c#64) + off) &&& 0xfffffffffffff000#64 = b + 0x65000#64 := by
  bv_robdd

theorem polyNextChunk_adrp_page {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) (off : BitVec 64)
    (hoff : (0x64f8c#64 + off) &&& 0xfff#64 = (0x64f8c#64 + off) - 0x65000#64) :
    ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + off) &&&
      0xfffffffffffff000#64 = b + 0x65000#64 := by
  have hfn : libsignalSessionCode.fnOff polyNextChunkName = 0x64f8c :=
    ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"
  rw [Program.fnAddr_rebase, hfn]
  exact add_page_mask_6a000 b off hb hoff

set_option maxHeartbeats 1600000 in
/-- `n = 5` constant basis case (`0x6a7f4 -> 0x6ab20..0x6ac5c -> 0x6adb4`, `+1136 -> +2608`). -/
theorem basis_n5_sepWPp {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64)
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 5#64)
    (hcont : ∀ s1 basisPtr accPtr,
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2608#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = 5#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         completePointsPolys5At b ∗
         basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_5) ∗
         A.live accPtr 10 2 ∗ memRegion accPtr 10 ∗
         ((fsp + 24#64) ↦₆₄ 5#64) ∗
         ((fsp + 96#64) ↦₆₄ 5#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       completePointsPolys5At b ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hshim := hA.shim_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  simp only [rustAllocSpec] at halloc
  have hpanic4892 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4892 b ext Q s0 s P R
  have hpanic4784 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4784 b ext Q s0 s P R
  have hpanic4796 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4796 b ext Q s0 s P R
  have hadrp0 : ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1996#64) &&&
      0xfffffffffffff000#64 = b + 0x65000#64 :=
    polyNextChunk_adrp_page hb 1996#64 rfl
  have hadrp1 : ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2048#64) &&&
      0xfffffffffffff000#64 = b + 0x65000#64 :=
    polyNextChunk_adrp_page hb 2048#64 rfl
  have hadrp2 : ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2100#64) &&&
      0xfffffffffffff000#64 = b + 0x65000#64 :=
    polyNextChunk_adrp_page hb 2100#64 rfl
  have hadrp3 : ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2152#64) &&&
      0xfffffffffffff000#64 = b + 0x65000#64 :=
    polyNextChunk_adrp_page hb 2152#64 rfl
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x470 32
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x79c 320
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4892 hpanic4784 hpanic4796 hadrp0 hadrp1 hadrp2 hadrp3 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  rw [completePointsPolys5At_split b]
  apply SepWPp.of_sepWP (mid := entry + 1964#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr1
    refine hpanic4892 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨halign1, htr1⟩
    have hcond1 : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom1
    have halign_basis0 : (sf_1.readReg64 (Reg.gpr 0#5) &&& 7#64 == 0#64) = true :=
      align8_of_mod8_eq_zero halign1
    have halign_basis24 : ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) &&& 7#64 == 0#64) = true :=
      align8_add_of_mod8_eq_zero halign1 (by decide)
    have halign_basis48 : ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) &&& 7#64 == 0#64) = true :=
      align8_add_of_mod8_eq_zero halign1 (by decide)
    have halign_basis72 : ((sf_1.readReg64 (Reg.gpr 0#5) + 72#64) &&& 7#64 == 0#64) = true :=
      align8_add_of_mod8_eq_zero halign1 (by decide)
    have halign_basis96 : ((sf_1.readReg64 (Reg.gpr 0#5) + 96#64) &&& 7#64 == 0#64) = true :=
      align8_add_of_mod8_eq_zero halign1 (by decide)
    rw [memRegion_split_basis5 (sf_1.readReg64 (Reg.gpr 0#5))]
    apply SepWPp.of_sepWP (mid := entry + 1968#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) ?_
    apply SepWPp.of_sepWP (mid := entry + 1992#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr2
      refine hpanic4784 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom2, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr1, h, htrace] at htr2; exact htr2⟩
    · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr2⟩
      have hcond2 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom2
      have hx24_sf3 : sf_3.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
        simp only [h_39, h_29, wp_norm]
      rw [memRegion_split_polyHeader (sf_1.readReg64 (Reg.gpr 0#5)),
          memRegion_split_deg4 (sf_3.readReg64 (Reg.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro u0_len
      apply SepWPp.exists_elim; intro u0_ptr
      apply SepWPp.exists_elim; intro u0_cap
      apply SepWPp.exists_elim; intro u0_c4
      apply SepWPp.exists_elim; intro u0_w03
      apply SepWPp.of_sepWP (mid := entry + 1996#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hcond2, ↓reduceIte]) (by wp_norm_lhs) ?_
      apply SepWPp.of_sepWP (mid := entry + 2044#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
      by_cases hoom3 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr3
        refine hpanic4784 _ _ ?_
        wp_steps
        exact SepWP.done (by simp only [wp_norm, hoom3, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
          ⟨Entails.refl _, by rw [h_44, htr2, h_22, htr1, h, htrace] at htr3; exact htr3⟩
      · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro ⟨_, htr3⟩
        have hcond3 : ¬(sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
          simpa [beq_iff_eq] using hoom3
        have hx24_sf5 : sf_5.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
          simp only [h_61, h_51, hx24_sf3]
        rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 24#64 32#64 40#64 (by bv_arith) (by bv_arith),
            memRegion_split_deg4 (sf_5.readReg64 (Reg.gpr 0#5))]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWPp.exists_elim; intro u1_len
        apply SepWPp.exists_elim; intro u1_ptr
        apply SepWPp.exists_elim; intro u1_cap
        apply SepWPp.exists_elim; intro u1_c4
        apply SepWPp.exists_elim; intro u1_w03
        apply SepWPp.of_sepWP (mid := entry + 2048#64)
        wp_steps
        refine SepWP.done (by simp only [wp_norm, hcond3, ↓reduceIte]) (by wp_norm_lhs) ?_
        apply SepWPp.of_sepWP (mid := entry + 2096#64)
        wp_steps; wp_apply; wp_steps; wp_apply
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
        by_cases hoom4 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr4
          refine hpanic4784 _ _ ?_
          wp_steps
          exact SepWP.done (by simp only [wp_norm, hoom4, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
            ⟨Entails.refl _, by rw [h_66, htr3, h_44, htr2, h_22, htr1, h, htrace] at htr4; exact htr4⟩
        · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro ⟨_, htr4⟩
          have hcond4 : ¬(sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
            simpa [beq_iff_eq] using hoom4
          have hx24_sf7 : sf_7.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
            simp only [h_83, h_73, hx24_sf5]
          rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 48#64 56#64 64#64 (by bv_arith) (by bv_arith),
              memRegion_split_deg4 (sf_7.readReg64 (Reg.gpr 0#5))]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWPp.exists_elim; intro u2_len
          apply SepWPp.exists_elim; intro u2_ptr
          apply SepWPp.exists_elim; intro u2_cap
          apply SepWPp.exists_elim; intro u2_c4
          apply SepWPp.exists_elim; intro u2_w03
          apply SepWPp.of_sepWP (mid := entry + 2100#64)
          wp_steps
          refine SepWP.done (by simp only [wp_norm, hcond4, ↓reduceIte]) (by wp_norm_lhs) ?_
          apply SepWPp.of_sepWP (mid := entry + 2148#64)
          wp_steps; wp_apply; wp_steps; wp_apply
          refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
          by_cases hoom5 : sf_9.readReg64 (Reg.gpr 0#5) = 0#64
          · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro htr5
            refine hpanic4784 _ _ ?_
            wp_steps
            exact SepWP.done (by simp only [wp_norm, hoom5, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
              ⟨Entails.refl _, by rw [h_88, htr4, h_66, htr3, h_44, htr2, h_22, htr1, h, htrace] at htr5; exact htr5⟩
          · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro ⟨_, htr5⟩
            have hcond5 : ¬(sf_9.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
              simpa [beq_iff_eq] using hoom5
            have hx24_sf9 : sf_9.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
              simp only [h_105, h_95, hx24_sf7]
            rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 72#64 80#64 88#64 (by bv_arith) (by bv_arith),
                memRegion_split_deg4 (sf_9.readReg64 (Reg.gpr 0#5))]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWPp.exists_elim; intro u3_len
            apply SepWPp.exists_elim; intro u3_ptr
            apply SepWPp.exists_elim; intro u3_cap
            apply SepWPp.exists_elim; intro u3_c4
            apply SepWPp.exists_elim; intro u3_w03
            apply SepWPp.of_sepWP (mid := entry + 2152#64)
            wp_steps
            refine SepWP.done (by simp only [wp_norm, hcond5, ↓reduceIte]) (by wp_norm_lhs) ?_
            apply SepWPp.of_sepWP (mid := entry + 2200#64)
            wp_steps; wp_apply; wp_steps; wp_apply
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
            by_cases hoom6 : sf_11.readReg64 (Reg.gpr 0#5) = 0#64
            · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
              apply sepWPp_pure_mid; intro htr6
              refine hpanic4784 _ _ ?_
              wp_steps
              exact SepWP.done (by simp only [wp_norm, hoom6, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
                ⟨Entails.refl _, by rw [h_110, htr5, h_88, htr4, h_66, htr3, h_44, htr2, h_22, htr1, h, htrace] at htr6; exact htr6⟩
            · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
              apply sepWPp_pure_mid; intro ⟨_, htr6⟩
              have hcond6 : ¬(sf_11.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
                simpa [beq_iff_eq] using hoom6
              have hsp_sf10 : sf_10.sp = fsp := by
                simp only [h_111, ‹sf_9.sp = sf_8.sp›, h_89, ‹sf_7.sp = sf_6.sp›, h_67,
                  ‹sf_5.sp = sf_4.sp›, h_45, ‹sf_3.sp = sf_2.sp›, h_23, ‹sf_1.sp = sf.sp›, h_1, hsp]
              have hsp_sf11 : sf_11.sp = fsp := by
                simp only [‹sf_11.sp = sf_10.sp›, hsp_sf10]
              have hx19_sf11 : sf_11.readReg64 (Reg.gpr 19#5) = 5#64 := by
                simp only [h_122, h_112, h_100, h_90, h_78, h_68, h_56, h_46, wp_norm]
              have hx24_sf11 : sf_11.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
                simp only [h_127, h_117, hx24_sf9]
              have hx25_sf11 : sf_11.readReg64 (Reg.gpr 25#5) = 5#64 := by
                simp only [h_128, h_118, h_106, h_96, h_84, h_74, h_62, h_52, h_40, h_30, wp_norm, h_18, h_8, hx25]
              rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 96#64 104#64 112#64 (by bv_arith) (by bv_arith),
                  memRegion_split_deg4 (sf_11.readReg64 (Reg.gpr 0#5))]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWPp.exists_elim; intro u4_len
              apply SepWPp.exists_elim; intro u4_ptr
              apply SepWPp.exists_elim; intro u4_cap
              apply SepWPp.exists_elim; intro u4_c4
              apply SepWPp.exists_elim; intro u4_w03
              apply SepWPp.of_sepWP (mid := entry + 2204#64)
              wp_steps
              refine SepWP.done (by simp only [wp_norm, hcond6, ↓reduceIte]) (by wp_norm_lhs) ?_
              rw [hsp_sf10]
              apply SepWPp.of_sepWP (mid := entry + 2260#64)
              wp_steps; wp_apply; wp_steps; wp_apply
              refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
              by_cases hoom7 : sf_13.readReg64 (Reg.gpr 0#5) = 0#64
              · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
                apply sepWPp_pure_mid; intro htr7
                refine hpanic4796 _ _ ?_
                wp_steps
                exact SepWP.done (by simp only [wp_norm, hoom7, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
                  ⟨Entails.refl _, by rw [h_132, htr6, h_110, htr5, h_88, htr4, h_66, htr3, h_44, htr2, h_22, htr1, h, htrace] at htr7; exact htr7⟩
              · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
                apply sepWPp_pure_mid; intro ⟨_, htr7⟩
                have hcond7 : ¬(sf_13.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
                  simpa [beq_iff_eq] using hoom7
                apply SepWPp.of_sepWP (mid := entry + 2608#64)
                wp_steps
                refine SepWP.done (by simp only [wp_norm, hcond7, ↓reduceIte]) (by wp_norm_lhs) ?_
                have hsp_sf12 : sf_12.sp = fsp := by
                  simp only [h_133, hsp_sf11]
                rw [hsp_sf12]
                have hpoly0 := polyOf_deg4_intro A (sf_1.readReg64 (Reg.gpr 0#5))
                  (sf_3.readReg64 (Reg.gpr 0#5)) 0x78039605b4050001#64
                  0x0001#16 0xb405#16 0x9605#16 0x7803#16 0x5a02#16
                  hoom2 rfl rfl rfl rfl
                have hpoly1 := polyOf_deg4_intro_off A (sf_1.readReg64 (Reg.gpr 0#5)) 24#64 32#64 40#64
                  (sf_5.readReg64 (Reg.gpr 0#5)) 0x7803c00750030000#64
                  0x0000#16 0x5003#16 0xc007#16 0x7803#16 0xe806#16
                  (by bv_arith) (by bv_arith) hoom3 rfl rfl rfl rfl
                have hpoly2 := polyOf_deg4_intro_off A (sf_1.readReg64 (Reg.gpr 0#5)) 48#64 56#64 64#64
                  (sf_7.readReg64 (Reg.gpr 0#5)) 0x78031400f0060000#64
                  0x0000#16 0xf006#16 0x1400#16 0x7803#16 0x9c05#16
                  (by bv_arith) (by bv_arith) hoom4 rfl rfl rfl rfl
                have hpoly3 := polyOf_deg4_intro_off A (sf_1.readReg64 (Reg.gpr 0#5)) 72#64 80#64 88#64
                  (sf_9.readReg64 (Reg.gpr 0#5)) 0x7803f0069b680000#64
                  0x0000#16 0x9b68#16 0xf006#16 0x7803#16 0x136d#16
                  (by bv_arith) (by bv_arith) hoom5 rfl rfl rfl rfl
                have hpoly4 := polyOf_deg4_intro_off A (sf_1.readReg64 (Reg.gpr 0#5)) 96#64 104#64 112#64
                  (sf_11.readReg64 (Reg.gpr 0#5)) 0x0000b2048f680000#64
                  0x0000#16 0x8f68#16 0xb204#16 0x0000#16 0x3d6c#16
                  (by bv_arith) (by bv_arith) hoom6 rfl rfl rfl rfl
                have hbasis :
                    (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 120 8 ∗
                     (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 5#64) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 5#64) ∗
                      A.live (sf_3.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                      ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x78039605b4050001#64) ∗
                      ((sf_3.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x5a02#16)) ∗
                     (((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ 5#64) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ sf_5.readReg64 (Reg.gpr 0#5)) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ 5#64) ∗
                      A.live (sf_5.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                      ((sf_5.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x7803c00750030000#64) ∗
                      ((sf_5.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0xe806#16)) ∗
                     (((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ 5#64) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ sf_7.readReg64 (Reg.gpr 0#5)) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ 5#64) ∗
                      A.live (sf_7.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                      ((sf_7.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x78031400f0060000#64) ∗
                      ((sf_7.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x9c05#16)) ∗
                     (((sf_1.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ 5#64) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ sf_9.readReg64 (Reg.gpr 0#5)) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ 5#64) ∗
                      A.live (sf_9.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                      ((sf_9.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x7803f0069b680000#64) ∗
                      ((sf_9.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x136d#16)) ∗
                     (((sf_1.readReg64 (Reg.gpr 0#5) + 96#64) ↦₆₄ 5#64) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 104#64) ↦₆₄ sf_11.readReg64 (Reg.gpr 0#5)) ∗
                      ((sf_1.readReg64 (Reg.gpr 0#5) + 112#64) ↦₆₄ 5#64) ∗
                      A.live (sf_11.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                      ((sf_11.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x0000b2048f680000#64) ∗
                      ((sf_11.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x3d6c#16))) ⊢
                    basisVecAt A (sf_1.readReg64 (Reg.gpr 0#5)) (extractCompletePolys COMPLETE_POINTS_POLYS_5) := by
                  rw [completePointsPolys5_eq]
                  unfold extractCompletePolys cp5Polys constPolysToPolys PolyConst.toPoly basisVecAt polyListOf
                  simp only [List.map, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
                    arrayAt, vecHeaderBytes, BitVec.ofNat_eq_ofNat, sepConj_emp,
                    BitVec.add_assoc, BitVec.reduceAdd]
                  refine Entails.pure_right hoom1 ?_
                  exact sepConj_mono_right
                    (sepConj_mono hpoly0
                      (sepConj_mono hpoly1
                        (sepConj_mono hpoly2
                          (sepConj_mono hpoly3 hpoly4))))
                refine SepWPp.weaken_pre ?_
                  (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_13.readReg64 (Reg.gpr 0#5))
                    hoom1 hoom7
                    (by simp only [wp_norm, hcond7, ↓reduceIte])
                    (by wp_norm_lhs)
                    (by simp only [wp_norm, ‹sf_13.sp = sf_12.sp›, hsp_sf12])
                    (by simp only [arm64_norm, wp_norm]; rw [htr7, h_132, htr6, h_110, htr5, h_88, htr4, h_66, htr3, h_44, htr2, h_22, htr1, h, htrace])
                    (by simp only [arm64_norm, wp_norm, *])
                    (by wp_norm_lhs)
                    (by simp only [wp_norm, h_145, h_135, h_123, h_113, h_101, h_91, h_79, h_69, h_57, h_47, h_35, h_25, h_13, h_3])
                    (by simp only [wp_norm, h_149, h_139, hx24_sf11])
                    (by simp only [wp_norm, h_150, h_140, hx25_sf11])
                    (by simp only [wp_norm, h_151, h_141, h_129, h_119, h_107, h_97, h_85, h_75, h_63, h_53, h_41, h_31, h_19, h_9])
                    (by simp only [wp_norm, h_152, h_142, h_130, h_120, h_108, h_98, h_86, h_76, h_64, h_54, h_42, h_32, h_20, h_10])
                    (by simp only [wp_norm, h_153, h_143, h_131, h_121, h_109, h_99, h_87, h_77, h_65, h_55, h_43, h_33, h_21, h_11])
                    (by simp only [wp_norm, hcs_sf_6, hpost_sf_6, hcs_sf_5, hpost_sf_5, hcs_sf_4, hpost_sf_4, hcs_sf_3, hpost_sf_3, hcs_sf_2, hpost_sf_2, hcs_sf_1, hpost_sf_1, hcs_sf, hpost_sf]))
                try simp only [hx19_sf11, hx24_sf11, hx24_sf9, hx24_sf7, hx24_sf5, hx24_sf3,
                  hadrp0, hadrp1, hadrp2, hadrp3, BitVec.add_assoc, BitVec.reduceAdd,
                  completePointsPolys5At_split b]
                refine Entails.trans (Entails.of_eq (show _ =
                  (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 120 8 ∗
                   (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 5#64) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 5#64) ∗
                    A.live (sf_3.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                    ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x78039605b4050001#64) ∗
                    ((sf_3.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x5a02#16)) ∗
                   (((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ 5#64) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ sf_5.readReg64 (Reg.gpr 0#5)) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ 5#64) ∗
                    A.live (sf_5.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                    ((sf_5.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x7803c00750030000#64) ∗
                    ((sf_5.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0xe806#16)) ∗
                   (((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ 5#64) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ sf_7.readReg64 (Reg.gpr 0#5)) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ 5#64) ∗
                    A.live (sf_7.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                    ((sf_7.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x78031400f0060000#64) ∗
                    ((sf_7.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x9c05#16)) ∗
                   (((sf_1.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ 5#64) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ sf_9.readReg64 (Reg.gpr 0#5)) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ 5#64) ∗
                    A.live (sf_9.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                    ((sf_9.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x7803f0069b680000#64) ∗
                    ((sf_9.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x136d#16)) ∗
                   (((sf_1.readReg64 (Reg.gpr 0#5) + 96#64) ↦₆₄ 5#64) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 104#64) ↦₆₄ sf_11.readReg64 (Reg.gpr 0#5)) ∗
                    ((sf_1.readReg64 (Reg.gpr 0#5) + 112#64) ↦₆₄ 5#64) ∗
                    A.live (sf_11.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                    ((sf_11.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x0000b2048f680000#64) ∗
                    ((sf_11.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x3d6c#16))) ∗
                  (A.pool ∗
                   ((b + bv% (ls_bytes% "010005b405960378025a0000")) ↦₆₄ᵣ 0x78039605b4050001#64) ∗
                   ((b + bv% (ls_bytes% "010005b405960378025a0000" + 10)) ↦₆₄ᵣ 0x7803c00750030000#64) ∗
                   ((b + bv% (ls_bytes% "010005b405960378025a0000" + 20)) ↦₆₄ᵣ 0x78031400f0060000#64) ∗
                   ((b + bv% (ls_bytes% "010005b405960378025a0000" + 30)) ↦₆₄ᵣ 0x7803f0069b680000#64) ∗
                   completePointsPolys5RestAt b ∗
                   A.live (sf_13.readReg64 (Reg.gpr 0#5)) 10 2 ∗
                   memRegion (sf_13.readReg64 (Reg.gpr 0#5)) 10 ∗
                   ((fsp + 24#64) ↦₆₄ 5#64) ∗
                   ((fsp + 96#64) ↦₆₄ 5#64) ∗
                   stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
                refine Entails.trans (sepConj_mono_left hbasis) ?_
                exact Entails.of_eq (by ac_rfl)

private theorem shl_one_eq_two_mul (x : BitVec 64) : x <<< (1 : Nat) = 2#64 * x := by bv_robdd
private theorem shl_one_bv_eq_two_mul (x : BitVec 64) : x <<< 1#64 = 2#64 * x := by bv_robdd

/-- Shared exit block (`0x6ad1c..0x6adb4`, `+2456 -> +2608`) for `n ∈ {30, 34, 36}`. -/
theorem basis_loop_exit_sepWPp {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp basisPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (n : Nat) (hn_ne : BitVec.ofNat 64 n ≠ 0#64) (hn_bound : 2 * n < 2 ^ 63)
    (u24 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2456#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hcont : ∀ s1 accPtr,
      accPtr ≠ 0#64 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2608#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x23 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         A.live accPtr (2 * n) 2 ∗ memRegion accPtr (2 * n) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ basisPtr) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ basisPtr) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hshim := hA.shim_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  simp only [rustAllocSpec] at halloc
  have hpanic4796 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4796 b ext Q s0 s P R
  have hcond_n : ¬(BitVec.ofNat 64 n == 0#64) = true := by
    simpa [beq_iff_eq] using hn_ne
  have hshl : BitVec.ofNat 64 n <<< (1 : Nat) = BitVec.ofNat 64 (2 * n) := by
    rw [shl_one_eq_two_mul, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_mul]
  have hshl' : BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 (2 * n) := by
    rw [shl_one_bv_eq_two_mul, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_mul]
  have htoNat : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpos : 0 < 2 * n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd rfl hn_ne
    · omega
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x998 20
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0xa18 24
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4796 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2584#64)
  wp_steps
  refine SepWP.done (by simp only [wp_norm, hx25, hcond_n, ↓reduceIte]) (by wp_norm_lhs) ?_
  apply SepWPp.of_sepWP (mid := entry + 2604#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr1
    refine hpanic4796 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
  · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr1⟩
    have hcond : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom
    apply SepWPp.of_sepWP (mid := entry + 2608#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond, ↓reduceIte]) (by wp_norm_lhs) ?_
    rw [h_1, hsp]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
        (by simp only [wp_norm, hcond, ↓reduceIte])
        (by wp_norm_lhs)
        (by simp only [wp_norm, ‹sf_1.sp = sf.sp›, h_1, hsp])
        (by simp only [arm64_norm, wp_norm]; rw [htr1, h, htrace])
        (by simp only [arm64_norm, wp_norm, *])
        (by wp_norm_lhs)
        (by simp only [wp_norm, h_13, h_3])
        (by simp only [wp_norm, h_17, h_7])
        (by simp only [wp_norm, h_18, h_8, hx25])
        (by simp only [wp_norm, h_19, h_9])
        (by simp only [wp_norm, h_20, h_10])
        (by simp only [wp_norm, h_21, h_11])
        (by simp only [wp_norm, hcs_sf, hpost_sf]))

end CryptoVerification.SpqrV1.Poly.NextChunk
