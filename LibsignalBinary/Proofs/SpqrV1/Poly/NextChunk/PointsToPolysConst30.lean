/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `points_to_polys` Constant Basis Loop (`n = 30`)

**Checked by Lean.**

Verifies the `n = 30` constant Lagrange basis copy loop (`0x6a7f4..0x6adb4`, `+1136 -> +2608`)
from `COMPLETE_POINTS_POLYS_30`.
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_30 :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_30 :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one ofNat_succ_add_neg_one ofNat_add_one_eq_succ

/-! ## `n = 30` Constant Basis Loop (`0x6a81c..0x6a8d4 -> 0x6ad1c..0x6adb4`) -/

/-- Loop body (`0x6a884..0x6a8bc -> 0x6a85c..0x6a880`) for `n = 30`, inducted over `rest : List Poly`. -/
theorem basis_n30_loop_sepWPp {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp basisPtr roBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hbasis_mod : basisPtr.toNat % 8 = 0)
    (R : SepProp) :
    ∀ (rest : List Poly) (i : Nat),
      rest ≠ [] →
      i + rest.length = 30 →
      (∀ p ∈ rest, p.coefficients.length = 30) →
      ∀ (s : State) (u672 : BitVec 64) (Frame : SepProp),
        s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1280#64 →
        s.status = .Running →
        s.sp = fsp →
        s.trace = s0.trace →
        s.readReg64 .x19 = basisPtr →
        s.readReg64 .x20 = BitVec.ofNat 64 (24 * i) →
        s.readReg64 .x21 = roBase + BitVec.ofNat 64 (60 * i) →
        s.readReg64 .x22 = BitVec.ofNat 64 (i + 1) →
        (∀ s1,
          s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2456#64 →
          s1.status = .Running →
          s1.sp = fsp →
          s1.trace = s0.trace →
          calleeSavedVRegs s1 = calleeSavedVRegs s →
          s1.readReg64 .x23 = s.readReg64 .x23 →
          s1.readReg64 .x25 = s.readReg64 .x25 →
          s1.readReg64 .x26 = s.readReg64 .x26 →
          s1.readReg64 .x27 = s.readReg64 .x27 →
          s1.readReg64 .x28 = s.readReg64 .x28 →
          s1.readReg64 .x29 = s.readReg64 .x29 →
          SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
            (A.pool ∗
             ((roBase + BitVec.ofNat 64 (60 * i)) ↦ᵣ polysToBytes rest) ∗
             polyListOf A (basisPtr + BitVec.ofNat 64 (24 * i)) rest ∗
             ((fsp + 656#64) ↦₆₄ 30#64) ∗
             ((fsp + 672#64) ↦₆₄ 30#64) ∗
             stackAt fsp allocHookStack ∗ Frame)
            Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
          (A.pool ∗
           ((roBase + BitVec.ofNat 64 (60 * i)) ↦ᵣ polysToBytes rest) ∗
           memRegion (basisPtr + BitVec.ofNat 64 (24 * i)) (24 * rest.length) ∗
           ((fsp + 656#64) ↦₆₄ 30#64) ∗
           ((fsp + 672#64) ↦₆₄ u672) ∗
           stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
  | [], _, hne, _, _ => absurd rfl hne
  | p :: ps', i, _, hi_len, hall => by
    intro s u672 Frame hpc hrun hsp htrace hx19 hx20 hx21 hx22 hcont
    have hlen_cons : (p :: ps').length = ps'.length + 1 := rfl
    have hi_lt : i < 30 := by omega
    have hp_len : p.coefficients.length = 30 := hall p List.mem_cons_self
    have hp_bytes : (gf16SliceBytes p.coefficients).length = 60 := by
      rw [gf16SliceBytes_length, hp_len]
    obtain ⟨w0, w1, w2, w3, w4, d2, d3, d4, w7, hro60, hrw60⟩ := exists_words_60 hp_bytes
    obtain ⟨hal0, hal8, hal16⟩ := align8_basis_step basisPtr hbasis_mod i
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
    have hpanic4724 := fun (s : State) (P : SepProp) =>
      @sepWPp_panic_of_sepWP_4724 b ext Q s0 s P R
    have hcmp_lt : ¬(BitVec.ofNat 64 i == 30#64) = true := by
      simpa using ofNat_beq_ofNat_false i 30 hi_lt (by decide)
    have hcmp_sub_lt : ¬(BitVec.ofNat 64 i - 30#64 == 0#64) = true := by
      simpa using ofNat_sub_ofNat_beq_zero_false i 30 hi_lt (by decide)
    have hx20_next : BitVec.ofNat 64 (24 * i) + 24#64 = BitVec.ofNat 64 (24 * (i + 1)) := by
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add]
      congr 1
    have hx21_next : (roBase + BitVec.ofNat 64 (60 * i)) + 60#64 =
        roBase + BitVec.ofNat 64 (60 * (i + 1)) := by
      rw [BitVec.add_assoc, show (60#64 : BitVec 64) = BitVec.ofNat 64 60 from rfl,
          ← BitVec.ofNat_add]
      congr 2
    poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x4d8 104
    dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4724 hcont ⊢
    generalize_entry hentry :
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 1296#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr1
      refine hpanic4724 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
    · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr1⟩
      have hcond : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom
      have hsp_sf1 : sf_1.sp = fsp := by
        simp only [‹sf_1.sp = sf.sp›, h_1, hsp]
      have hx19_sf1 : sf_1.readReg64 (Reg.gpr 19#5) = basisPtr := by
        simp only [h_12, h_2, hx19]
      have hx20_sf1 : sf_1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 (24 * i) := by
        simp only [h_13, h_3, hx20]
      have hx21_sf1 : sf_1.readReg64 (Reg.gpr 21#5) = roBase + BitVec.ofNat 64 (60 * i) := by
        simp only [h_14, h_4, hx21]
      have hx22_sf1 : sf_1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (i + 1) := by
        simp only [h_15, h_5, hx22]
      rw [show (60 * i : Nat) = 2 * 30 * i by omega,
          polysToBytes_cons_ro roBase 30 i p ps' hp_len,
          show (2 * 30 * i : Nat) = 60 * i by omega,
          show (2 * 30 * (i + 1) : Nat) = 60 * (i + 1) by omega,
          hro60 (roBase + BitVec.ofNat 64 (60 * i)),
          memRegion_split_60 (sf_1.readReg64 (Reg.gpr 0#5)),
          hlen_cons,
          memRegion_split_basis_cons basisPtr i ps'.length (by omega)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro u_cap
      apply SepWPp.exists_elim; intro u_ptr
      apply SepWPp.exists_elim; intro u_len
      apply SepWPp.exists_elim; intro u52
      apply SepWPp.exists_elim; intro u48
      apply SepWPp.exists_elim; intro u40
      apply SepWPp.exists_elim; intro u32
      apply SepWPp.exists_elim; intro u24
      apply SepWPp.exists_elim; intro u16
      apply SepWPp.exists_elim; intro u8
      apply SepWPp.exists_elim; intro u0
      apply SepWPp.of_sepWP (mid := entry + 1300#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hcond, ↓reduceIte]) (by wp_norm_lhs) ?_
      rw [h_1, hsp]
      apply SepWPp.of_sepWP (mid := entry + 1320#64)
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
      -- Shift ro atoms at +40..+52 to +44..+52 for ldur q0, [x21, #0x2c]
      have hro_shift := ro_shift_40_48 (roBase + BitVec.ofNat 64 (60 * i)) d2 d3 d4
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        ((((roBase + BitVec.ofNat 64 (60 * i)) + 40#64) ↦₆₄ᵣ (d3 ++ d2)) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 48#64) ↦₃₂ᵣ d4)) ∗
        (A.pool ∗
         ((roBase + BitVec.ofNat 64 (60 * i)) ↦₆₄ᵣ w0) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 8#64) ↦₆₄ᵣ w1) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 16#64) ↦₆₄ᵣ w2) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 24#64) ↦₆₄ᵣ w3) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 32#64) ↦₆₄ᵣ w4) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 52#64) ↦₆₄ᵣ w7) ∗
         ((roBase + BitVec.ofNat 64 (60 * (i + 1))) ↦ᵣ polysToBytes ps') ∗
         A.live (sf_1.readReg64 (Reg.gpr 0#5)) 60 2 ∗
         ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ w0) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ u32) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ u40) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₃₂ u48) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 52#64) ↦₆₄ u52) ∗
         ((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ u_len) ∗
         (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ u_ptr) ∗
         (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ u_cap) ∗
         memRegion (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) (24 * ps'.length) ∗
         ((fsp + 656#64) ↦₆₄ 30#64) ∗
         ((fsp + 672#64) ↦₆₄ u672) ∗
         stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      rw [hro_shift]
      apply SepWPp.of_sepWP (mid := entry + 1332#64)
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
      -- Shift rw atoms at +40..+52 to +44..+52 for stur q0, [x0, #0x2c], and restore ro atoms
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        (((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ (d3 ++ d2)) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₃₂ u48)) ∗
        ((((roBase + BitVec.ofNat 64 (60 * i)) + 40#64) ↦₃₂ᵣ d2) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 44#64) ↦₆₄ᵣ (d4 ++ d3))) ∗
        (A.pool ∗
         ((roBase + BitVec.ofNat 64 (60 * i)) ↦₆₄ᵣ w0) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 8#64) ↦₆₄ᵣ w1) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 16#64) ↦₆₄ᵣ w2) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 24#64) ↦₆₄ᵣ w3) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 32#64) ↦₆₄ᵣ w4) ∗
         (((roBase + BitVec.ofNat 64 (60 * i)) + 52#64) ↦₆₄ᵣ w7) ∗
         ((roBase + BitVec.ofNat 64 (60 * (i + 1))) ↦ᵣ polysToBytes ps') ∗
         A.live (sf_1.readReg64 (Reg.gpr 0#5)) 60 2 ∗
         ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ w0) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ w4) ∗
         ((sf_1.readReg64 (Reg.gpr 0#5) + 52#64) ↦₆₄ u52) ∗
         ((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ u_len) ∗
         (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ u_ptr) ∗
         (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ u_cap) ∗
         memRegion (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) (24 * ps'.length) ∗
         ((fsp + 656#64) ↦₆₄ 30#64) ∗
         ((fsp + 672#64) ↦₆₄ u672) ∗
         stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
      rw [rw_shift_40_48 (sf_1.readReg64 (Reg.gpr 0#5)) d2 d3 u48, ← hro_shift]
      apply SepWPp.of_sepWP
        (mid := if (BitVec.ofNat 64 (i + 1 + 1) == 31#64) = true then entry + 2456#64 else entry + 1280#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hx22_sf1, hcmp_lt, hcmp_sub_lt, ↓reduceIte]) (by wp_norm_lhs) ?_
      have hpoly_i :
          (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ 30#64) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 30#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 60 2 ∗
           ((sf_1.readReg64 (Reg.gpr 0#5)) ↦ₛ gf16SliceBytes p.coefficients)) ⊢
          polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) p :=
        polyOf_of_pointsToBytes A (basisPtr + BitVec.ofNat 64 (24 * i))
          (sf_1.readReg64 (Reg.gpr 0#5)) p 30 (by decide) (by decide) hoom hp_len
      cases ps' with
      | nil =>
        have hi29 : i = 29 := by simp at hi_len; omega
        subst hi29
        simp only [hx19_sf1, hx20_sf1, hx21_sf1, hx22_sf1,
          BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
        rw [polyListOf_cons_off A basisPtr 29 p [],
            show polyListOf A (basisPtr + BitVec.ofNat 64 (24 * 30)) [] = emp from rfl,
            show (60 * 29 : Nat) = 2 * 30 * 29 by decide,
            polysToBytes_cons_ro roBase 30 29 p [] hp_len] at hcont
        simp only [BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd, sepConj_emp] at hcont
        refine SepWPp.weaken_pre ?_
          (hcont _ (by simp only [wp_norm, hx22_sf1, ↓reduceIte]) (by wp_norm_lhs)
            (by simp only [wp_norm, hsp_sf1])
            (by simp only [arm64_norm, wp_norm]; rw [htr1, h, htrace])
            (by simp only [arm64_norm, wp_norm, *])
            (by simp only [wp_norm, h_16, h_6])
            (by simp only [wp_norm, h_18, h_8])
            (by simp only [wp_norm, h_19, h_9])
            (by simp only [wp_norm, h_20, h_10])
            (by simp only [wp_norm, h_21, h_11])
            (by simp only [wp_norm, hcs_sf, hpost_sf]))
        have hro_eq := (hro60 (roBase + 1740#64)).symm
        have hrw_eq := (hrw60 (sf_1.readReg64 (Reg.gpr 0#5))).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hro_eq hrw_eq hpoly_i
        refine Entails.trans (Entails.of_eq (show _ =
          (((basisPtr + 696#64) ↦₆₄ 30#64) ∗
           ((basisPtr + 704#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           ((basisPtr + 712#64) ↦₆₄ 30#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 60 2 ∗
           (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ w0) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ w4) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₃₂ d2) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 44#64) ↦₆₄ (d4 ++ d3)) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 52#64) ↦₆₄ w7))) ∗
          (((roBase + 1740#64) ↦₆₄ᵣ w0) ∗
           ((roBase + 1748#64) ↦₆₄ᵣ w1) ∗
           ((roBase + 1756#64) ↦₆₄ᵣ w2) ∗
           ((roBase + 1764#64) ↦₆₄ᵣ w3) ∗
           ((roBase + 1772#64) ↦₆₄ᵣ w4) ∗
           ((roBase + 1780#64) ↦₆₄ᵣ (d3 ++ d2)) ∗
           ((roBase + 1788#64) ↦₃₂ᵣ d4) ∗
           ((roBase + 1792#64) ↦₆₄ᵣ w7)) ∗
          (A.pool ∗
           ((roBase + 1800#64) ↦ᵣ polysToBytes []) ∗
           memRegion (basisPtr + 720#64) 0 ∗
           ((fsp + 656#64) ↦₆₄ 30#64) ∗
           ((fsp + 672#64) ↦₆₄ 30#64) ∗
           stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        rw [hrw_eq, hro_eq, ProofLib.memRegion_zero]
        simp only [emp_sepConj, sepConj_emp]
        refine Entails.trans (sepConj_mono_left hpoly_i) ?_
        exact Entails.of_eq (by ac_rfl)
      | cons p' ps'' =>
        have hi2_lt : i + 1 + 1 < 31 := by simp at hi_len; omega
        have hcmp_end : ¬(BitVec.ofNat 64 (i + 1 + 1) == 31#64) = true := by
          simpa using ofNat_beq_ofNat_false (i + 1 + 1) 31 hi2_lt (by decide)
        have hro_eq := (hro60 (roBase + BitVec.ofNat 64 (60 * i))).symm
        have hrw_eq := (hrw60 (sf_1.readReg64 (Reg.gpr 0#5))).symm
        refine SepWPp.weaken_pre ?_
          (basis_n30_loop_sepWPp hA s0 fsp basisPtr roBase hfsp_align hbasis_mod R
            (p' :: ps'') (i + 1) (List.cons_ne_nil _ _) (by simp at hi_len ⊢; omega)
            (fun q hq => hall q (List.mem_cons_of_mem _ hq))
            _ (BitVec.ofNat 64 (i + 1))
            (((roBase + BitVec.ofNat 64 (60 * i)) ↦ᵣ gf16SliceBytes p.coefficients) ∗
             polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) p ∗ Frame)
            (by rw [hentry]; simp only [wp_norm, hx22_sf1, hcmp_end, Bool.false_eq_true, ↓reduceIte])
            (by wp_norm_lhs)
            (by simp only [wp_norm, hsp_sf1])
            (by simp only [arm64_norm, wp_norm]; rw [htr1, h, htrace])
            (by simp only [wp_norm, hx19_sf1])
            (by simp only [wp_norm, hx20_sf1, hx20_next])
            (by simp only [wp_norm, hx21_sf1, hx21_next])
            (by simp only [wp_norm, hx22_sf1])
            (fun s1 hpc1 hrun1 hsp1 htr_s1 hvregs_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 => by
              refine SepWPp.weaken_pre ?_
                (hcont s1 (by rw [hentry] at hpc1; exact hpc1) hrun1 hsp1 htr_s1
                  (by rw [hvregs_1]; simp only [arm64_norm, wp_norm, *])
                  (by rw [hx23_1]; simp only [wp_norm, h_16, h_6])
                  (by rw [hx25_1]; simp only [wp_norm, h_18, h_8])
                  (by rw [hx26_1]; simp only [wp_norm, h_19, h_9])
                  (by rw [hx27_1]; simp only [wp_norm, h_20, h_10])
                  (by rw [hx28_1]; simp only [wp_norm, h_21, h_11])
                  (by rw [hx29_1]; simp only [wp_norm, hcs_sf, hpost_sf]))
              rw [show (60 * i : Nat) = 2 * 30 * i by omega,
                  polysToBytes_cons_ro roBase 30 i p (p' :: ps'') hp_len,
                  show (2 * 30 * i : Nat) = 60 * i by omega,
                  show (2 * 30 * (i + 1) : Nat) = 60 * (i + 1) by omega,
                  polyListOf_cons_off A basisPtr i p (p' :: ps'')]
              exact Entails.of_eq (by ac_rfl)))
        refine Entails.trans (Entails.of_eq (show _ =
          (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ 30#64) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 30#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 60 2 ∗
           (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ w0) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ w4) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₃₂ d2) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 44#64) ↦₆₄ (d4 ++ d3)) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 52#64) ↦₆₄ w7))) ∗
          (((roBase + BitVec.ofNat 64 (60 * i)) ↦₆₄ᵣ w0) ∗
           (((roBase + BitVec.ofNat 64 (60 * i)) + 8#64) ↦₆₄ᵣ w1) ∗
           (((roBase + BitVec.ofNat 64 (60 * i)) + 16#64) ↦₆₄ᵣ w2) ∗
           (((roBase + BitVec.ofNat 64 (60 * i)) + 24#64) ↦₆₄ᵣ w3) ∗
           (((roBase + BitVec.ofNat 64 (60 * i)) + 32#64) ↦₆₄ᵣ w4) ∗
           (((roBase + BitVec.ofNat 64 (60 * i)) + 40#64) ↦₆₄ᵣ (d3 ++ d2)) ∗
           (((roBase + BitVec.ofNat 64 (60 * i)) + 48#64) ↦₃₂ᵣ d4) ∗
           (((roBase + BitVec.ofNat 64 (60 * i)) + 52#64) ↦₆₄ᵣ w7)) ∗
          (A.pool ∗
           ((roBase + BitVec.ofNat 64 (60 * (i + 1))) ↦ᵣ polysToBytes (p' :: ps'')) ∗
           memRegion (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) (24 * (p' :: ps'').length) ∗
           ((fsp + 656#64) ↦₆₄ 30#64) ∗
           ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
           stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        rw [hrw_eq, hro_eq]
        refine Entails.trans (sepConj_mono_left hpoly_i) ?_
        exact Entails.of_eq (by ac_rfl)

/-- `n = 30` constant basis case (`0x6a7f4 -> 0x6a81c..0x6a8d4 -> 0x6ad1c..0x6adb4`, `+1136 -> +2608`). -/
theorem basis_n30_sepWPp {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64)
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 u656 u664 u672 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 30#64)
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
      s1.readReg64 .x25 = 30#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         completePointsPolys30At b ∗
         basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_30) ∗
         A.live accPtr 60 2 ∗ memRegion accPtr 60 ∗
         ((fsp + 24#64) ↦₆₄ 30#64) ∗
         ((fsp + 96#64) ↦₆₄ 30#64) ∗
         ((fsp + 656#64) ↦₆₄ 30#64) ∗
         ((fsp + 664#64) ↦₆₄ basisPtr) ∗
         ((fsp + 672#64) ↦₆₄ 30#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       completePointsPolys30At b ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗
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
  have hpanic4880 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4880 b ext Q s0 s P R
  have hadrp : ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1212#64) &&&
      0xfffffffffffff000#64 = b + 0x65000#64 :=
    polyNextChunk_adrp_page hb 1212#64 rfl
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x470 104
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4880 hadrp hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1196#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr1
    refine hpanic4880 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨halign1, htr1⟩
    have hcond1 : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom1
    have hsp_sf1 : sf_1.sp = fsp := by
      simp only [‹sf_1.sp = sf.sp›, h_1, hsp]
    apply SepWPp.of_sepWP (mid := entry + 1200#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) ?_
    rw [h_1, hsp]
    apply SepWPp.of_sepWP (mid := entry + 1280#64)
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    obtain ⟨_, hlen30, hall30⟩ := completePointsPolys30_spec
    have hne30 : extractCompletePolys COMPLETE_POINTS_POLYS_30 ≠ [] := by
      intro hnil; rw [hnil] at hlen30; contradiction
    have hro30 : completePointsPolys30At b =
        (((b + bv% (ls_bytes% "0100a521526fb8ea3c622b41")) + BitVec.ofNat 64 (60 * 0)) ↦ᵣ
          polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_30)) := by
      unfold completePointsPolys30At completePointsPolys30Bytes
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    have hmem30 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 720 =
        memRegion ((sf_1.readReg64 (Reg.gpr 0#5)) + BitVec.ofNat 64 (24 * 0))
          (24 * (extractCompletePolys COMPLETE_POINTS_POLYS_30).length) := by
      rw [hlen30]; simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul]
    rw [hro30, hmem30]
    refine SepWPp.weaken_pre ?_
      (basis_n30_loop_sepWPp hA s0 fsp (sf_1.readReg64 (Reg.gpr 0#5)) (b + bv% (ls_bytes% "0100a521526fb8ea3c622b41"))
        hfsp_align halign1 R
        (extractCompletePolys COMPLETE_POINTS_POLYS_30) 0 hne30
        (by rw [Nat.zero_add]; exact hlen30) hall30
        _ 0#64
        (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 720 8 ∗
         ((fsp + 24#64) ↦₆₄ u24) ∗
         ((fsp + 96#64) ↦₆₄ 30#64) ∗
         ((fsp + 664#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗ Frame)
        (by rw [hentry]; wp_norm_goal)
        (by wp_norm_lhs)
        (by simp only [wp_norm, hsp_sf1])
        (by simp only [arm64_norm, wp_norm]; rw [htr1, h, htrace])
        (by simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero])
        (by simp only [wp_norm, Nat.mul_zero, BitVec.ofNat_eq_ofNat])
        (by simp only [wp_norm, hadrp, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd])
        (by simp only [wp_norm])
        (fun s1 hpc1 hrun1 hsp1 htr_s1 hvregs_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 => by
          refine SepWPp.weaken_pre ?_
            (basis_loop_exit_sepWPp hA s0 s1 fsp (sf_1.readReg64 (Reg.gpr 0#5)) hfsp_align
              30 (by decide) (by decide) u24
              (((b + bv% (ls_bytes% "0100a521526fb8ea3c622b41") + BitVec.ofNat 64 (60 * 0)) ↦ᵣ
                  polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_30)) ∗
               polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                 (extractCompletePolys COMPLETE_POINTS_POLYS_30) ∗
               A.live (sf_1.readReg64 (Reg.gpr 0#5)) 720 8 ∗
               ((fsp + 96#64) ↦₆₄ 30#64) ∗
               ((fsp + 672#64) ↦₆₄ 30#64) ∗ Frame) R
              hpc1 hrun1 hsp1 htr_s1
              (by rw [hx25_1]; simp only [wp_norm, h_18, h_8, hx25])
              (fun s2 accPtr hacc hpc2 hrun2 hsp2 htr2 hvregs_2 hx0_2 hx20_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => by
                have hbasis :
                    (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 720 8 ∗
                     polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                       (extractCompletePolys COMPLETE_POINTS_POLYS_30)) ⊢
                    basisVecAt A (sf_1.readReg64 (Reg.gpr 0#5)) (extractCompletePolys COMPLETE_POINTS_POLYS_30) := by
                  unfold basisVecAt
                  rw [hlen30]
                  simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul]
                  exact Entails.pure_right hoom1 (Entails.refl _)
                refine SepWPp.weaken_pre ?_
                  (hcont s2 (sf_1.readReg64 (Reg.gpr 0#5)) accPtr hoom1 hacc
                    (by rw [hentry] at hpc2; exact hpc2) hrun2 hsp2 htr2
                    (by rw [hvregs_2, hvregs_1]; simp only [arm64_norm, wp_norm, *])
                    hx0_2
                    (by rw [hx20_2, hx23_1]; simp only [wp_norm, h_16, h_6])
                    hx24_2 hx25_2
                    (by rw [hx26_2, hx26_1]; simp only [wp_norm, h_19, h_9])
                    (by rw [hx27_2, hx27_1]; simp only [wp_norm, h_20, h_10])
                    (by rw [hx28_2, hx28_1]; simp only [wp_norm, h_21, h_11])
                    (by rw [hx29_2, hx29_1]; simp only [wp_norm, hcs_sf, hpost_sf]))
                rw [← hro30]
                refine Entails.trans (Entails.of_eq (show _ =
                  (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 720 8 ∗
                   polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                     (extractCompletePolys COMPLETE_POINTS_POLYS_30)) ∗
                  (A.pool ∗
                   completePointsPolys30At b ∗
                   A.live accPtr 60 2 ∗ memRegion accPtr 60 ∗
                   ((fsp + 24#64) ↦₆₄ 30#64) ∗
                   ((fsp + 96#64) ↦₆₄ 30#64) ∗
                   ((fsp + 656#64) ↦₆₄ 30#64) ∗
                   ((fsp + 664#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                   ((fsp + 672#64) ↦₆₄ 30#64) ∗
                   stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
                refine Entails.trans (sepConj_mono_left hbasis) ?_
                exact Entails.of_eq (by ac_rfl)))
          exact Entails.of_eq (by ac_rfl)))
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.NextChunk
