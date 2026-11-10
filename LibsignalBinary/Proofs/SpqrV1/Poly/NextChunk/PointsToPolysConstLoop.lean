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
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Constant Basis Loops (`n = 36, 34`)

**Checked by Lean.**

Verifies the loop-based constant Lagrange basis copy paths `basis_n36_sepWPp` and
`basis_n34_sepWPp` (`+1136 -> +2608`) from `COMPLETE_POINTS_POLYS_{36,34}`.
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two'' :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight'' :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

/-! ## 1. Arithmetic, Alignment, and Separation-Logic Helpers for Constant Basis Loops -/

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_sub_one (i : Nat) :
    BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]

private theorem add_neg_one_eq_sub_one (x : BitVec 64) :
    x + 18446744073709551615#64 = x - 1#64 := by bv_robdd

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_succ_add_neg_one (i : Nat) :
    BitVec.ofNat 64 (i + 1) + 18446744073709551615#64 = BitVec.ofNat 64 i := by
  rw [add_neg_one_eq_sub_one, ofNat_succ_sub_one]

@[local simp, local arm64_norm, local wp_norm]
theorem ofNat_add_one_eq_succ (i : Nat) :
    BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [← BitVec.ofNat_add]

theorem ofNat_sub_ofNat_beq_zero_false (i n : Nat) (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 i - BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h' : BitVec.ofNat 64 i = BitVec.ofNat 64 n := by
    have := congrArg (· + BitVec.ofNat 64 n) h
    simpa [BitVec.sub_add_cancel] using this
  have ht := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
  omega

theorem ofNat_beq_ofNat_false (i n : Nat) (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 i == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
  omega

private theorem align8_add_mul24_bv (ptr off : BitVec 64)
    (hp : ptr &&& 7#64 = 0#64) (ho : off &&& 7#64 = 0#64) :
    ((ptr + off) &&& 7#64 == 0#64) = true ∧
    (((ptr + off) + 8#64) &&& 7#64 == 0#64) = true ∧
    (((ptr + off) + 16#64) &&& 7#64 == 0#64) = true := by
  bv_robdd

theorem align8_basis_step (ptr : BitVec 64) (hmod : ptr.toNat % 8 = 0) (i : Nat) :
    ((ptr + BitVec.ofNat 64 (24 * i)) &&& 7#64 == 0#64) = true ∧
    (((ptr + BitVec.ofNat 64 (24 * i)) + 8#64) &&& 7#64 == 0#64) = true ∧
    (((ptr + BitVec.ofNat 64 (24 * i)) + 16#64) &&& 7#64 == 0#64) = true := by
  have hp : ptr &&& 7#64 = 0#64 := beq_iff_eq.mp (align8_of_mod8_eq_zero hmod)
  have ho : BitVec.ofNat 64 (24 * i) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    change (24 * i % 2 ^ 64) &&& 7 = 0
    rw [Nat.and_two_pow_sub_one_eq_mod _ 3]
    omega
  exact align8_add_mul24_bv ptr (BitVec.ofNat 64 (24 * i)) hp ho

theorem memRegion_split_basis_cons (basisPtr : BitVec 64) (i k : Nat) (hk : 24 * (k + 1) < 2 ^ 64) :
    memRegion (basisPtr + BitVec.ofNat 64 (24 * i)) (24 * (k + 1)) =
      (∃∗ u_cap : BitVec 64, ∃∗ u_ptr : BitVec 64, ∃∗ u_len : BitVec 64,
        ((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ u_len) ∗
        (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ u_ptr) ∗
        (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ u_cap)) ∗
      memRegion (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) (24 * k) := by
  have h24 : 24 * (k + 1) = 24 + 24 * k := by omega
  have hb' : basisPtr + BitVec.ofNat 64 (24 * (i + 1)) =
      (basisPtr + BitVec.ofNat 64 (24 * i)) + 24#64 := by
    rw [BitVec.add_assoc, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl,
        ← BitVec.ofNat_add]
    congr 2
  rw [ProofLib.memRegion_split' (b := basisPtr + BitVec.ofNat 64 (24 * i))
        (n := 24) (k := 24 * k) (b' := basisPtr + BitVec.ofNat 64 (24 * (i + 1)))
        h24 hb' (by omega),
      memRegion_split_polyHeader (basisPtr + BitVec.ofNat 64 (24 * i))]

theorem polyListOf_cons_off (A : RustAlloc) (basisPtr : BitVec 64) (i : Nat) (p : Poly) (ps : List Poly) :
    polyListOf A (basisPtr + BitVec.ofNat 64 (24 * i)) (p :: ps) =
      polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) p ∗
      polyListOf A (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) ps := by
  change polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) p ∗
      polyListOf A ((basisPtr + BitVec.ofNat 64 (24 * i)) + 24#64) ps = _
  have h : (basisPtr + BitVec.ofNat 64 (24 * i)) + 24#64 =
      basisPtr + BitVec.ofNat 64 (24 * (i + 1)) := by
    rw [BitVec.add_assoc, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl,
        ← BitVec.ofNat_add]
    congr 2
  rw [h]

theorem polysToBytes_cons_ro (roBase : BitVec 64) (m i : Nat) (p : Poly) (ps : List Poly)
    (hp : p.coefficients.length = m) :
    ((roBase + BitVec.ofNat 64 (2 * m * i)) ↦ᵣ polysToBytes (p :: ps)) =
      ((roBase + BitVec.ofNat 64 (2 * m * i)) ↦ᵣ gf16SliceBytes p.coefficients) ∗
      ((roBase + BitVec.ofNat 64 (2 * m * (i + 1))) ↦ᵣ polysToBytes ps) := by
  rw [polysToBytes_cons, pointsToBytesRO_append, gf16SliceBytes_length, hp]
  have h : (roBase + BitVec.ofNat 64 (2 * m * i)) + BitVec.ofNat 64 (2 * m) =
      roBase + BitVec.ofNat 64 (2 * m * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [h]

/-! ## 2. `n = 36` Constant Basis Loop (`0x6a9c8..0x6aa80 -> 0x6ad1c..0x6adb4`) -/

/-- Loop body (`0x6aa30..0x6aa68 -> 0x6aa08..0x6aa2c`) for `n = 36`, inducted over `rest : List Poly`. -/
theorem basis_n36_loop_sepWPp {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp basisPtr roBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hbasis_mod : basisPtr.toNat % 8 = 0)
    (R : SepProp) :
    ∀ (rest : List Poly) (i : Nat),
      rest ≠ [] →
      i + rest.length = 36 →
      (∀ p ∈ rest, p.coefficients.length = 36) →
      ∀ (s : State) (u672 : BitVec 64) (Frame : SepProp),
        s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1708#64 →
        s.status = .Running →
        s.sp = fsp →
        s.trace = s0.trace →
        s.readReg64 .x19 = basisPtr →
        s.readReg64 .x20 = BitVec.ofNat 64 (24 * i) →
        s.readReg64 .x21 = roBase + BitVec.ofNat 64 (72 * i) →
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
             ((roBase + BitVec.ofNat 64 (72 * i)) ↦ᵣ polysToBytes rest) ∗
             polyListOf A (basisPtr + BitVec.ofNat 64 (24 * i)) rest ∗
             ((fsp + 656#64) ↦₆₄ 36#64) ∗
             ((fsp + 672#64) ↦₆₄ 36#64) ∗
             stackAt fsp allocHookStack ∗ Frame)
            Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
          (A.pool ∗
           ((roBase + BitVec.ofNat 64 (72 * i)) ↦ᵣ polysToBytes rest) ∗
           memRegion (basisPtr + BitVec.ofNat 64 (24 * i)) (24 * rest.length) ∗
           ((fsp + 656#64) ↦₆₄ 36#64) ∗
           ((fsp + 672#64) ↦₆₄ u672) ∗
           stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
  | [], _, hne, _, _ => absurd rfl hne
  | p :: ps', i, _, hi_len, hall => by
    intro s u672 Frame hpc hrun hsp htrace hx19 hx20 hx21 hx22 hcont
    have hlen_cons : (p :: ps').length = ps'.length + 1 := rfl
    have hi_lt : i < 36 := by omega
    have hp_len : p.coefficients.length = 36 := hall p List.mem_cons_self
    have hp_bytes : (gf16SliceBytes p.coefficients).length = 72 := by
      rw [gf16SliceBytes_length, hp_len]
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hro72, hrw72⟩ := exists_words_72 hp_bytes
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
    have hpanic4700 := fun (s : State) (P : SepProp) =>
      @sepWPp_panic_of_sepWP_4700 b ext Q s0 s P R
    have hcmp_lt : ¬(BitVec.ofNat 64 i == 36#64) = true := by
      simpa using ofNat_beq_ofNat_false i 36 hi_lt (by decide)
    have hcmp_sub_lt : ¬(BitVec.ofNat 64 i - 36#64 == 0#64) = true := by
      simpa using ofNat_sub_ofNat_beq_zero_false i 36 hi_lt (by decide)
    have hx20_next : BitVec.ofNat 64 (24 * i) + 24#64 = BitVec.ofNat 64 (24 * (i + 1)) := by
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add]
      congr 1
    have hx21_next : (roBase + BitVec.ofNat 64 (72 * i)) + 72#64 =
        roBase + BitVec.ofNat 64 (72 * (i + 1)) := by
      rw [BitVec.add_assoc, show (72#64 : BitVec 64) = BitVec.ofNat 64 72 from rfl,
          ← BitVec.ofNat_add]
      congr 2
    poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x684 104
    dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4700 hcont ⊢
    generalize_entry hentry :
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 1724#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr1
      refine hpanic4700 _ _ ?_
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
      have hx21_sf1 : sf_1.readReg64 (Reg.gpr 21#5) = roBase + BitVec.ofNat 64 (72 * i) := by
        simp only [h_14, h_4, hx21]
      have hx22_sf1 : sf_1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (i + 1) := by
        simp only [h_15, h_5, hx22]
      rw [show (72 * i : Nat) = 2 * 36 * i by omega,
          polysToBytes_cons_ro roBase 36 i p ps' hp_len,
          show (2 * 36 * i : Nat) = 72 * i by omega,
          show (2 * 36 * (i + 1) : Nat) = 72 * (i + 1) by omega,
          hro72 (roBase + BitVec.ofNat 64 (72 * i)),
          memRegion_split_72 (sf_1.readReg64 (Reg.gpr 0#5)),
          hlen_cons,
          memRegion_split_basis_cons basisPtr i ps'.length (by omega)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro u_cap
      apply SepWPp.exists_elim; intro u_ptr
      apply SepWPp.exists_elim; intro u_len
      apply SepWPp.exists_elim; intro u0
      apply SepWPp.exists_elim; intro u8
      apply SepWPp.exists_elim; intro u16
      apply SepWPp.exists_elim; intro u24
      apply SepWPp.exists_elim; intro u32
      apply SepWPp.exists_elim; intro u40
      apply SepWPp.exists_elim; intro u48
      apply SepWPp.exists_elim; intro u56
      apply SepWPp.exists_elim; intro u64
      apply SepWPp.of_sepWP (mid := entry + 1728#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hcond, ↓reduceIte]) (by wp_norm_lhs) ?_
      rw [h_1, hsp]
      apply SepWPp.of_sepWP
        (mid := if (BitVec.ofNat 64 (i + 1 + 1) == 37#64) = true then entry + 2456#64 else entry + 1708#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hx22_sf1, hcmp_lt, hcmp_sub_lt, ↓reduceIte]) (by wp_norm_lhs) ?_
      have hpoly_i :
          (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ 36#64) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 36#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 72 2 ∗
           ((sf_1.readReg64 (Reg.gpr 0#5)) ↦ₛ gf16SliceBytes p.coefficients)) ⊢
          polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) p :=
        polyOf_of_pointsToBytes A (basisPtr + BitVec.ofNat 64 (24 * i))
          (sf_1.readReg64 (Reg.gpr 0#5)) p 36 (by decide) (by decide) hoom hp_len
      cases ps' with
      | nil =>
        have hi35 : i = 35 := by simp at hi_len; omega
        subst hi35
        simp only [hx19_sf1, hx20_sf1, hx21_sf1, hx22_sf1,
          BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
        rw [polyListOf_cons_off A basisPtr 35 p [],
            show polyListOf A (basisPtr + BitVec.ofNat 64 (24 * 36)) [] = emp from rfl,
            show (72 * 35 : Nat) = 2 * 36 * 35 by decide,
            polysToBytes_cons_ro roBase 36 35 p [] hp_len] at hcont
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
        have hro_eq := (hro72 (roBase + 2520#64)).symm
        have hrw_eq := (hrw72 (sf_1.readReg64 (Reg.gpr 0#5))).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hro_eq hrw_eq hpoly_i
        refine Entails.trans (Entails.of_eq (show _ =
          (((basisPtr + 840#64) ↦₆₄ 36#64) ∗
           ((basisPtr + 848#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           ((basisPtr + 856#64) ↦₆₄ 36#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 72 2 ∗
           (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ w0) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ w4) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ w5) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ w6) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ w7) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ w8))) ∗
          (((roBase + 2520#64) ↦₆₄ᵣ w0) ∗
           ((roBase + 2528#64) ↦₆₄ᵣ w1) ∗
           ((roBase + 2536#64) ↦₆₄ᵣ w2) ∗
           ((roBase + 2544#64) ↦₆₄ᵣ w3) ∗
           ((roBase + 2552#64) ↦₆₄ᵣ w4) ∗
           ((roBase + 2560#64) ↦₆₄ᵣ w5) ∗
           ((roBase + 2568#64) ↦₆₄ᵣ w6) ∗
           ((roBase + 2576#64) ↦₆₄ᵣ w7) ∗
           ((roBase + 2584#64) ↦₆₄ᵣ w8)) ∗
          (A.pool ∗
           ((roBase + 2592#64) ↦ᵣ polysToBytes []) ∗
           memRegion (basisPtr + 864#64) 0 ∗
           ((fsp + 656#64) ↦₆₄ 36#64) ∗
           ((fsp + 672#64) ↦₆₄ 36#64) ∗
           stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        rw [hrw_eq, hro_eq, ProofLib.memRegion_zero]
        simp only [emp_sepConj, sepConj_emp]
        refine Entails.trans (sepConj_mono_left hpoly_i) ?_
        exact Entails.of_eq (by ac_rfl)
      | cons p' ps'' =>
        have hi2_lt : i + 1 + 1 < 37 := by simp at hi_len; omega
        have hcmp_end : ¬(BitVec.ofNat 64 (i + 1 + 1) == 37#64) = true := by
          simpa using ofNat_beq_ofNat_false (i + 1 + 1) 37 hi2_lt (by decide)
        have hro_eq := (hro72 (roBase + BitVec.ofNat 64 (72 * i))).symm
        have hrw_eq := (hrw72 (sf_1.readReg64 (Reg.gpr 0#5))).symm
        refine SepWPp.weaken_pre ?_
          (basis_n36_loop_sepWPp hA s0 fsp basisPtr roBase hfsp_align hbasis_mod R
            (p' :: ps'') (i + 1) (List.cons_ne_nil _ _) (by simp at hi_len ⊢; omega)
            (fun q hq => hall q (List.mem_cons_of_mem _ hq))
            _ (BitVec.ofNat 64 (i + 1))
            (((roBase + BitVec.ofNat 64 (72 * i)) ↦ᵣ gf16SliceBytes p.coefficients) ∗
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
              rw [show (72 * i : Nat) = 2 * 36 * i by omega,
                  polysToBytes_cons_ro roBase 36 i p (p' :: ps'') hp_len,
                  show (2 * 36 * i : Nat) = 72 * i by omega,
                  show (2 * 36 * (i + 1) : Nat) = 72 * (i + 1) by omega,
                  polyListOf_cons_off A basisPtr i p (p' :: ps'')]
              exact Entails.of_eq (by ac_rfl)))
        refine Entails.trans (Entails.of_eq (show _ =
          (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ 36#64) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 36#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 72 2 ∗
           (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ w0) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ w4) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ w5) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ w6) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ w7) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ w8))) ∗
          (((roBase + BitVec.ofNat 64 (72 * i)) ↦₆₄ᵣ w0) ∗
           (((roBase + BitVec.ofNat 64 (72 * i)) + 8#64) ↦₆₄ᵣ w1) ∗
           (((roBase + BitVec.ofNat 64 (72 * i)) + 16#64) ↦₆₄ᵣ w2) ∗
           (((roBase + BitVec.ofNat 64 (72 * i)) + 24#64) ↦₆₄ᵣ w3) ∗
           (((roBase + BitVec.ofNat 64 (72 * i)) + 32#64) ↦₆₄ᵣ w4) ∗
           (((roBase + BitVec.ofNat 64 (72 * i)) + 40#64) ↦₆₄ᵣ w5) ∗
           (((roBase + BitVec.ofNat 64 (72 * i)) + 48#64) ↦₆₄ᵣ w6) ∗
           (((roBase + BitVec.ofNat 64 (72 * i)) + 56#64) ↦₆₄ᵣ w7) ∗
           (((roBase + BitVec.ofNat 64 (72 * i)) + 64#64) ↦₆₄ᵣ w8)) ∗
          (A.pool ∗
           ((roBase + BitVec.ofNat 64 (72 * (i + 1))) ↦ᵣ polysToBytes (p' :: ps'')) ∗
           memRegion (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) (24 * (p' :: ps'').length) ∗
           ((fsp + 656#64) ↦₆₄ 36#64) ∗
           ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
           stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        rw [hrw_eq, hro_eq]
        refine Entails.trans (sepConj_mono_left hpoly_i) ?_
        exact Entails.of_eq (by ac_rfl)

/-- `n = 36` constant basis case (`0x6a7f4 -> 0x6a9c8..0x6aa80 -> 0x6ad1c..0x6adb4`, `+1136 -> +2608`). -/
theorem basis_n36_sepWPp {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64)
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 u656 u664 u672 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 36#64)
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
      s1.readReg64 .x25 = 36#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         completePointsPolys36At b ∗
         basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_36) ∗
         A.live accPtr 72 2 ∗ memRegion accPtr 72 ∗
         ((fsp + 24#64) ↦₆₄ 36#64) ∗
         ((fsp + 96#64) ↦₆₄ 36#64) ∗
         ((fsp + 656#64) ↦₆₄ 36#64) ∗
         ((fsp + 664#64) ↦₆₄ basisPtr) ∗
         ((fsp + 672#64) ↦₆₄ 36#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       completePointsPolys36At b ∗
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
  have hpanic4856 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4856 b ext Q s0 s P R
  have hadrp : ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1640#64) &&&
      0xfffffffffffff000#64 = b + 0x65000#64 :=
    polyNextChunk_adrp_page hb 1640#64 rfl
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x470 24
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x634 80
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4856 hadrp hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 1624#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr1
    refine hpanic4856 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨halign1, htr1⟩
    have hcond1 : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom1
    have hsp_sf1 : sf_1.sp = fsp := by
      simp only [‹sf_1.sp = sf.sp›, h_1, hsp]
    apply SepWPp.of_sepWP (mid := entry + 1628#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) ?_
    rw [h_1, hsp]
    apply SepWPp.of_sepWP (mid := entry + 1708#64)
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    obtain ⟨_, hlen36, hall36⟩ := completePointsPolys36_spec
    have hne36 : extractCompletePolys COMPLETE_POINTS_POLYS_36 ≠ [] := by
      intro hnil; rw [hnil] at hlen36; contradiction
    have hro36 : completePointsPolys36At b =
        (((b + bv% (ls_bytes% "01003010df98e7bf90f48e9e")) + BitVec.ofNat 64 (72 * 0)) ↦ᵣ
          polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_36)) := by
      unfold completePointsPolys36At completePointsPolys36Bytes
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    have hmem36 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 864 =
        memRegion ((sf_1.readReg64 (Reg.gpr 0#5)) + BitVec.ofNat 64 (24 * 0))
          (24 * (extractCompletePolys COMPLETE_POINTS_POLYS_36).length) := by
      rw [hlen36]; simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul]
    rw [hro36, hmem36]
    refine SepWPp.weaken_pre ?_
      (basis_n36_loop_sepWPp hA s0 fsp (sf_1.readReg64 (Reg.gpr 0#5)) (b + bv% (ls_bytes% "01003010df98e7bf90f48e9e"))
        hfsp_align halign1 R
        (extractCompletePolys COMPLETE_POINTS_POLYS_36) 0 hne36
        (by rw [Nat.zero_add]; exact hlen36) hall36
        _ 0#64
        (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 864 8 ∗
         ((fsp + 24#64) ↦₆₄ u24) ∗
         ((fsp + 96#64) ↦₆₄ 36#64) ∗
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
              36 (by decide) (by decide) u24
              (((b + bv% (ls_bytes% "01003010df98e7bf90f48e9e") + BitVec.ofNat 64 (72 * 0)) ↦ᵣ
                  polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_36)) ∗
               polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                 (extractCompletePolys COMPLETE_POINTS_POLYS_36) ∗
               A.live (sf_1.readReg64 (Reg.gpr 0#5)) 864 8 ∗
               ((fsp + 96#64) ↦₆₄ 36#64) ∗
               ((fsp + 672#64) ↦₆₄ 36#64) ∗ Frame) R
              hpc1 hrun1 hsp1 htr_s1
              (by rw [hx25_1]; simp only [wp_norm, h_18, h_8, hx25])
              (fun s2 accPtr hacc hpc2 hrun2 hsp2 htr2 hvregs_2 hx0_2 hx20_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => by
                have hbasis :
                    (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 864 8 ∗
                     polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                       (extractCompletePolys COMPLETE_POINTS_POLYS_36)) ⊢
                    basisVecAt A (sf_1.readReg64 (Reg.gpr 0#5)) (extractCompletePolys COMPLETE_POINTS_POLYS_36) := by
                  unfold basisVecAt
                  rw [hlen36]
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
                rw [← hro36]
                refine Entails.trans (Entails.of_eq (show _ =
                  (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 864 8 ∗
                   polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                     (extractCompletePolys COMPLETE_POINTS_POLYS_36)) ∗
                  (A.pool ∗
                   completePointsPolys36At b ∗
                   A.live accPtr 72 2 ∗ memRegion accPtr 72 ∗
                   ((fsp + 24#64) ↦₆₄ 36#64) ∗
                   ((fsp + 96#64) ↦₆₄ 36#64) ∗
                   ((fsp + 656#64) ↦₆₄ 36#64) ∗
                   ((fsp + 664#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                   ((fsp + 672#64) ↦₆₄ 36#64) ∗
                   stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
                refine Entails.trans (sepConj_mono_left hbasis) ?_
                exact Entails.of_eq (by ac_rfl)))
          exact Entails.of_eq (by ac_rfl)))
    exact Entails.of_eq (by ac_rfl)

/-! ## 3. `n = 34` Constant Basis Loop (`0x6ac60..0x6ad18 -> 0x6ad1c..0x6adb4`) -/

/-- Loop body (`0x6acc8..0x6ad00 -> 0x6aca0..0x6acc4`) for `n = 34`, inducted over `rest : List Poly`. -/
theorem basis_n34_loop_sepWPp {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp basisPtr roBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hbasis_mod : basisPtr.toNat % 8 = 0)
    (R : SepProp) :
    ∀ (rest : List Poly) (i : Nat),
      rest ≠ [] →
      i + rest.length = 34 →
      (∀ p ∈ rest, p.coefficients.length = 34) →
      ∀ (s : State) (u672 : BitVec 64) (Frame : SepProp),
        s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2372#64 →
        s.status = .Running →
        s.sp = fsp →
        s.trace = s0.trace →
        s.readReg64 .x19 = basisPtr →
        s.readReg64 .x20 = BitVec.ofNat 64 (24 * i) →
        s.readReg64 .x21 = roBase + BitVec.ofNat 64 (68 * i) →
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
             ((roBase + BitVec.ofNat 64 (68 * i)) ↦ᵣ polysToBytes rest) ∗
             polyListOf A (basisPtr + BitVec.ofNat 64 (24 * i)) rest ∗
             ((fsp + 656#64) ↦₆₄ 34#64) ∗
             ((fsp + 672#64) ↦₆₄ 34#64) ∗
             stackAt fsp allocHookStack ∗ Frame)
            Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
          (A.pool ∗
           ((roBase + BitVec.ofNat 64 (68 * i)) ↦ᵣ polysToBytes rest) ∗
           memRegion (basisPtr + BitVec.ofNat 64 (24 * i)) (24 * rest.length) ∗
           ((fsp + 656#64) ↦₆₄ 34#64) ∗
           ((fsp + 672#64) ↦₆₄ u672) ∗
           stackAt fsp allocHookStack ∗ Frame)
          Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))
  | [], _, hne, _, _ => absurd rfl hne
  | p :: ps', i, _, hi_len, hall => by
    intro s u672 Frame hpc hrun hsp htrace hx19 hx20 hx21 hx22 hcont
    have hlen_cons : (p :: ps').length = ps'.length + 1 := rfl
    have hi_lt : i < 34 := by omega
    have hp_len : p.coefficients.length = 34 := hall p List.mem_cons_self
    have hp_bytes : (gf16SliceBytes p.coefficients).length = 68 := by
      rw [gf16SliceBytes_length, hp_len]
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hro68, hrw68⟩ := exists_words_68 hp_bytes
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
    have hpanic4712 := fun (s : State) (P : SepProp) =>
      @sepWPp_panic_of_sepWP_4712 b ext Q s0 s P R
    have hcmp_lt : ¬(BitVec.ofNat 64 i == 34#64) = true := by
      simpa using ofNat_beq_ofNat_false i 34 hi_lt (by decide)
    have hcmp_sub_lt : ¬(BitVec.ofNat 64 i - 34#64 == 0#64) = true := by
      simpa using ofNat_sub_ofNat_beq_zero_false i 34 hi_lt (by decide)
    have hx20_next : BitVec.ofNat 64 (24 * i) + 24#64 = BitVec.ofNat 64 (24 * (i + 1)) := by
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add]
      congr 1
    have hx21_next : (roBase + BitVec.ofNat 64 (68 * i)) + 68#64 =
        roBase + BitVec.ofNat 64 (68 * (i + 1)) := by
      rw [BitVec.add_assoc, show (68#64 : BitVec 64) = BitVec.ofNat 64 68 from rfl,
          ← BitVec.ofNat_add]
      congr 2
    poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x91c 104
    dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4712 hcont ⊢
    generalize_entry hentry :
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 2388#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr1
      refine hpanic4712 _ _ ?_
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
      have hx21_sf1 : sf_1.readReg64 (Reg.gpr 21#5) = roBase + BitVec.ofNat 64 (68 * i) := by
        simp only [h_14, h_4, hx21]
      have hx22_sf1 : sf_1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (i + 1) := by
        simp only [h_15, h_5, hx22]
      rw [show (68 * i : Nat) = 2 * 34 * i by omega,
          polysToBytes_cons_ro roBase 34 i p ps' hp_len,
          show (2 * 34 * i : Nat) = 68 * i by omega,
          show (2 * 34 * (i + 1) : Nat) = 68 * (i + 1) by omega,
          hro68 (roBase + BitVec.ofNat 64 (68 * i)),
          memRegion_split_68 (sf_1.readReg64 (Reg.gpr 0#5)),
          hlen_cons,
          memRegion_split_basis_cons basisPtr i ps'.length (by omega)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro u_cap
      apply SepWPp.exists_elim; intro u_ptr
      apply SepWPp.exists_elim; intro u_len
      apply SepWPp.exists_elim; intro u0
      apply SepWPp.exists_elim; intro u8
      apply SepWPp.exists_elim; intro u16
      apply SepWPp.exists_elim; intro u24
      apply SepWPp.exists_elim; intro u32
      apply SepWPp.exists_elim; intro u40
      apply SepWPp.exists_elim; intro u48
      apply SepWPp.exists_elim; intro u56
      apply SepWPp.exists_elim; intro u64
      apply SepWPp.of_sepWP (mid := entry + 2392#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hcond, ↓reduceIte]) (by wp_norm_lhs) ?_
      rw [h_1, hsp]
      apply SepWPp.of_sepWP
        (mid := if (BitVec.ofNat 64 (i + 1 + 1) == 35#64) = true then entry + 2456#64 else entry + 2372#64)
      wp_steps
      refine SepWP.done (by simp only [wp_norm, hx22_sf1, hcmp_lt, hcmp_sub_lt, ↓reduceIte]) (by wp_norm_lhs) ?_
      have hpoly_i :
          (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ 34#64) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 34#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 68 2 ∗
           ((sf_1.readReg64 (Reg.gpr 0#5)) ↦ₛ gf16SliceBytes p.coefficients)) ⊢
          polyOf A (basisPtr + BitVec.ofNat 64 (24 * i)) p :=
        polyOf_of_pointsToBytes A (basisPtr + BitVec.ofNat 64 (24 * i))
          (sf_1.readReg64 (Reg.gpr 0#5)) p 34 (by decide) (by decide) hoom hp_len
      cases ps' with
      | nil =>
        have hi33 : i = 33 := by simp at hi_len; omega
        subst hi33
        simp only [hx19_sf1, hx20_sf1, hx21_sf1, hx22_sf1,
          BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
        rw [polyListOf_cons_off A basisPtr 33 p [],
            show polyListOf A (basisPtr + BitVec.ofNat 64 (24 * 34)) [] = emp from rfl,
            show (68 * 33 : Nat) = 2 * 34 * 33 by decide,
            polysToBytes_cons_ro roBase 34 33 p [] hp_len] at hcont
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
        have hro_eq := (hro68 (roBase + 2244#64)).symm
        have hrw_eq := (hrw68 (sf_1.readReg64 (Reg.gpr 0#5))).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hro_eq hrw_eq hpoly_i
        refine Entails.trans (Entails.of_eq (show _ =
          (((basisPtr + 792#64) ↦₆₄ 34#64) ∗
           ((basisPtr + 800#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           ((basisPtr + 808#64) ↦₆₄ 34#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 68 2 ∗
           (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ w0) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ w4) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ w5) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ w6) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ w7) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₃₂ w8))) ∗
          (((roBase + 2244#64) ↦₆₄ᵣ w0) ∗
           ((roBase + 2252#64) ↦₆₄ᵣ w1) ∗
           ((roBase + 2260#64) ↦₆₄ᵣ w2) ∗
           ((roBase + 2268#64) ↦₆₄ᵣ w3) ∗
           ((roBase + 2276#64) ↦₆₄ᵣ w4) ∗
           ((roBase + 2284#64) ↦₆₄ᵣ w5) ∗
           ((roBase + 2292#64) ↦₆₄ᵣ w6) ∗
           ((roBase + 2300#64) ↦₆₄ᵣ w7) ∗
           ((roBase + 2308#64) ↦₃₂ᵣ w8)) ∗
          (A.pool ∗
           ((roBase + 2312#64) ↦ᵣ polysToBytes []) ∗
           memRegion (basisPtr + 816#64) 0 ∗
           ((fsp + 656#64) ↦₆₄ 34#64) ∗
           ((fsp + 672#64) ↦₆₄ 34#64) ∗
           stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        rw [hrw_eq, hro_eq, ProofLib.memRegion_zero]
        simp only [emp_sepConj, sepConj_emp]
        refine Entails.trans (sepConj_mono_left hpoly_i) ?_
        exact Entails.of_eq (by ac_rfl)
      | cons p' ps'' =>
        have hi2_lt : i + 1 + 1 < 35 := by simp at hi_len; omega
        have hcmp_end : ¬(BitVec.ofNat 64 (i + 1 + 1) == 35#64) = true := by
          simpa using ofNat_beq_ofNat_false (i + 1 + 1) 35 hi2_lt (by decide)
        have hro_eq := (hro68 (roBase + BitVec.ofNat 64 (68 * i))).symm
        have hrw_eq := (hrw68 (sf_1.readReg64 (Reg.gpr 0#5))).symm
        refine SepWPp.weaken_pre ?_
          (basis_n34_loop_sepWPp hA s0 fsp basisPtr roBase hfsp_align hbasis_mod R
            (p' :: ps'') (i + 1) (List.cons_ne_nil _ _) (by simp at hi_len ⊢; omega)
            (fun q hq => hall q (List.mem_cons_of_mem _ hq))
            _ (BitVec.ofNat 64 (i + 1))
            (((roBase + BitVec.ofNat 64 (68 * i)) ↦ᵣ gf16SliceBytes p.coefficients) ∗
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
              rw [show (68 * i : Nat) = 2 * 34 * i by omega,
                  polysToBytes_cons_ro roBase 34 i p (p' :: ps'') hp_len,
                  show (2 * 34 * i : Nat) = 68 * i by omega,
                  show (2 * 34 * (i + 1) : Nat) = 68 * (i + 1) by omega,
                  polyListOf_cons_off A basisPtr i p (p' :: ps'')]
              exact Entails.of_eq (by ac_rfl)))
        refine Entails.trans (Entails.of_eq (show _ =
          (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ 34#64) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
           (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 34#64) ∗
           A.live (sf_1.readReg64 (Reg.gpr 0#5)) 68 2 ∗
           (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ w0) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ w4) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ w5) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ w6) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ w7) ∗
            ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₃₂ w8))) ∗
          (((roBase + BitVec.ofNat 64 (68 * i)) ↦₆₄ᵣ w0) ∗
           (((roBase + BitVec.ofNat 64 (68 * i)) + 8#64) ↦₆₄ᵣ w1) ∗
           (((roBase + BitVec.ofNat 64 (68 * i)) + 16#64) ↦₆₄ᵣ w2) ∗
           (((roBase + BitVec.ofNat 64 (68 * i)) + 24#64) ↦₆₄ᵣ w3) ∗
           (((roBase + BitVec.ofNat 64 (68 * i)) + 32#64) ↦₆₄ᵣ w4) ∗
           (((roBase + BitVec.ofNat 64 (68 * i)) + 40#64) ↦₆₄ᵣ w5) ∗
           (((roBase + BitVec.ofNat 64 (68 * i)) + 48#64) ↦₆₄ᵣ w6) ∗
           (((roBase + BitVec.ofNat 64 (68 * i)) + 56#64) ↦₆₄ᵣ w7) ∗
           (((roBase + BitVec.ofNat 64 (68 * i)) + 64#64) ↦₃₂ᵣ w8)) ∗
          (A.pool ∗
           ((roBase + BitVec.ofNat 64 (68 * (i + 1))) ↦ᵣ polysToBytes (p' :: ps'')) ∗
           memRegion (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) (24 * (p' :: ps'').length) ∗
           ((fsp + 656#64) ↦₆₄ 34#64) ∗
           ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
           stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
        rw [hrw_eq, hro_eq]
        refine Entails.trans (sepConj_mono_left hpoly_i) ?_
        exact Entails.of_eq (by ac_rfl)

/-- `n = 34` constant basis case (`0x6a7f4 -> 0x6ac60..0x6ad18 -> 0x6ad1c..0x6adb4`, `+1136 -> +2608`). -/
theorem basis_n34_sepWPp {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64)
    {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 u656 u664 u672 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 34#64)
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
      s1.readReg64 .x25 = 34#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         completePointsPolys34At b ∗
         basisVecAt A basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_34) ∗
         A.live accPtr 68 2 ∗ memRegion accPtr 68 ∗
         ((fsp + 24#64) ↦₆₄ 34#64) ∗
         ((fsp + 96#64) ↦₆₄ 34#64) ∗
         ((fsp + 656#64) ↦₆₄ 34#64) ∗
         ((fsp + 664#64) ↦₆₄ basisPtr) ∗
         ((fsp + 672#64) ↦₆₄ 34#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       completePointsPolys34At b ∗
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
  have hpanic4868 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4868 b ext Q s0 s P R
  have hadrp : ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2304#64) &&&
      0xfffffffffffff000#64 = b + 0x65000#64 :=
    polyNextChunk_adrp_page hb 2304#64 rfl
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x470 24
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x634 8
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x8dc 64
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4868 hadrp hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 2288#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr1
    refine hpanic4868 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr1; exact htr1⟩
  · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨halign1, htr1⟩
    have hcond1 : ¬(sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
      simpa [beq_iff_eq] using hoom1
    have hsp_sf1 : sf_1.sp = fsp := by
      simp only [‹sf_1.sp = sf.sp›, h_1, hsp]
    apply SepWPp.of_sepWP (mid := entry + 2292#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) ?_
    rw [h_1, hsp]
    apply SepWPp.of_sepWP (mid := entry + 2372#64)
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    obtain ⟨_, hlen34, hall34⟩ := completePointsPolys34_spec
    have hne34 : extractCompletePolys COMPLETE_POINTS_POLYS_34 ≠ [] := by
      intro hnil; rw [hnil] at hlen34; contradiction
    have hro34 : completePointsPolys34At b =
        (((b + bv% (ls_bytes% "0100744059e124d3e459e459")) + BitVec.ofNat 64 (68 * 0)) ↦ᵣ
          polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_34)) := by
      unfold completePointsPolys34At completePointsPolys34Bytes
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    have hmem34 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 816 =
        memRegion ((sf_1.readReg64 (Reg.gpr 0#5)) + BitVec.ofNat 64 (24 * 0))
          (24 * (extractCompletePolys COMPLETE_POINTS_POLYS_34).length) := by
      rw [hlen34]; simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul]
    rw [hro34, hmem34]
    refine SepWPp.weaken_pre ?_
      (basis_n34_loop_sepWPp hA s0 fsp (sf_1.readReg64 (Reg.gpr 0#5)) (b + bv% (ls_bytes% "0100744059e124d3e459e459"))
        hfsp_align halign1 R
        (extractCompletePolys COMPLETE_POINTS_POLYS_34) 0 hne34
        (by rw [Nat.zero_add]; exact hlen34) hall34
        _ 0#64
        (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 816 8 ∗
         ((fsp + 24#64) ↦₆₄ u24) ∗
         ((fsp + 96#64) ↦₆₄ 34#64) ∗
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
              34 (by decide) (by decide) u24
              (((b + bv% (ls_bytes% "0100744059e124d3e459e459") + BitVec.ofNat 64 (68 * 0)) ↦ᵣ
                  polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_34)) ∗
               polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                 (extractCompletePolys COMPLETE_POINTS_POLYS_34) ∗
               A.live (sf_1.readReg64 (Reg.gpr 0#5)) 816 8 ∗
               ((fsp + 96#64) ↦₆₄ 34#64) ∗
               ((fsp + 672#64) ↦₆₄ 34#64) ∗ Frame) R
              hpc1 hrun1 hsp1 htr_s1
              (by rw [hx25_1]; simp only [wp_norm, h_18, h_8, hx25])
              (fun s2 accPtr hacc hpc2 hrun2 hsp2 htr2 hvregs_2 hx0_2 hx20_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => by
                have hbasis :
                    (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 816 8 ∗
                     polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                       (extractCompletePolys COMPLETE_POINTS_POLYS_34)) ⊢
                    basisVecAt A (sf_1.readReg64 (Reg.gpr 0#5)) (extractCompletePolys COMPLETE_POINTS_POLYS_34) := by
                  unfold basisVecAt
                  rw [hlen34]
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
                rw [← hro34]
                refine Entails.trans (Entails.of_eq (show _ =
                  (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 816 8 ∗
                   polyListOf A (sf_1.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (24 * 0))
                     (extractCompletePolys COMPLETE_POINTS_POLYS_34)) ∗
                  (A.pool ∗
                   completePointsPolys34At b ∗
                   A.live accPtr 68 2 ∗ memRegion accPtr 68 ∗
                   ((fsp + 24#64) ↦₆₄ 34#64) ∗
                   ((fsp + 96#64) ↦₆₄ 34#64) ∗
                   ((fsp + 656#64) ↦₆₄ 34#64) ∗
                   ((fsp + 664#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
                   ((fsp + 672#64) ↦₆₄ 34#64) ∗
                   stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
                refine Entails.trans (sepConj_mono_left hbasis) ?_
                exact Entails.of_eq (by ac_rfl)))
          exact Entails.of_eq (by ac_rfl)))
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.NextChunk
