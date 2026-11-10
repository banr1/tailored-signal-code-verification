/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallback
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst30
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Dynamic Lagrange Fallback Exit and Unified Positive Basis

**Checked by Lean.**

Verifies `lagrangeBasisExit_sepWPp` (`+4116 -> +2608`), the full dynamic fallback
`basis_fallback_sepWPp`, and the unified non-empty basis construction theorem `basis_pos_sepWPp`
(`+1136 -> +2608`) for all `0 < pts.length ≤ 0x0555555555555555`.
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
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
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

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two_fbe :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight_fbe :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one ofNat_succ_add_neg_one ofNat_add_one_eq_succ
  shl_one_ofNat_eq shl_one_ofNat_eq_nat

/-! ## 1. Pure & Memory Helper Lemmas -/

theorem toOnePts_ne_nil {pts : List Pt} (h : pts ≠ []) : toOnePts pts ≠ [] := by
  intro hnil
  have hlen : (toOnePts pts).length = 0 := by rw [hnil]; rfl
  rw [toOnePts_length] at hlen
  exact h (List.eq_nil_of_length_eq_zero hlen)

theorem lagrangeBasisTail_eq_lagrangeBasisFrom (ones : List Pt) :
    ∀ (k i : Nat), lagrangeBasisTail ones i k = lagrangeBasisFrom ones i k
  | 0, _ => rfl
  | k + 1, i => by
    simp [lagrangeBasisTail, lagrangeBasisFrom, lagrangeBasisTail_eq_lagrangeBasisFrom ones k (i + 1)]

theorem lagrangeBasisPure_length (ones : List Pt) :
    (lagrangeBasisPure ones).length = ones.length := by
  simp [lagrangeBasisPure]

theorem lagrangeBasisPure_mem_length (ones : List Pt) (p : Poly)
    (hp : p ∈ lagrangeBasisPure ones) :
    p.coefficients.length = ones.length := by
  rw [← lagrangeBasisFrom_zero_eq, ← lagrangeBasisTail_eq_lagrangeBasisFrom] at hp
  exact lagrangeBasisTail_mem_length ones ones.length 0 p hp

theorem ptAt_entails_memRegion (pt : Pt) (addr : BitVec 64) :
    ptAt pt addr ⊢ memRegion addr 4 := by
  unfold ptAt
  have h4 : (4 : Nat) = 2 + 2 := rfl
  rw [ProofLib.memRegion_split' (b := addr) (n := 2) (k := 2) (b' := addr + 2#64) h4 rfl (by decide),
      ProofLib.memRegion_two addr, ProofLib.memRegion_two (addr + 2#64)]
  exact sepConj_mono (Entails.sepExists_right pt.x.value (Entails.refl _))
    (Entails.sepExists_right pt.y.value (Entails.refl _))

theorem ptSliceAt_entails_memRegion (addr : BitVec 64) (pts : List Pt)
    (hbound : pts.length ≤ 0x0555555555555555) :
    ptSliceAt addr pts ⊢ memRegion addr (4 * pts.length) := by
  induction pts generalizing addr with
  | nil =>
    simp only [ptSliceAt, arrayAt, List.length_nil, Nat.mul_zero, ProofLib.memRegion_zero]
    exact Entails.refl _
  | cons pt rest ih =>
    have hrest : rest.length ≤ 0x0555555555555555 := by simp at hbound; omega
    have hsplit : memRegion addr (4 * (rest.length + 1)) =
        memRegion addr 4 ∗ memRegion (addr + 4#64) (4 * rest.length) :=
      ProofLib.memRegion_split' (b := addr) (n := 4) (k := 4 * rest.length) (b' := addr + 4#64)
        (by omega) rfl (by omega)
    rw [ptSliceAt_cons, List.length_cons, hsplit]
    exact sepConj_mono (ptAt_entails_memRegion pt addr) (ih (addr + 4#64) hrest)

theorem memRegion24_off_eq_polyHeader (base : BitVec 64) :
    memRegion (base + 656#64) 24 =
      ∃∗ u16 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        ((base + 656#64) ↦₆₄ u0) ∗ ((base + 664#64) ↦₆₄ u8) ∗ ((base + 672#64) ↦₆₄ u16) := by
  have h8 : (base + 656#64) + 8#64 = base + 664#64 := by bv_omega
  have h16 : (base + 656#64) + 16#64 = base + 672#64 := by bv_omega
  rw [memRegion_split_polyHeader (base + 656#64), h8, h16]

/-! ## 2. Dynamic Lagrange Basis Loop Entry/Exit (`0x6b398..0x6b4c8`, `+4116 -> +2608`) -/

/-- `0x6b398..0x6b4c8` (`+4116 -> +2608`): runs `lagrangeBasisLoop_sepWPp` on `toOnePts pts`,
    deallocates `xsPtr`, and allocates `accPtr` (`2 * pts.length` bytes, align 2). -/
theorem lagrangeBasisExit_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (fsp ptVecPtr xsPtr basisPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hxs_ne : xsPtr ≠ 0#64) (hbasis_ne : basisPtr ≠ 0#64)
    (u72 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4116#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = xsPtr)
    (hx21 : s.readReg64 .x21 = basisPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 accPtr u216' u224' u1040' u1048' u1056',
      accPtr ≠ 0#64 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2608#64 →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗
         basisVecAt A basisPtr (lagrangeBasisPure (toOnePts pts)) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 72#64) ↦₆₄ basisPtr) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       A.live xsPtr (4 * pts.length) 2 ∗ ptSliceAt xsPtr (toOnePts pts) ∗
       A.live basisPtr (24 * pts.length) 8 ∗ memRegion basisPtr (24 * pts.length) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn_pos : 0 < pts.length := List.length_pos_iff.mpr hpts_ne
  have hones_ne : toOnePts pts ≠ [] := toOnePts_ne_nil hpts_ne
  have hones_len : (toOnePts pts).length = pts.length := toOnePts_length pts
  have hones_bound : (toOnePts pts).length ≤ 0x0555555555555555 := by rw [hones_len]; exact hbound
  have hsum : 0 + ((toOnePts pts).length - 1 + 1) = (toOnePts pts).length := by rw [hones_len]; omega
  have h24_eq : 24 * ((toOnePts pts).length - 1 + 1) = 24 * (toOnePts pts).length := by rw [hones_len]; omega
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
  have hdealloc := hA.dealloc_ok_at polyNextChunkName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_dealloc")])
  simp only [rustDeallocSpec] at hdealloc
  have hpanic4796 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4796 b ext Q s0 s P R
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1014 12
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1110 56
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hdealloc hpanic4796 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 4128#64)
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  rw [← hones_len, ← h24_eq]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (lagrangeBasisLoop_sepWPp hA hb ((toOnePts pts).length - 1) 0 (toOnePts pts) hones_ne hones_bound hsum
      s0 _ fsp xsPtr basisPtr hfsp_align u216 u224 u1040 u1048 u1056
      (A.live xsPtr (4 * (toOnePts pts).length) 2 ∗
       A.live basisPtr (24 * (((toOnePts pts).length - 1) + 1)) 8 ∗
       ((fsp + 72#64) ↦₆₄ basisPtr) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ Frame) R
      (by rw [hentry]; wp_norm_goal)
      (by wp_norm_lhs)
      (by simp only [wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htrace])
      (by wp_norm_lhs)
      (by simp only [wp_norm, hx20])
      (by simp only [wp_norm, hx21])
      (by rw [hones_len]; wp_norm_lhs)
      (by simp only [wp_norm, hx29]) ?_)
  intro s1 u216' u224' u1040' u1048' u1056'
    hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
  rw [hentry] at hpc1
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
  apply SepWPp.of_sepWP (mid := entry + 4416#64)
  apply SepWP.fold hxs_mem (by sep_focus)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps; wp_apply
  refine SepWP.done hpc_sf_2 hrun_sf_2 ?_
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
    apply SepWPp.of_sepWP (mid := entry + 2608#64)
    wp_steps
    refine SepWP.done (by simp only [wp_norm, hcond_ne, hcond_oom, ↓reduceIte]) (by wp_norm_lhs) ?_
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
      (hcont _ (sf_2.readReg64 (Reg.gpr 0#5)) u216' u224' u1040' u1048' u1056' hoom
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
       reduceTableAt b ∗ tokenInitAt b ∗
       stackAt fsp allocHookStack ∗
       memRegion (fsp - 4304#64) (lagrangePrepareStack - allocHookStack) ∗
       Frame) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hbasis) ?_
    exact Entails.of_eq (by ac_rfl)

/-! ## 3. Full Dynamic Lagrange Fallback (`0x6a7f4 -> 0x6adb4`, `+1136 -> +2608`) -/

/-- Full dynamic Lagrange fallback (`0x6a7f4 -> 0x6aa90..0x6ab1c -> 0x6b398..0x6b4c8 -> 0x6adb4`,
    `+1136 -> +2608`) for `pts.length ∉ {0, 1, 3, 5, 30, 34, 36}`. -/
theorem basis_fallback_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (pts : List Pt) (hpts_ne : pts ≠ [])
    (hn1 : pts.length ≠ 1) (hn3 : pts.length ≠ 3) (hn5 : pts.length ≠ 5)
    (hn30 : pts.length ≠ 30) (hn34 : pts.length ≠ 34) (hn36 : pts.length ≠ 36)
    (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u72 u80 u96 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1136#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056',
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2608#64 →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗ ptSliceAt ptVecPtr pts ∗
         basisVecAt A basisPtr (lagrangeBasisPure (toOnePts pts)) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hn0 : pts.length ≠ 0 := by intro h0; exact hpts_ne (List.eq_nil_of_length_eq_zero h0)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (dispatch_fallback_sepWPp s0 s fsp hfsp_align pts.length hn0 hn1 hn3 hn5 hn30 hn34 hn36 hbound u96
      (A.pool ∗ ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTableAt b ∗ tokenInitAt b ∗ stackAt fsp lagrangePrepareStack ∗ Frame) R
      hpc hrun hsp htrace hx25 ?_)
  intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (allocXsAndBasis_sepWPp hA s0 s1 fsp ptVecPtr hfsp_align pts hpts_ne hbound u24 u80
      (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTableAt b ∗ tokenInitAt b ∗ Frame) R
      hpc1 hrun1 hsp1 htr1 hx19_1 (by rw [hx24_1, hx24]) (by rw [hx26_1, hx26]) ?_)
  intro s2 xsPtr basisPtr hxs_ne hbasis_ne _ hpc2 hrun2 hsp2 htr2 hvregs2
    hx20_2 hx21_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
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
         reduceTableAt b ∗ tokenInitAt b ∗ Frame) by ac_rfl)) ?_
      rw [← hst]
      exact Entails.of_eq (by ac_rfl))
    (lagrangeBasisExit_sepWPp hA hb pts hpts_ne hbound s0 s2 fsp ptVecPtr xsPtr basisPtr
      hfsp_align hxs_ne hbasis_ne u72 u216 u224 u1040 u1048 u1056
      (ptSliceAt ptVecPtr pts ∗ ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame) R
      hpc2 hrun2 hsp2 htr2 hx20_2 hx21_2 hx24_2 (by rw [hx29_2, hx29_1, hx29]) ?_)
  intro s3 accPtr u216' u224' u1040' u1048' u1056' hacc_ne
    hpc3 hrun3 hsp3 htr3 hvregs3 hx0_3 hx20_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s3 basisPtr accPtr basisPtr ptVecPtr u216' u224' u1040' u1048' u1056'
      hbasis_ne hacc_ne hpc3 hrun3 hsp3 htr3 (by rw [hvregs3, hvregs2, hvregs1]) hx0_3
      (by rw [hx20_3, hx25_2, hx20_1]) hx24_3 hx25_3 hx26_3
      (by rw [hx27_3, hx27_2, hx27_1]) (by rw [hx28_3, hx28_2, hx28_1]) hx29_3)

/-! ## 4. Unified Basis Construction for `0 < pts.length` (`basis_pos_sepWPp`) -/

/-- Pure basis polynomial list produced by `Poly.fromCompletePoints` for `pts`. -/
def completePointsBasisPure (pts : List Pt) : List Poly :=
  let n := pts.length
  if n == 0 then
    []
  else if n == 1 then
    extractCompletePolys COMPLETE_POINTS_POLYS_1
  else if n == 3 then
    extractCompletePolys COMPLETE_POINTS_POLYS_3
  else if n == 5 then
    extractCompletePolys COMPLETE_POINTS_POLYS_5
  else if n == 30 then
    extractCompletePolys COMPLETE_POINTS_POLYS_30
  else if n == 34 then
    extractCompletePolys COMPLETE_POINTS_POLYS_34
  else if n == 36 then
    extractCompletePolys COMPLETE_POINTS_POLYS_36
  else
    lagrangeBasisPure (toOnePts pts)

@[simp]
theorem completePointsBasisPure_length (pts : List Pt) :
    (completePointsBasisPure pts).length = pts.length := by
  unfold completePointsBasisPure
  dsimp only
  split
  · rename_i h0; exact (beq_iff_eq.mp h0).symm
  · split
    · rename_i _ h1; rw [completePointsPolys1_eq]; exact (beq_iff_eq.mp h1).symm
    · split
      · rename_i _ _ h3; rw [completePointsPolys3_eq]; exact (beq_iff_eq.mp h3).symm
      · split
        · rename_i _ _ _ h5; rw [completePointsPolys5_spec.2.1]; exact (beq_iff_eq.mp h5).symm
        · split
          · rename_i _ _ _ _ h30; rw [completePointsPolys30_spec.2.1]; exact (beq_iff_eq.mp h30).symm
          · split
            · rename_i _ _ _ _ _ h34; rw [completePointsPolys34_spec.2.1]; exact (beq_iff_eq.mp h34).symm
            · split
              · rename_i _ _ _ _ _ _ h36; rw [completePointsPolys36_spec.2.1]; exact (beq_iff_eq.mp h36).symm
              · rw [lagrangeBasisPure_length, toOnePts_length]

theorem completePointsBasisPure_mem_length (pts : List Pt) (p : Poly)
    (hp : p ∈ completePointsBasisPure pts) :
    p.coefficients.length = pts.length := by
  unfold completePointsBasisPure at hp
  dsimp only at hp
  split at hp
  · contradiction
  · split at hp
    · rename_i _ h1
      rw [beq_iff_eq.mp h1]
      rw [completePointsPolys1_eq] at hp
      simp [extractCompletePolys, constPolysToPolys, PolyConst.toPoly] at hp
      subst hp; rfl
    · split at hp
      · rename_i _ _ h3
        rw [beq_iff_eq.mp h3]
        rw [completePointsPolys3_eq] at hp
        simp [extractCompletePolys, constPolysToPolys, PolyConst.toPoly] at hp
        rcases hp with rfl | rfl | rfl <;> rfl
      · split at hp
        · rename_i _ _ _ h5
          rw [beq_iff_eq.mp h5]
          exact completePointsPolys5_spec.2.2 p hp
        · split at hp
          · rename_i _ _ _ _ h30
            rw [beq_iff_eq.mp h30]
            exact completePointsPolys30_spec.2.2 p hp
          · split at hp
            · rename_i _ _ _ _ _ h34
              rw [beq_iff_eq.mp h34]
              exact completePointsPolys34_spec.2.2 p hp
            · split at hp
              · rename_i _ _ _ _ _ _ h36
                rw [beq_iff_eq.mp h36]
                exact completePointsPolys36_spec.2.2 p hp
              · have h := lagrangeBasisPure_mem_length (toOnePts pts) p hp
                rwa [toOnePts_length] at h

theorem fromCompletePoints_eq_ok (pts : List Pt)
    (hcomplete : Poly.checkCompletePoints 0 pts = true)
    (hbound : pts.length ≤ 0x0555555555555555) :
    Poly.fromCompletePoints pts =
      .ok (.ok (Poly.lagrangeSum pts (completePointsBasisPure pts))) := by
  unfold Poly.fromCompletePoints completePointsBasisPure
  simp only [hcomplete, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  split
  · rfl
  · split
    · rw [completePointsPolys1_eq]; rfl
    · split
      · rw [completePointsPolys3_eq]; rfl
      · split
        · obtain ⟨⟨cps, heq, _⟩, _⟩ := completePointsPolys5_spec
          rw [heq]; rfl
        · split
          · obtain ⟨⟨cps, heq, _⟩, _⟩ := completePointsPolys30_spec
            rw [heq]; rfl
          · split
            · obtain ⟨⟨cps, heq, _⟩, _⟩ := completePointsPolys34_spec
              rw [heq]; rfl
            · split
              · obtain ⟨⟨cps, heq, _⟩, _⟩ := completePointsPolys36_spec
                rw [heq]; rfl
              · have hones_def :
                    List.map (fun pt : Pt => ({ x := pt.x, y := GF16.ONE } : Pt)) pts =
                      toOnePts pts := rfl
                have hlen : pts.length = (toOnePts pts).length := (toOnePts_length pts).symm
                have hub : (toOnePts pts).length + 1 ≤ USIZE_MAX := by
                  rw [toOnePts_length]; unfold USIZE_MAX; omega
                rw [hones_def, hlen, mapM_range_lagrangeInterpolatePt_eq_ok (toOnePts pts) hub,
                    lagrangeBasisTail_eq_lagrangeBasisFrom, lagrangeBasisFrom_zero_eq]

/-- Unified basis construction (`0x6a7f4 -> 0x6adb4`, `+1136 -> +2608`) for all
    `pts ≠ []` with `pts.length ≤ 0x0555555555555555`. -/
theorem basis_pos_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64)
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u72 u80 u96 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 1136#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056',
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 2608#64 →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool ∗ ptSliceAt ptVecPtr pts ∗
         basisVecAt A basisPtr (completePointsBasisPure pts) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗ ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  by_cases hn1 : pts.length = 1
  · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_1 := by
      unfold completePointsBasisPure; simp [hn1]
    rw [stackAt_lagrangePrepare_split_alloc fsp]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (basis_n1_sepWPp hA s0 s fsp hfsp_align u24 u96
        (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗
         ptSliceAt ptVecPtr pts ∗
         ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗ Frame) R
        hpc hrun hsp htrace (by rw [hx25, hn1]) ?_)
    intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
      hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    refine SepWPp.weaken_pre
      (by
        rw [hbasis_eq, hn1, stackAt_lagrangePrepare_split_alloc fsp]
        exact Entails.of_eq (by ac_rfl))
      (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
        hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
        (by rw [hx25_1, hn1]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
  · by_cases hn3 : pts.length = 3
    · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_3 := by
        unfold completePointsBasisPure; simp [hn3]
      rw [stackAt_lagrangePrepare_split_alloc fsp]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (basis_n3_sepWPp hA s0 s fsp hfsp_align u24 u96
          (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
             (lagrangePrepareStack - allocHookStack) ∗
           ptSliceAt ptVecPtr pts ∗
           ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
           ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
           memRegion (fsp + 656#64) 24 ∗
           ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
           completePointsPolysAt b ∗ reduceTableAt b ∗ tokenInitAt b ∗ Frame) R
          hpc hrun hsp htrace (by rw [hx25, hn3]) ?_)
      intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
        hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      refine SepWPp.weaken_pre
        (by
          rw [hbasis_eq, hn3, stackAt_lagrangePrepare_split_alloc fsp]
          exact Entails.of_eq (by ac_rfl))
        (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
          hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
          (by rw [hx25_1, hn3]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
    · by_cases hn5 : pts.length = 5
      · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_5 := by
          unfold completePointsBasisPure; simp [hn5]
        unfold completePointsPolysAt
        rw [stackAt_lagrangePrepare_split_alloc fsp]
        refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
          (basis_n5_sepWPp hb hA s0 s fsp hfsp_align u24 u96
            (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
               (lagrangePrepareStack - allocHookStack) ∗
             ptSliceAt ptVecPtr pts ∗
             ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
             ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
             memRegion (fsp + 656#64) 24 ∗
             ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
             completePointsPolys30At b ∗ completePointsPolys34At b ∗ completePointsPolys36At b ∗
             reduceTableAt b ∗ tokenInitAt b ∗ Frame) R
            hpc hrun hsp htrace (by rw [hx25, hn5]) ?_)
        intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
          hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
        refine SepWPp.weaken_pre
          (by
            unfold completePointsPolysAt
            rw [hbasis_eq, hn5, stackAt_lagrangePrepare_split_alloc fsp]
            exact Entails.of_eq (by ac_rfl))
          (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
            hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
            (by rw [hx25_1, hn5]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
      · by_cases hn30 : pts.length = 30
        · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_30 := by
            unfold completePointsBasisPure; simp [hn30]
          unfold completePointsPolysAt
          rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWPp.exists_elim; intro u672
          apply SepWPp.exists_elim; intro u664
          apply SepWPp.exists_elim; intro u656
          refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (basis_n30_sepWPp hb hA s0 s fsp hfsp_align u24 u96 u656 u664 u672
              (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                 (lagrangePrepareStack - allocHookStack) ∗
               ptSliceAt ptVecPtr pts ∗
               ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
               ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
               ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
               completePointsPolys5At b ∗ completePointsPolys34At b ∗ completePointsPolys36At b ∗
               reduceTableAt b ∗ tokenInitAt b ∗ Frame) R
              hpc hrun hsp htrace (by rw [hx25, hn30]) ?_)
          intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
            hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
          refine SepWPp.weaken_pre
            (by
              unfold completePointsPolysAt
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
                 (completePointsPolys5At b ∗ completePointsPolys30At b ∗
                  completePointsPolys34At b ∗ completePointsPolys36At b) ∗
                 reduceTableAt b ∗ tokenInitAt b ∗
                 (stackAt fsp allocHookStack ∗
                  memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                    (lagrangePrepareStack - allocHookStack)) ∗ Frame) by ac_rfl)) ?_
              refine Entails.trans (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 30#64 basisPtr 30#64)) ?_
              exact Entails.of_eq (by ac_rfl))
            (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
              hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
              (by rw [hx25_1, hn30]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
        · by_cases hn34 : pts.length = 34
          · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_34 := by
              unfold completePointsBasisPure; simp [hn34]
            unfold completePointsPolysAt
            rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWPp.exists_elim; intro u672
            apply SepWPp.exists_elim; intro u664
            apply SepWPp.exists_elim; intro u656
            refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
              (basis_n34_sepWPp hb hA s0 s fsp hfsp_align u24 u96 u656 u664 u672
                (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                   (lagrangePrepareStack - allocHookStack) ∗
                 ptSliceAt ptVecPtr pts ∗
                 ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                 ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                 ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
                 completePointsPolys5At b ∗ completePointsPolys30At b ∗ completePointsPolys36At b ∗
                 reduceTableAt b ∗ tokenInitAt b ∗ Frame) R
                hpc hrun hsp htrace (by rw [hx25, hn34]) ?_)
            intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
              hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
            refine SepWPp.weaken_pre
              (by
                unfold completePointsPolysAt
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
                   (completePointsPolys5At b ∗ completePointsPolys30At b ∗
                    completePointsPolys34At b ∗ completePointsPolys36At b) ∗
                   reduceTableAt b ∗ tokenInitAt b ∗
                   (stackAt fsp allocHookStack ∗
                    memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                      (lagrangePrepareStack - allocHookStack)) ∗ Frame) by ac_rfl)) ?_
                refine Entails.trans (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 34#64 basisPtr 34#64)) ?_
                exact Entails.of_eq (by ac_rfl))
              (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
                hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
                (by rw [hx25_1, hn34]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
          · by_cases hn36 : pts.length = 36
            · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_36 := by
                unfold completePointsBasisPure; simp [hn36]
              unfold completePointsPolysAt
              rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWPp.exists_elim; intro u672
              apply SepWPp.exists_elim; intro u664
              apply SepWPp.exists_elim; intro u656
              refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
                (basis_n36_sepWPp hb hA s0 s fsp hfsp_align u24 u96 u656 u664 u672
                  (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                     (lagrangePrepareStack - allocHookStack) ∗
                   ptSliceAt ptVecPtr pts ∗
                   ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                   ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                   ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗ ((fsp + 1056#64) ↦₆₄ u1056) ∗
                   completePointsPolys5At b ∗ completePointsPolys30At b ∗ completePointsPolys34At b ∗
                   reduceTableAt b ∗ tokenInitAt b ∗ Frame) R
                  hpc hrun hsp htrace (by rw [hx25, hn36]) ?_)
              intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
              refine SepWPp.weaken_pre
                (by
                  unfold completePointsPolysAt
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
                     (completePointsPolys5At b ∗ completePointsPolys30At b ∗
                      completePointsPolys34At b ∗ completePointsPolys36At b) ∗
                     reduceTableAt b ∗ tokenInitAt b ∗
                     (stackAt fsp allocHookStack ∗
                      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                        (lagrangePrepareStack - allocHookStack)) ∗ Frame) by ac_rfl)) ?_
                  refine Entails.trans (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 36#64 basisPtr 36#64)) ?_
                  exact Entails.of_eq (by ac_rfl))
                (hcont s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
                  hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
                  (by rw [hx25_1, hn36]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
            · have hn0 : pts.length ≠ 0 := by intro h0; exact hpts_ne (List.eq_nil_of_length_eq_zero h0)
              have hbasis_eq : completePointsBasisPure pts = lagrangeBasisPure (toOnePts pts) := by
                unfold completePointsBasisPure; simp [hn0, hn1, hn3, hn5, hn30, hn34, hn36]
              refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
                (basis_fallback_sepWPp hA hb pts hpts_ne hn1 hn3 hn5 hn30 hn34 hn36 hbound
                  s0 s fsp ptVecPtr hfsp_align u24 u72 u80 u96 u216 u224 u1040 u1048 u1056
                  (completePointsPolysAt b ∗ Frame) R
                  hpc hrun hsp htrace hx24 hx25 hx26 hx29 ?_)
              intro s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056'
                hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
              refine SepWPp.weaken_pre
                (by rw [hbasis_eq]; exact Entails.of_eq (by ac_rfl))
                (hcont s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056'
                  hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                  hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1)

end CryptoVerification.SpqrV1.Poly.NextChunk
