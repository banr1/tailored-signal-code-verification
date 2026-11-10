/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.PhaseBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Proof for `<spqr::encoding::polynomial::Poly>::compute_at`

Proves `computeAt_placed_ok` on Block `371` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.ProofBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_371 blkPC_371 blkPl_371
   lscall_blk_cl lsmpl lsρ sepWP_seq_lscl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.SpqrV1.Alloc
  (growOneStack spqrHandleErrorSym spqrRustAllocSym
   spqrRustNoAllocShimSym spqrRustReallocSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (tokenInitPlacedAt zeroExtend_16_truncate_32_64)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (ComputeAtArgs computeAtPure computeAtStack ge2_to_61974_rearrange
   grow0_post_rearrange len_bit62_false memRegion_ge2_split merge_allocHook_after_alloc
   ofNat_beq_false_of_lt ofNat_shl_one ofNat_shl_one_bv ofNat_two_mul_toNat
   readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sepWPp_seq_lscl
   sp_setMem_pre spqrRustDeallocSym stackAt_computeAt_split stackAt_growOne_eq_allocHook
   subs_succ_one_ne_zero truncate16_zext64_trunc32 zext16_xor_trunc32)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (aligned16_add_mul_two and_one_of_mod_two
   readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget
   RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
   rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   rustDeallocEvents rustReallocEvents subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
  (computeAtAllocEvents computeAtEvents computeAtPlacedSpec computeAtScratchCap
   grow0_pre_split grow1_pre_split growOneGF16OneSpec growOneGF16ZeroSpec
   grow_one_gf16_one_placed_ok grow_one_gf16_zero_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.PhaseBudget
  (call_noPanic_to_sepWP_lscl from_61974_cap4_placed_sepWP from_61974_ge2_placed_sepWP)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

private theorem trace_of_acp {s1 s2 : State} (h : AllocCallPreserved s1 s2) :
    s2.trace = s1.trace :=
  h.2.1

private theorem eq_trans_assump {α : Type} {a b c : α} (h1 : a = b) (h2 : b = c) : a = c :=
  h1.trans h2

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  ofNat_shl_one ofNat_shl_one_bv truncate16_zext64_trunc32 zext16_xor_trunc32
  Arm64.Obj.pageOf_add_lo12Of
attribute [local simp] growOneGF16ZeroSpec growOneGF16OneSpec

set_option hygiene false in
local macro "wp_steps_n_rw_pool " n:num mid:term:max stTerm:term:max : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_371).rebase (blkPl_371).base (hooksException (Rust.withPanics ext)))
    blkLib_eq_371 (mid := $mid)
  intro _m_strip
  wp_steps $n
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have _hp := (A.pool_transport lim $stTerm _ _
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))).symm
  wp_conv_pre => rw [_hp]
  clear _hp))

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `371`) -/

set_option maxHeartbeats 1600000 in
theorem computeAt_placed_ok [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hrealloc_sat : HookSat (Rust.withPanics ext) spqrRustReallocSym
      (rustCliReallocBudgetSpec M A lim))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (blkPl_371).base
      (withLsCodeLoaded lsmpl (computeAtPlacedSpec M A lim)) := by
  have hshim :
      subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
        (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
    spqr_hook_ok_of_mem hshim_sat
  have halloc :
      subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
        (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (spqr_hook_ok_of_mem halloc_sat)
  have hdealloc :
      subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
        (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem hdealloc_sat
  dsimp only [rustCliAllocNoOomSpec, RustLayoutOk, LayoutOk, ↓reduceIte] at halloc
  simp only [withLsCodeLoaded, computeAtPlacedSpec]
  wpp_init g s0
  rcases g with ⟨a, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0_init : s0.readReg64 (Reg.gpr 0#5) = a.p_coeffs := by assumption
  have hx1_init : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 a.poly.coefficients.length := by
    assumption
  have hx2_init : BitVec.truncate 16 (s0.readReg64 (Reg.gpr 2#5)) = a.x.value := by assumption
  have hbound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63 := by omega
  have hfits : FitsEvents M lim st (computeAtAllocEvents a.poly.coefficients.length) := by
    assumption
  have hsp0 : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_align
  by_cases hnil : a.poly.coefficients = []
  · -- Empty polynomial (`a.poly.coefficients = []`)
    have hx1_0 : (BitVec.ofNat 64 a.poly.coefficients.length == 0#64) = true := by
      rw [hnil]; rfl
    have hfits0 : FitsEvents M lim st (rustAllocEvents 8 2) := by
      simpa [computeAtAllocEvents, hnil] using hfits
    apply sepWPp_seq_lscl hcl0 (mid := lsmpl.base 359)
    wp_simp_pre only [stackAt_computeAt_split s0.sp]
    wp_pull_exists
    wp_steps_n_rw_pool 17 (lsmpl.base 359) st
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_pre_g0
    have hgrow0 := lscall_blk_cl
      (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (grow_one_gf16_zero_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat) hcl_pre_g0
    let st1 : M.σ := M.stepEvents (rustAllocEvents 8 2) st
    apply call_noPanic_to_sepWP_lscl hcl_pre_g0 hgrow0
      (x := (s0.sp - 136#64, st))
      (ret_pc := (blkPl_371).base + 696#64)
      (φ := FitsEvents M lim st (rustAllocEvents 8 2))
      (T := ((s0.sp - 136#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 136#64 + 8#64) ↦₆₄ 2#64) ∗
            A.pool lim st _ ∗
            stackAt (s0.sp - 144#64) growOneStack)
    · wp_norm_lhs
    · wp_norm_lhs
    · simp only [State.spAligned, arm64_norm, wp_norm, beq_iff_eq]
      revert hsp0; bv_bits
    · wp_norm_lhs
    · dsimp only [growOneGF16ZeroSpec]
      simp only [arm64_norm, wp_norm]
      rfl
    · exact hfits0
    · exact grow0_pre_split s0.sp _ _ _ _ _ _ _
    · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
    · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
    · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
    · intro sf_g hcl_g hpc_g hrun_g hsp_g hcs_g
      wp_simp_pre only [growOneGF16ZeroSpec, sepConj_assoc, sepExists_sepConj_left,
        sepExists_sepConj_right]
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
      wp_steps_n_rw_pool 6 ((blkPl_371).base + 96#64) st1
      simp only [State.setMem_setMem]
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      intro hcl_974
      have hevs0 :
          M.stepEvents (rustDeallocEvents 8 2) st1 =
            M.stepEvents (computeAtEvents a.poly.coefficients.length) st := by
        simp [st1, computeAtEvents, computeAtAllocEvents, computeAtScratchCap, hnil,
          ← M.stepEvents_append]
      refine SepWP.mono (from_61974_cap4_placed_sepWP M A lim st1 ext hdealloc a R s0 _
        (by simp [hnil]) v0_1 hp'_ne hp'_al v1_1 1#64 hsp0
        (by exact hcl_974)
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hsp_g')
        (by simpa [arm64_norm, wp_norm] using htr_g)
        (by simpa [arm64_norm, wp_norm] using hcs_g.2.2.2.2.2.2.2.2.2.2.2)
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm, hx0_init] using hcs_g.1)
        (by simpa [arm64_norm, wp_norm, hx1_init, hnil] using hcs_g.2.1)
        (by
          have hx21 := hcs_g.2.2.1
          simp only [arm64_norm, wp_norm] at hx21 ⊢
          rw [hx21]
          simpa [arm64_norm, wp_norm] using hx2_init))
        fun sf1 P_f _ _ ⟨himp, hsp1, hcs1⟩ => ⟨fun hm => ?_, hsp1, hcs1⟩
      have hq := himp hm
      rw [hevs0] at hq
      simp only [satisfies_pure_sepConj] at hq ⊢
      exact ⟨⟨hq.1.1, hq.1.2.1⟩, hq.2⟩
  · -- Non-empty polynomial (`a.poly.coefficients ≠ []`)
    have hlen_pos : 0 < a.poly.coefficients.length := List.length_pos_iff.mpr hnil
    rcases ofNat_beq_false_of_lt hlen_pos (by omega) with ⟨_, _, hx1_ne0, _⟩
    have hbit62 :
        ((BitVec.ofNat 64 a.poly.coefficients.length &&& 4611686018427387904#64) != 0#64) =
          false :=
      len_bit62_false a.poly.coefficients.length (by omega)
    have htoNat_2len :
        (BitVec.ofNat 64 (2 * a.poly.coefficients.length)).toNat =
          2 * a.poly.coefficients.length :=
      ofNat_two_mul_toNat a.poly.coefficients.length (by omega)
    have hpow2 : ∃ k, 2 = 2 ^ k := ⟨1, rfl⟩
    have hpos_2len : 0 < 2 * a.poly.coefficients.length := by omega
    have hal_2 : (2 : Nat) ≤ 2 ^ 31 := by decide
    have hfits_alloc :
        FitsEvents M lim st (rustAllocEvents (2 * a.poly.coefficients.length) 2) := by
      by_cases h1 : a.poly.coefficients.length = 1
      · simp only [computeAtAllocEvents, h1, show (1 : Nat) = 0 ↔ False by decide,
          ↓reduceIte] at hfits
        rw [h1]
        exact ((fitsEvents_append M lim _ _ st).mp hfits).1
      · have h0 : a.poly.coefficients.length ≠ 0 := by omega
        simpa [computeAtAllocEvents, h0, h1] using hfits
    apply sepWPp_seq_lscl hcl0 (mid := (blkPl_371).base + 68#64)
    wp_simp_pre only [stackAt_computeAt_split s0.sp,
      stackAt_growOne_eq_allocHook (s0.sp - 144#64)]
    wp_pull_exists
    wp_steps_n_rw_pool 14 (lsρ spqrRustNoAllocShimSym) st
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have htr_sf0 : sf.trace = s0.trace := ‹_›
    have hsp_sf0 : sf.sp = s0.sp - 144#64 := ‹_›
    have hx19_0 : sf.readReg64 (Reg.gpr 19#5) = a.p_coeffs := ‹_›
    have hx20_0 : sf.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 a.poly.coefficients.length := ‹_›
    have hx21_0 : sf.readReg64 (Reg.gpr 21#5) =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) := ‹_›
    have hvregs_sf0 : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      simpa [arm64_norm, wp_norm] using hvregs
    rw [← A.pool_of_vmPreserved ‹_›]
    wp_steps_n_rw_pool 3 (lsρ spqrRustAllocSym) st
    simp only [State.setMem_setMem]
    wp_call halloc (2 * a.poly.coefficients.length, 2, st)
    let st1 : M.σ := M.stepEvents (rustAllocEvents (2 * a.poly.coefficients.length) 2) st
    apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
    intro hcl_sf1
    have hptr0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹_›
    have hptr_mod : (sf_1.readReg64 (Reg.gpr 0#5)).toNat % 2 = 0 := ‹_›
    have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
    have hp0_al : sf_1.readReg64 (Reg.gpr 0#5) &&& 1#64 = 0#64 :=
      and_one_of_mod_two hptr_mod
    have hal_p0 : MemWidth.isAligned .W16 (sf_1.readReg64 (Reg.gpr 0#5)) = true := by
      simpa using aligned16_add_mul_two (sf_1.readReg64 (Reg.gpr 0#5)) hp0_al 0
    have hsp_sf1 : sf_1.sp = s0.sp - 144#64 :=
      eq_trans_assump ‹_› (by simp [arm64_norm, wp_norm, hsp_sf0])
    have hx19_1 : sf_1.readReg64 (Reg.gpr 19#5) = a.p_coeffs :=
      eq_trans_assump ‹_› (by simp [arm64_norm, wp_norm, hx19_0])
    have hx20_1' : sf_1.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 a.poly.coefficients.length :=
      eq_trans_assump ‹_› (by simp [arm64_norm, wp_norm, hx20_0])
    have hx21_1 : sf_1.readReg64 (Reg.gpr 21#5) =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) :=
      eq_trans_assump ‹_› (by simp [arm64_norm, wp_norm, hx21_0])
    have hsp_sf1_al : (sf_1.sp &&& 15#64 == 0#64) = true := by
      rw [hsp_sf1, beq_iff_eq]; revert hsp0; bv_bits
    have htr_sf1 : sf_1.trace = s0.trace := by
      have ht1 := trace_of_acp (s2 := sf_1) ‹_›
      simpa [arm64_norm, wp_norm, htr_sf0] using ht1
    have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := by
      simpa [arm64_norm, wp_norm, hvregs_sf0] using hvregs_1
    wp_conv_pre =>
      simp only [arm64_norm, wp_norm, hsp_sf0]
      rw [← sepConj_assoc (A.live _ _ _) (memRegion _ _) _, merge_allocHook_after_alloc s0.sp]
    by_cases hlen1 : a.poly.coefficients.length = 1
    · -- `a.poly.coefficients.length = 1` (calls `grow_one` at +0x2d4)
      have hx20_1 : (BitVec.ofNat 64 a.poly.coefficients.length == 1#64) = true := by
        rw [hlen1]; rfl
      have hsub_1 : (BitVec.ofNat 64 a.poly.coefficients.length - 1#64 == 0#64) = true := by
        rw [hlen1]; rfl
      have hfits_realloc : FitsEvents M lim st1 (rustReallocEvents 2 8 2) := by
        have hf := hfits
        simp only [computeAtAllocEvents, hlen1, show (1 : Nat) = 0 ↔ False by decide,
          ↓reduceIte] at hf
        simpa [st1, hlen1] using ((fitsEvents_append M lim _ _ st).mp hf).2
      have hmem2 :
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * a.poly.coefficients.length) =
            ∃∗ w0 : BitVec 16, (sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ w0 := by
        rw [hlen1, Nat.mul_one, ProofLib.memRegion_two]
      have hst1_2 : M.stepEvents (rustAllocEvents 2 2) st = st1 := by
        dsimp [st1]; rw [hlen1]
      apply sepWPp_seq_lscl hcl_sf1 (mid := lsmpl.base 359)
      wp_conv_pre =>
        rw [hmem2, hlen1, show 2 * 1 = 2 from rfl, hst1_2]
      wp_pull_exists
      wp_steps_n_rw_pool 9 (lsmpl.base 359) st1
      simp only [State.setMem_setMem]
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      intro hcl_pre_g1
      have hgrow1 := lscall_blk_cl
        (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
        (grow_one_gf16_one_placed_ok h_panic hshim_sat halloc_sat hrealloc_sat) hcl_pre_g1
      let st2 : M.σ := M.stepEvents (rustReallocEvents 2 8 2) st1
      apply call_noPanic_to_sepWP_lscl hcl_pre_g1 hgrow1
        (x := ((s0.sp - 136#64, sf_1.readReg64 (Reg.gpr 0#5)), st1))
        (ret_pc := (blkPl_371).base + 728#64)
        (φ := sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 ∧
          FitsEvents M lim st1 (rustReallocEvents 2 8 2))
        (T := ((s0.sp - 136#64) ↦₆₄ 1#64) ∗
              ((s0.sp - 136#64 + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
              A.live (sf_1.readReg64 (Reg.gpr 0#5)) 2 2 ∗
              ((sf_1.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16) ∗
              A.pool lim st1 _ ∗
              stackAt (s0.sp - 144#64) growOneStack)
      · wp_norm_lhs
      · wp_norm_lhs
      · simp only [State.spAligned, arm64_norm, wp_norm, hsp_sf1_al]
      · wp_norm_lhs
      · dsimp only [growOneGF16OneSpec]
        simp only [arm64_norm, wp_norm, hsp_sf1]
        rfl
      · exact ⟨hptr0, hfits_realloc⟩
      · exact grow1_pre_split s0.sp (sf_1.readReg64 (Reg.gpr 0#5)) _ _ _ _ _ _ _ _ _ _
      · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
      · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
      · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
      · intro sf_g hcl_g hpc_g hrun_g hsp_g hcs_g
        wp_simp_pre only [growOneGF16OneSpec, sepConj_assoc, sepExists_sepConj_left,
          sepExists_sepConj_right]
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
        apply sepWP_seq_lscl (by exact hcl_g) (mid := (blkPl_371).base + 96#64)
        wp_steps_n_rw_pool 2 ((blkPl_371).base + 96#64) st2
        simp only [State.setMem_setMem]
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        intro hcl_974
        have hevs1 :
            M.stepEvents (rustDeallocEvents 8 2) st2 =
              M.stepEvents (computeAtEvents a.poly.coefficients.length) st := by
          simp [st2, st1, computeAtEvents, computeAtAllocEvents, computeAtScratchCap, hlen1,
            ← M.stepEvents_append]
        refine SepWP.mono (from_61974_cap4_placed_sepWP M A lim st2 ext hdealloc a R s0 _
          (by omega) v0_2 hp'_ne hp'_al v1_1 1#64 hsp0
          (by exact hcl_974)
          (by wp_norm_lhs)
          (by wp_norm_lhs)
          (by simpa [arm64_norm, wp_norm] using hsp_g')
          (by
            have htr_g' : sf_g.trace = sf_1.trace := by simpa [arm64_norm, wp_norm] using htr_g
            simpa [arm64_norm, wp_norm, htr_sf1] using htr_g')
          (by
            have hv_g := hcs_g.2.2.2.2.2.2.2.2.2.2.2
            simp only [arm64_norm, wp_norm] at hv_g ⊢
            rw [hv_g]; exact hvregs_sf1)
          (by wp_norm_lhs)
          (by
            have hx19 := hcs_g.1
            simp only [arm64_norm, wp_norm] at hx19 ⊢
            rw [hx19, hx19_1])
          (by
            have hx20 := hcs_g.2.1
            simp only [arm64_norm, wp_norm] at hx20 ⊢
            rw [hx20, hx20_1'])
          (by
            have hx21 := hcs_g.2.2.1
            simp only [arm64_norm, wp_norm] at hx21 ⊢
            rw [hx21, hx21_1]
            simpa [arm64_norm, wp_norm] using hx2_init))
          fun sf1 P_f _ _ ⟨himp, hsp1, hcs1⟩ => ⟨fun hm => ?_, hsp1, hcs1⟩
        have hq := himp hm
        rw [hevs1] at hq
        simp only [satisfies_pure_sepConj] at hq ⊢
        exact ⟨⟨hq.1.1, hq.1.2.1⟩, hq.2⟩
    · -- `2 ≤ a.poly.coefficients.length` (falls through to +0x60)
      have hlen_ge2 : 2 ≤ a.poly.coefficients.length := by omega
      rcases subs_succ_one_ne_zero (r := a.poly.coefficients.length - 2) (by omega) with
        ⟨hsub1_ne0, hlen_ne1⟩
      rw [show a.poly.coefficients.length - 2 + 1 + 1 = a.poly.coefficients.length by omega]
        at hsub1_ne0 hlen_ne1
      apply SepWPp.of_sepWP_ret
      wp_conv_pre =>
        rw [memRegion_ge2_split (sf_1.readReg64 (Reg.gpr 0#5)) a.poly.coefficients.length
              hlen_ge2 (by omega),
            sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
      wp_pull_exists
      apply sepWP_seq_lscl (by exact hcl_sf1) (mid := (blkPl_371).base + 96#64)
      wp_steps_n_rw_pool 7 ((blkPl_371).base + 96#64) st1
      simp only [State.setMem_setMem]
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      intro hcl_974
      wp_conv_pre => rw [ge2_to_61974_rearrange]
      have hevs_ge2 :
          M.stepEvents (rustDeallocEvents (2 * a.poly.coefficients.length) 2) st1 =
            M.stepEvents (computeAtEvents a.poly.coefficients.length) st := by
        have h0 : a.poly.coefficients.length ≠ 0 := by omega
        have hle1 : ¬ a.poly.coefficients.length ≤ 1 := by omega
        simp [st1, computeAtEvents, computeAtAllocEvents, computeAtScratchCap, h0, hlen1, hle1,
          ← M.stepEvents_append]
      refine SepWP.mono (from_61974_ge2_placed_sepWP M A lim st1 ext hdealloc a R s0 _
        hlen_ge2 (by omega) (sf_1.readReg64 (Reg.gpr 0#5)) hptr0 hp0_al _ 1#64 hsp0
        (by exact hcl_974)
        (by wp_norm_lhs)
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hsp_sf1)
        (by simpa [arm64_norm, wp_norm] using htr_sf1)
        (by simpa [arm64_norm, wp_norm] using hvregs_sf1)
        (by wp_norm_lhs)
        (by simpa [arm64_norm, wp_norm] using hx19_1)
        (by simpa [arm64_norm, wp_norm] using hx20_1')
        (by
          simp only [arm64_norm, wp_norm]
          rw [hx21_1]
          simpa [arm64_norm, wp_norm] using hx2_init))
        fun sf1 P_f _ _ ⟨himp, hsp1, hcs1⟩ => ⟨fun hm => ?_, hsp1, hcs1⟩
      have hq := himp hm
      rw [hevs_ge2] at hq
      simp only [satisfies_pure_sepConj] at hq ⊢
      exact ⟨⟨hq.1.1, hq.1.2.1⟩, hq.2⟩

end LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.ProofBudget
