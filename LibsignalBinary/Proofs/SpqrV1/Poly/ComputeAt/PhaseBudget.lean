/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Phase
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Phase Composition for `<spqr::encoding::polynomial::Poly>::compute_at`

Threads `RustCliAllocBudget M` and `VmPreserved` through the power-table phase, dot-product phase,
and `__rust_dealloc` epilogue on Block `371`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.PhaseBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_371 blkPC_371 blkPC_371_rebase_fetch_0xfc
   blkPC_371_rebase_fetch_0x1e0 blkPC_384 blkPl_371 blkPl_384 lscall_blk lsmpl lsρ sepWP_seq_lscl
   withMemEq)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (GF16 tokenName tokenStorageName)
open CryptoVerification.LibsignalSpqrV1.reduce (reduceByteEntry)
open CryptoVerification.LibsignalSpqrV1.unaccelerated (mul polyMul)
open CryptoVerification.SpqrV1.Alloc (growOneStack)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (aligned_tokenOnce_placed step_ldar32 tokenInitPlacedAt tokenInitPlacedAt_fold
   zeroExtend_16_truncate_32_64)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (polyMul_asm_eq polyReduce_asm_eq reduceTablePlacedAt reduceTablePlacedAt_focus16
   uxtw1_idx1_eq uxtw1_idx2_eq sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre
   readReg64_setMem_setPC_pre readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre
   readReg_setMem_setPC_pre)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (aligned16_add_mul_two)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (ComputeAtArgs combine_two_gf16 computeAtPowersPure computeAtPowersPure_length computeAtPure
   computeAtPure_eq_dotLoopPure computeAtPure_nil computeAtStack dotLoopPure dotLoopPure_succ
   eor_gf16_add_comm gf16Slice2_rest4_entails_memRegion8 gf16SliceAt_append_singleton_assoc
   gf16SliceAt_entails_memRegion insert_emp_memRegion_after_w1 memRegion_two_succ ofNat_add_ofNat
   ofNat_add_one ofNat_and_one ofNat_beq_false_of_lt ofNat_shl_one ofNat_shl_one_bv
   ofNat_sub_one_succ ofNat_two_mul_toNat ofNat_ule_false_of_lt ofNat_ushr_one ofNat_ushr_one_bv
   powersLoopPure powersLoopPure_succ powers_to_dot_frame powers_to_dot_ge2_frame ptr_add_two_step
   readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre spqrRustDeallocSym
   stackAt_computeAt_merge stackAt_growOne_eq_allocHook stackAt_growOne_merge_allocHook
   subs_succ_one_ne_zero truncate16_zext64_trunc32 ult_max_two_false ult_three_false_of_ge
   ult_three_of_lt zext16_xor_trunc32)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (gf16SliceAt_focus_assoc)

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

private theorem sepWP_expose_state {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : ∀ s', s' = s → SepWP prog tgt s' P Q) : SepWP prog tgt s P Q :=
  h s rfl

private theorem sepWP_grab_acp {prog : Program} {tgt : BitVec 64} {s0 s_call sf_call : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hacp : AllocCallPreserved s_call sf_call) (htr : s_call.trace = s0.trace)
    (h : sf_call.trace = s0.trace → SepWP prog tgt sf_call P Q) :
    SepWP prog tgt sf_call P Q :=
  h (hacp.2.1.trans htr)

private theorem sepWP_grab_vm {prog : Program} {tgt : BitVec 64} {s0 s_call sf_call : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hcall : VmPreserved s_call sf_call) (htr_call : sf_call.trace = s_call.trace)
    (hpre : VmPreserved s0 s_call) (htr0 : s_call.trace = s0.trace)
    (h : VmPreserved s0 sf_call → sf_call.trace = s0.trace → SepWP prog tgt sf_call P Q) :
    SepWP prog tgt sf_call P Q :=
  h (hpre.trans hcall) (htr_call.trans htr0)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre calleeSavedVRegs_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm]
  zeroExtend_16_truncate_32_64 polyReduce_asm_eq
  ofNat_shl_one ofNat_shl_one_bv zext16_xor_trunc32
  Arm64.Obj.pageOf_add_lo12Of

/-- Sequence a zero-panic, zero-OOM `subroutine_ok` call under `LibsignalCodeLoaded` before a
`SepWP` continuation into `SepWPp` (budget counterpart of `SepWPp.call_panic_to_sepWP_lscl`). -/
theorem call_noPanic_to_sepWP_lscl [LibsignalPlacement]
    {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {s : State} {spec : Spec α} {x : α} {φ : Prop} {T F P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withMemEq s.mem spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf R', sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → False)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog ret sf (spec.post x s sf ∗ F) Q) :
    SepWPp prog ret s P Q Qp := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withMemEq s.mem spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withMemEq]
    rw [hspec, show ((⌜φ⌝ ∗ T) ∗ ⌜s.mem = s.mem⌝) ∗ (F ∗ R') =
      ⌜φ ∧ s.mem = s.mem⌝ ∗ ((T ∗ F) ∗ R') by rw [← pure_sepConj_pure]; sep_ac_rfl,
      ← hP, satisfies_pure_sepConj]
    exact ⟨⟨hφ, rfl⟩, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      SepWPp.of_sepWP_ret (Qp := Qp) (hnext sm hclm hpcm hrunm hspm hcsm) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpan sm (F ∗ R') hpan_st hpost).elim
  · exact (hexit sm code (F ∗ R') hex hpost).elim
  · exact (hoom sm R' hoom_st hpost).elim

set_option maxHeartbeats 1600000 in
/-- Deallocation epilogue (`+0x268..+0x2a0`) on Block `371`, stepping `st` by `rustDeallocEvents (2 * cap_xs) 2`. -/
theorem epilogue_dealloc_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (a : ComputeAtArgs) (R : SepProp) (s0 sf : State)
    (cap_xs : Nat) (hcap_pos : 0 < cap_xs) (hcap_bound : 2 * cap_xs + 2 ≤ 2 ^ 63)
    (p_xs : BitVec 64) (_hp_xs_ne : p_xs ≠ 0#64)
    (v120 : BitVec 64)
    (hpc : sf.pc = (blkPl_371).base + 616#64)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s0.sp - 144#64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (htr : sf.trace = s0.trace)
    (hvregs0 : calleeSavedVRegs sf = calleeSavedVRegs s0)
    (hx20 : BitVec.truncate 16 (sf.readReg64 .x20) = (computeAtPure a.poly a.x).value) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
      (memRegion p_xs (2 * cap_xs) ∗
       gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.live p_xs (2 * cap_xs) 2 ∗
       A.pool lim st sf ∗
       stackAt (s0.sp - 144#64) growOneStack ∗
       memRegion (s0.sp - 144#64) 8 ∗
       ((s0.sp - 136#64) ↦₆₄ BitVec.ofNat 64 cap_xs) ∗
       ((s0.sp - 128#64) ↦₆₄ p_xs) ∗
       ((s0.sp - 120#64) ↦₆₄ v120) ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace ∧
              BitVec.truncate 16 (sf1.readReg64 .x0) = (computeAtPure a.poly a.x).value ∧
              M.liveBytes (M.stepEvents (rustDeallocEvents (2 * cap_xs) 2) st) ≤ M.liveBytes st⌝ ∗
             gf16SliceAt a.p_coeffs a.poly.coefficients ∗
             tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (rustDeallocEvents (2 * cap_xs) 2) st) sf1 ∗
             stackAt s0.sp computeAtStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  rcases ofNat_beq_false_of_lt hcap_pos (by omega) with ⟨_, _, hcap_ne0, _⟩
  have htoNat_cap : (BitVec.ofNat 64 (2 * cap_xs)).toNat = 2 * cap_xs :=
    ofNat_two_mul_toNat cap_xs (by omega)
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  wp_conv_pre => rw [stackAt_growOne_eq_allocHook (s0.sp - 144#64), ← hsp]
  wp_steps 6
  wp_call hdealloc (p_xs, 2 * cap_xs, 2, st)
  have hlive_le :
      M.liveBytes (M.stepEvents (rustDeallocEvents (2 * cap_xs) 2) st) ≤ M.liveBytes st :=
    hpost
  refine sepWP_grab_acp (s0 := s0) (by assumption)
    (by simpa [wp_norm, arm64_norm] using htr) fun htr_ret => ?_
  wp_conv_pre => rw [hsp, stackAt_growOne_merge_allocHook (s0.sp - 144#64)]
  wp_steps 9
  apply SepWP.fold
    (stackAt_computeAt_merge s0.sp (s0.sp - 144#64)
      (BitVec.ofNat 64 cap_xs) p_xs v120
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) rfl)
    (by sep_focus)
  have hsp_ret : sf_1.sp + 144#64 = s0.sp := by
    rw [hsp_sf, hsp, BitVec.sub_add_cancel]
  have hx0_ret :
      BitVec.truncate 16 (BitVec.zeroExtend 64 (BitVec.truncate 32 (sf_1.readReg64 .x20))) =
        (computeAtPure a.poly a.x).value := by
    rw [truncate16_zext64_trunc32, h_1, hx20]
  have hvregs_ret : calleeSavedVRegs sf_1 = calleeSavedVRegs s0 := by
    rw [hvregs, hvregs0]
  wp_done

/-! ## Internal `VmPreserved`-Threaded Loop Helpers -/

private def unacceleratedMulPlacedVmSpec [LibsignalPlacement] : Spec (BitVec 16 × BitVec 16) where
  pre := fun (a, b_arg) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b_arg⌝ ∗
      reduceTablePlacedAt
  post := fun (a, b_arg) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = mul a b_arg ∧
      sf.trace = s0.trace ∧
      VmPreserved s0 sf⌝ ∗
      reduceTablePlacedAt

@[local arm64_norm, local wp_norm]
private theorem polyReduce_trunc16_asm_eq (a b_arg : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 (reduceByteEntry (BitVec.truncate 8
      ((polyMul a b_arg ^^^ BitVec.zeroExtend 32 (reduceByteEntry
        (BitVec.truncate 8 (polyMul a b_arg >>> 24))) <<< 8) >>> 16))) ^^^
      BitVec.zeroExtend 64 (polyMul a b_arg ^^^ BitVec.zeroExtend 32 (reduceByteEntry
        (BitVec.truncate 8 (polyMul a b_arg >>> 24))) <<< 8)) = mul a b_arg := by
  rw [← polyReduce_asm_eq]; ext i hi; simp

private theorem unacceleratedMul_placed_vm_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (blkPl_384).base
      unacceleratedMulPlacedVmSpec := by
  simp only [unacceleratedMulPlacedVmSpec]
  wp_init ab s0
  wp_steps 52
  rw [polyMul_asm_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul ab.1 ab.2 >>> 24)),
        uxtw1_idx1_eq (polyMul ab.1 ab.2)]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (polyMul ab.1 ab.2),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (polyMul ab.1 ab.2 >>> 24)),
        reduceTablePlacedAt_focus16 (BitVec.truncate 8 ((polyMul ab.1 ab.2 ^^^
          BitVec.zeroExtend 32 (reduceByteEntry (BitVec.truncate 8 (polyMul ab.1 ab.2 >>> 24))) <<< 8) >>> 16)),
        uxtw1_idx2_eq]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 ((polyMul ab.1 ab.2 ^^^
          BitVec.zeroExtend 32 (reduceByteEntry (BitVec.truncate 8 (polyMul ab.1 ab.2 >>> 24))) <<< 8) >>> 16))]
  wp_done

private theorem perm_powers_post (R T X S1 S2 S3 F : SepProp) :
    R ∗ T ∗ X ∗ S1 ∗ S2 ∗ S3 ∗ F =
      X ∗ S1 ∗ S2 ∗ S3 ∗ T ∗ R ∗ F := by sep_ac_rfl

private theorem perm_dot_post (R T C X F : SepProp) :
    R ∗ T ∗ C ∗ X ∗ F = C ∗ X ∗ T ∗ R ∗ F := by sep_ac_rfl

set_option maxHeartbeats 1600000 in
private theorem powersStep_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 p_xs : BitVec 64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (len i : Nat) (_hi2 : 2 ≤ i) (hi_lt : i < len) (hlen_bound : 2 * len + 2 ≤ 2 ^ 63)
    (xs : List GF16) (hxs_len : xs.length = i)
    (h1 : i / 2 < xs.length) (h2 : (i / 2) + (i % 2) < xs.length)
    (v_slot : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 216#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 i)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 len)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx27 : s.readReg64 .x27 = p_xs)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 i)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 212#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.pstate = subsPState64 (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 1)) →
      sf.readReg64 .x1 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = BitVec.ofNat 64 len →
      sf.readReg64 .x23 = lsρ tokenName + 8#64 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      sf.readReg64 .x27 = p_xs →
      sf.readReg64 .x28 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
         ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt p_xs xs ∗
       ((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
       ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
       ((sp0 - 128#64) ↦₆₄ p_xs) ∗
       ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  have halign_tok := aligned_tokenOnce_placed
  have hshr := ofNat_ushr_one (i := i) (by omega)
  have hshr_bv := ofNat_ushr_one_bv (i := i) (by omega)
  have hule1 := ofNat_ule_false_of_lt (m := i / 2) (n := i) (by omega) (by omega)
  have hand1 := ofNat_and_one i
  have hadd1 := ofNat_add_ofNat (i / 2) (i % 2)
  have hule2 := ofNat_ule_false_of_lt (m := (i / 2) + (i % 2)) (n := i) (by omega) (by omega)
  have hal1 := aligned16_add_mul_two p_xs hp_xs (i / 2)
  have hal2 := aligned16_add_mul_two p_xs hp_xs ((i / 2) + (i % 2))
  have hal_i := aligned16_add_mul_two p_xs hp_xs i
  rcases ofNat_beq_false_of_lt hi_lt (by omega) with ⟨hneq1, hneq2, hneq3, hneq4⟩
  have hadd_i := ofNat_add_one i
  have h_fetch_ldar := blkPC_371_rebase_fetch_0xfc (blkPl_371).base (Rust.withPanics ext)
  have hmul := lscall_blk (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
    (unacceleratedMul_placed_vm_ok (Rust.withPanics ext)) hcl
  simp only [withMemEq, unacceleratedMulPlacedVmSpec] at hmul
  apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 212#64)
  wp_steps 7
  wp_conv_pre => rw [gf16SliceAt_focus_assoc h1 p_xs]
  wp_steps 1
  wp_conv_pre => rw [← gf16SliceAt_focus_assoc h1 p_xs, gf16SliceAt_focus_assoc h2 p_xs]
  wp_steps 1
  wp_conv_pre => rw [← gf16SliceAt_focus_assoc h2 p_xs]
  wp_simp_pre [tokenInitPlacedAt]
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · exact h_fetch_ldar
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign_tok
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_call hmul
  refine sepWP_grab_vm (s0 := s) (by assumption) (by assumption)
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) fun hvm_pre htr_mul => ?_
  apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
    (Q := (blkPC_371).rebase (blkPl_371).base
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
    blkLib_eq_371 (mid := (blkPl_371).base + 212#64)
  intro m_strip
  wp_steps 10
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  have hvm_tot : VmPreserved s _ :=
    hvm_pre.trans (hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_next
  have hptr_eq : p_xs + BitVec.ofNat 64 (2 * i) = p_xs + BitVec.ofNat 64 (2 * xs.length) := by
    rw [hxs_len]
  have hval_eq : mul (xs[i / 2]'h1).value (xs[(i / 2) + (i % 2)]'h2).value =
      (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)).value := rfl
  wp_conv_pre =>
    rw [hptr_eq, hval_eq,
        gf16SliceAt_append_singleton_assoc p_xs xs
          (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)),
        perm_powers_post]
  exact hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm, hsp_sf] using hsp)
    (by simpa [arm64_norm, wp_norm] using htr_mul)
    hvm_tot
    (by wp_norm_lhs)
    (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using h)
    (by simpa [arm64_norm, wp_norm, h_1] using hx20)
    (by simpa [arm64_norm, wp_norm, h_4] using hx23)
    (by simpa [arm64_norm, wp_norm] using h_5)
    (by simpa [arm64_norm, wp_norm, h_6] using hx25)
    (by wp_norm_lhs)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hcs_sf)
    (by simpa [arm64_norm, wp_norm] using hvregs)

set_option maxHeartbeats 1600000 in
private theorem powersLoop_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (len : Nat) (hlen_bound : 2 * len + 2 ≤ 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r i : Nat) (xs : List GF16)
      (_hi2 : 2 ≤ i) (_hir : i + (r + 1) = len) (_hxs_len : xs.length = i)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_371).base + 216#64 →
      s.status = .Running →
      s.sp = sp0 - 144#64 →
      s.readReg64 .x1 = BitVec.ofNat 64 i →
      s.readReg64 .x20 = BitVec.ofNat 64 len →
      s.readReg64 .x23 = lsρ tokenName + 8#64 →
      s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x27 = p_xs →
      s.readReg64 .x28 = BitVec.ofNat 64 i →
      (∀ sf : State,
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_371).base + 416#64 →
        sf.status = .Running →
        sf.sp = sp0 - 144#64 →
        sf.trace = s.trace →
        VmPreserved s sf →
        sf.readReg64 .x1 = BitVec.ofNat 64 len →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = BitVec.ofNat 64 len →
        sf.readReg64 .x23 = lsρ tokenName + 8#64 →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
        sf.readReg64 .x27 = p_xs →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt p_xs (powersLoopPure i (r + 1) xs) ∗
           ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
           ((sp0 - 128#64) ↦₆₄ p_xs) ∗
           ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 len) ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt p_xs xs ∗
         memRegion (p_xs + BitVec.ofNat 64 (2 * i)) (2 * (r + 1)) ∗
         ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro r
  induction r with
  | zero =>
    intro i xs hi2 hir hxs_len s F hcl hpc hrun hsp hx1 hx20 hx23 hx25 hx27 hx28 hnext
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have hi_lt : i < len := by omega
    have hlen_eq : i + 1 = len := by omega
    rw [memRegion_two_succ (p_xs + BitVec.ofNat 64 (2 * i)) 0 (by omega),
        memRegion_zero, sepConj_emp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun v_slot => ?_
    apply powersStep_placed_vm_sepWP ext sp0 p_xs hp_xs len i hi2 hi_lt hlen_bound xs hxs_len
      h1 h2 v_slot ret_pc Q s F hcl hpc hrun hsp hsp0 hx1 hx20 hx23 hx25 hx27 hx28
    intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hpst1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    rw [hlen_eq] at hpst1 hx1_1 hx28_1 ⊢
    wp_steps 1
    rw [powersLoopPure_succ i 0 xs h1 h2] at hnext
    dsimp only [powersLoopPure] at hnext
    exact hnext _ hcl1 (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htr1)
      (hvm1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [arm64_norm, wp_norm] using hx1_1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r' ih =>
    intro i xs hi2 hir hxs_len s F hcl hpc hrun hsp hx1 hx20 hx23 hx25 hx27 hx28 hnext
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have hi_lt : i < len := by omega
    have hi1_lt : i + 1 < len := by omega
    rcases ofNat_beq_false_of_lt hi1_lt (by omega) with ⟨hneq1, hneq2, hneq3, hneq4⟩
    rw [memRegion_two_succ (p_xs + BitVec.ofNat 64 (2 * i)) (r' + 1) (by omega),
        ptr_add_two_step p_xs i]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun v_slot => ?_
    wp_conv_pre =>
      rw [show gf16SliceAt p_xs xs ∗
            (((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
             memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1))) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F =
          gf16SliceAt p_xs xs ∗
            ((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F) by sep_ac_rfl]
    apply powersStep_placed_vm_sepWP ext sp0 p_xs hp_xs len i hi2 hi_lt hlen_bound xs hxs_len
      h1 h2 v_slot ret_pc Q s (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F)
      hcl hpc hrun hsp hsp0 hx1 hx20 hx23 hx25 hx27 hx28
    intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hpst1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    wp_steps 1
    wp_conv_pre =>
      rw [show gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F) =
          gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
            memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F by sep_ac_rfl]
    apply ih (i + 1) (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)])
      (by omega) (by omega) (by simp [hxs_len]) _ F (by exact hcl1)
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx1_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
    intro sf hcl_f hpc_f hrun_f hsp_f htr_f hvm_f hx1_f hx19_f hx20_f hx23_f hx24_f hx25_f hx27_f hx29_f hvregs_f
    rw [powersLoopPure_succ i (r' + 1) xs h1 h2] at hnext
    exact hnext sf hcl_f hpc_f hrun_f hsp_f
      (by rw [htr_f]; simpa [arm64_norm, wp_norm] using htr1)
      ((hvm1.trans (by simp only [wp_norm, arm64_norm])).trans hvm_f)
      hx1_f
      (by rw [hx19_f]; simpa [arm64_norm, wp_norm] using hx19_1)
      hx20_f hx23_f
      (by rw [hx24_f]; simpa [arm64_norm, wp_norm] using hx24_1)
      hx25_f hx27_f
      (by rw [hx29_f]; simpa [arm64_norm, wp_norm] using hx29_1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
private theorem dotStep_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (p_coeffs p_xs : BitVec 64) (hpx_al : p_xs &&& 1#64 = 0#64)
    (coeffs xs : List GF16)
    (r k : Nat) (acc : GF16)
    (hkc : k < coeffs.length) (hkx : k < xs.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 472#64)
    (hrun : s.status = .Running)
    (hsp_al : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * k))
    (hx20 : BitVec.truncate 16 (s.readReg64 .x20) = acc.value)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx27 : s.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * k))
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (r + 1))
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 468#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      (sf.sp &&& 15#64 == 0#64) = true →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.pstate = subsPState64 (BitVec.ofNat 64 (r + 1)) 1#64 →
      sf.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * (k + 1)) →
      BitVec.truncate 16 (sf.readReg64 .x20) =
        (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx))).value →
      sf.readReg64 .x23 = lsρ tokenName + 8#64 →
      sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      sf.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x28 = BitVec.ofNat 64 r →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_coeffs coeffs ∗
         gf16SliceAt p_xs xs ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt p_coeffs coeffs ∗
       gf16SliceAt p_xs xs ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  have halign_tok := aligned_tokenOnce_placed
  have hal_x := aligned16_add_mul_two p_xs hpx_al k
  have hstep_c := ptr_add_two_step p_coeffs k
  have hstep_x := ptr_add_two_step p_xs k
  have hsub_r := ofNat_sub_one_succ r
  have h_fetch_ldar := blkPC_371_rebase_fetch_0x1e0 (blkPl_371).base (Rust.withPanics ext)
  have hmul := lscall_blk (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
    (unacceleratedMul_placed_vm_ok (Rust.withPanics ext)) hcl
  simp only [withMemEq, unacceleratedMulPlacedVmSpec] at hmul
  apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 468#64)
  wp_conv_pre => rw [gf16SliceAt_focus_assoc hkc p_coeffs]
  wp_steps 1
  wp_conv_pre =>
    rw [← gf16SliceAt_focus_assoc hkc p_coeffs,
        gf16SliceAt_focus_assoc hkx p_xs]
  wp_steps 1
  wp_conv_pre =>
    rw [← gf16SliceAt_focus_assoc hkx p_xs]
  wp_simp_pre [tokenInitPlacedAt]
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · exact h_fetch_ldar
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign_tok
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_call hmul
  refine sepWP_grab_vm (s0 := s) (by assumption) (by assumption)
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) fun hvm_pre htr_mul => ?_
  wp_steps 2
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_next
  wp_conv_pre => rw [perm_dot_post]
  exact hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp_sf)
    (by simpa [arm64_norm, wp_norm, hsp_sf] using hsp_al)
    (by simpa [arm64_norm, wp_norm] using htr_mul)
    (hvm_pre.trans (by simp only [wp_norm, arm64_norm]))
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using h)
    (by simp only [arm64_norm, wp_norm]
        rw [h_10, hx20]
        exact eor_gf16_add_comm acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
    (by simpa [arm64_norm, wp_norm, h_4] using hx23)
    (by simpa [arm64_norm, wp_norm, h_6] using hx25)
    (by simpa [arm64_norm, wp_norm] using h_8)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hcs_sf)
    (by simpa [arm64_norm, wp_norm] using hvregs)

set_option maxHeartbeats 1600000 in
private theorem dotLoop_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (p_coeffs p_xs : BitVec 64) (hpx_al : p_xs &&& 1#64 = 0#64)
    (coeffs xs : List GF16)
    (hlen_le : coeffs.length ≤ xs.length) (hlen_bound : 2 * coeffs.length + 2 ≤ 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r k : Nat) (acc : GF16)
      (_hkr : k + (r + 1) = coeffs.length)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_371).base + 472#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * k) →
      BitVec.truncate 16 (s.readReg64 .x20) = acc.value →
      s.readReg64 .x23 = lsρ tokenName + 8#64 →
      s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * k) →
      s.readReg64 .x28 = BitVec.ofNat 64 (r + 1) →
      (∀ sf : State,
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_371).base + 616#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        (sf.sp &&& 15#64 == 0#64) = true →
        sf.trace = s.trace →
        VmPreserved s sf →
        BitVec.truncate 16 (sf.readReg64 .x20) = (dotLoopPure k (r + 1) coeffs xs acc).value →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt p_coeffs coeffs ∗
           gf16SliceAt p_xs xs ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt p_coeffs coeffs ∗
         gf16SliceAt p_xs xs ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro r
  induction r with
  | zero =>
    intro k acc hkr s F hcl hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28 hnext
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    apply dotStep_placed_vm_sepWP ext p_coeffs p_xs hpx_al coeffs xs 0 k acc hkc hkx
      ret_pc Q s F hcl hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28
    intro s1 hcl1 hpc1 hrun1 hsp1 hsp_al1 htr1 hvm1 hpst1 _hx19_1 hx20_1 _hx23_1 _hx25_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    wp_steps 1
    rw [dotLoopPure_succ k 0 coeffs xs acc hkc hkx] at hnext
    dsimp only [dotLoopPure] at hnext
    exact hnext _ hcl1 (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hsp_al1)
      (by simpa [arm64_norm, wp_norm] using htr1)
      (hvm1.trans (by simp only [wp_norm, arm64_norm]))
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r' ih =>
    intro k acc hkr s F hcl hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28 hnext
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    rcases subs_succ_one_ne_zero (r := r') (by omega) with ⟨hneq1, hneq2⟩
    apply dotStep_placed_vm_sepWP ext p_coeffs p_xs hpx_al coeffs xs (r' + 1) k acc hkc hkx
      ret_pc Q s F hcl hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28
    intro s1 hcl1 hpc1 hrun1 hsp1 hsp_al1 htr1 hvm1 hpst1 hx19_1 hx20_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    wp_steps 1
    apply ih (k + 1) (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
      (by omega) _ F (by exact hcl1)
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp_al1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
    intro sf hcl_f hpc_f hrun_f hsp_f hsp_al_f htr_f hvm_f hx20_f hx29_f hvregs_f
    rw [dotLoopPure_succ k (r' + 1) coeffs xs acc hkc hkx] at hnext
    exact hnext sf hcl_f hpc_f hrun_f
      (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp1)
      hsp_al_f
      (by rw [htr_f]; simpa [arm64_norm, wp_norm] using htr1)
      ((hvm1.trans (by simp only [wp_norm, arm64_norm])).trans hvm_f)
      hx20_f
      (by rw [hx29_f]; simpa [arm64_norm, wp_norm] using hx29_1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
private theorem dot_from_61ab4_placed_vm_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (a : ComputeAtArgs) (hlen_pos : 0 < a.poly.coefficients.length)
    (hlen_bound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63)
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx27 : s.readReg64 .x27 = p_xs)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 616#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      BitVec.truncate 16 (sf.readReg64 .x20) = (computeAtPure a.poly a.x).value →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
         gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  rcases ofNat_beq_false_of_lt hlen_pos (by omega) with ⟨_, _, hlen_ne0, _⟩
  have hult_false :
      (BitVec.ofNat 64 (max 2 a.poly.coefficients.length)).ult
        (BitVec.ofNat 64 a.poly.coefficients.length) = false :=
    ult_max_two_false a.poly.coefficients.length hlen_bound
  have hsp_al : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, beq_iff_eq]; revert hsp0; bv_bits
  wp_steps 10
  have hle_powers :
      a.poly.coefficients.length ≤
        (computeAtPowersPure a.poly.coefficients.length a.x).length := by
    rw [computeAtPowersPure_length]; omega
  have hr_eq :
      BitVec.ofNat 64 a.poly.coefficients.length =
        BitVec.ofNat 64 (a.poly.coefficients.length - 1 + 1) := by
    congr 1; omega
  apply dotLoop_placed_vm_sepWP ext a.p_coeffs p_xs hp_xs
    a.poly.coefficients (computeAtPowersPure a.poly.coefficients.length a.x)
    hle_powers hlen_bound ret_pc Q
    (a.poly.coefficients.length - 1) 0 GF16.ZERO (by omega)
    _ F (by exact hcl)
    (by wp_norm_lhs)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp_al)
    (by simpa [arm64_norm, wp_norm] using hx19)
    (by rfl)
    (by simpa [arm64_norm, wp_norm] using hx23)
    (by simpa [arm64_norm, wp_norm] using hx25)
    (by simpa [arm64_norm, wp_norm] using hx27)
    (by simp only [arm64_norm, wp_norm, hr_eq])
  intro sf hcl_f hpc_f hrun_f hsp_f _hsp_al_f htr_f hvm_f hx20_f hx29_f hvregs_f
  have hdot_eq :
      dotLoopPure 0 (a.poly.coefficients.length - 1 + 1)
        a.poly.coefficients (computeAtPowersPure a.poly.coefficients.length a.x) GF16.ZERO =
        computeAtPure a.poly a.x := by
    rw [Nat.sub_add_cancel hlen_pos, ← computeAtPure_eq_dotLoopPure]
  rw [hdot_eq] at hx20_f
  exact hnext sf hcl_f hpc_f hrun_f
    (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp)
    (by simpa [arm64_norm, wp_norm] using htr_f)
    ((by simp only [wp_norm, arm64_norm] : VmPreserved s _).trans hvm_f)
    hx20_f
    (by simpa [arm64_norm, wp_norm] using hx29_f)
    (by simpa [arm64_norm, wp_norm] using hvregs_f)

/-! ## Budget-Threaded Relocatable `[LibsignalPlacement]` Phase Lemmas -/

set_option maxHeartbeats 1600000 in
/-- Power-table phase (`+0x60..+0x1a0`) on Block `371` preserving `VmPreserved s sf`. -/
theorem powers_from_61974_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (a : ComputeAtArgs) (hlen_bound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63)
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (v_cap : BitVec 64)
    (hcap_ge3 : 3 ≤ a.poly.coefficients.length →
      v_cap = BitVec.ofNat 64 a.poly.coefficients.length)
    (v1 : BitVec 16) (v120 : BitVec 64)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hx0 : s.readReg64 .x0 = p_xs)
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx21 : BitVec.truncate 16 (s.readReg64 .x21) = a.x.value)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 416#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.readReg64 .x1 = BitVec.ofNat 64 (max 2 a.poly.coefficients.length) →
      sf.readReg64 .x19 = a.p_coeffs →
      sf.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length →
      sf.readReg64 .x23 = lsρ tokenName + 8#64 →
      sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      sf.readReg64 .x27 = p_xs →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
         ((sp0 - 136#64) ↦₆₄ v_cap) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (max 2 a.poly.coefficients.length)) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      ((p_xs ↦₁₆ 1#16) ∗
       ((p_xs + 2#64) ↦₁₆ v1) ∗
       memRegion (p_xs + 4#64) (2 * (a.poly.coefficients.length - 2)) ∗
       ((sp0 - 136#64) ↦₆₄ v_cap) ∗
       ((sp0 - 128#64) ↦₆₄ p_xs) ∗
       ((sp0 - 120#64) ↦₆₄ v120) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  have hal_p2 : MemWidth.isAligned .W16 (p_xs + 2#64) = true :=
    aligned16_add_mul_two p_xs hp_xs 1
  have hsp_al : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, beq_iff_eq]; revert hsp0; bv_bits
  by_cases hlt3 : a.poly.coefficients.length < 3
  · have hult3 : (BitVec.ofNat 64 a.poly.coefficients.length).ult 3#64 = true :=
      ult_three_of_lt a.poly.coefficients.length hlt3
    apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 416#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_371).rebase (blkPl_371).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_371 (mid := (blkPl_371).base + 416#64)
    intro m_strip
    wp_steps 12
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
    have hvm_f : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_f
    have hmax2 : max 2 a.poly.coefficients.length = 2 := by omega
    have hsub2 : a.poly.coefficients.length - 2 = 0 := by omega
    have hle2 : a.poly.coefficients.length ≤ 2 := by omega
    have hpow_le2 : computeAtPowersPure a.poly.coefficients.length a.x = [GF16.ONE, a.x] := by
      unfold computeAtPowersPure
      simp [hle2]
    wp_conv_pre =>
      rw [hsub2, Nat.mul_zero, memRegion_zero, emp_sepConj,
          combine_two_gf16 p_xs a.x, ← hpow_le2]
    rw [hmax2] at hnext
    apply hnext _ hcl_f
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hsp
    · wp_norm_lhs
    · exact hvm_f
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hx19
    · simpa [arm64_norm, wp_norm] using hx20
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
  · have hge3 : 3 ≤ a.poly.coefficients.length := by omega
    have hult3 : (BitVec.ofNat 64 a.poly.coefficients.length).ult 3#64 = false :=
      ult_three_false_of_ge a.poly.coefficients.length hge3 hlen_bound
    have hv_cap := hcap_ge3 hge3
    subst hv_cap
    apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 216#64)
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_371).rebase (blkPl_371).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_371 (mid := (blkPl_371).base + 216#64)
    intro m_strip
    wp_steps 19
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
    have hvm_mid : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_mid
    have hrem_eq : a.poly.coefficients.length - 2 = (a.poly.coefficients.length - 3) + 1 := by omega
    wp_conv_pre =>
      rw [combine_two_gf16 p_xs a.x, hrem_eq,
          show p_xs + 4#64 = p_xs + BitVec.ofNat 64 (2 * 2) from rfl]
    apply powersLoop_placed_vm_sepWP ext sp0 p_xs hsp0 hp_xs
      a.poly.coefficients.length hlen_bound ret_pc Q
      (a.poly.coefficients.length - 3) 2 [GF16.ONE, a.x]
      (by omega) (by omega) (by rfl) _ F (by exact hcl_mid)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp)
      (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hx20)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
    intro sf hcl_f hpc_f hrun_f hsp_f htr_f hvm_f hx1_f hx19_f hx20_f hx23_f _hx24_f hx25_f hx27_f hx29_f hvregs_f
    have hmax_ge3 : max 2 a.poly.coefficients.length = a.poly.coefficients.length := by omega
    have hnot_le2 : ¬ a.poly.coefficients.length ≤ 2 := by omega
    have hpow_ge3 :
        powersLoopPure 2 (a.poly.coefficients.length - 3 + 1) [GF16.ONE, a.x] =
          computeAtPowersPure a.poly.coefficients.length a.x := by
      unfold computeAtPowersPure
      simp only [hnot_le2, ↓reduceIte,
        show a.poly.coefficients.length - 2 = a.poly.coefficients.length - 3 + 1 by omega]
    wp_conv_pre => rw [hpow_ge3]
    rw [hmax_ge3] at hnext
    exact hnext sf hcl_f hpc_f hrun_f hsp_f
      (by simpa [arm64_norm, wp_norm] using htr_f)
      (hvm_mid.trans hvm_f)
      hx1_f
      (by rw [hx19_f]; simpa [arm64_norm, wp_norm] using hx19)
      hx20_f hx23_f hx25_f hx27_f
      (by rw [hx29_f]; wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hvregs_f)

set_option maxHeartbeats 1600000 in
/-- Budget-threaded phase composition from `+0x60` to return on Block `371` for `len ≤ 1` (`cap_xs = 4`). -/
theorem from_61974_cap4_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (a : ComputeAtArgs) (R : SepProp) (s0 s : State)
    (hlen_le1 : a.poly.coefficients.length ≤ 1)
    (p_xs : BitVec 64) (hp_xs_ne : p_xs ≠ 0#64) (hp_xs_al : p_xs &&& 1#64 = 0#64)
    (w1 : BitVec 16) (v120 : BitVec 64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (htr : s.trace = s0.trace)
    (hvregs0 : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = p_xs)
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx21 : BitVec.truncate 16 (s.readReg64 .x21) = a.x.value) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((p_xs ↦₁₆ 1#16) ∗
       ((p_xs + 2#64) ↦₁₆ w1) ∗
       ((s0.sp - 136#64) ↦₆₄ 4#64) ∗
       ((s0.sp - 128#64) ↦₆₄ p_xs) ∗
       ((s0.sp - 120#64) ↦₆₄ v120) ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       memRegion (p_xs + 4#64) 4 ∗
       A.live p_xs 8 2 ∗
       A.pool lim st s ∗
       stackAt (s0.sp - 144#64) growOneStack ∗
       memRegion (s0.sp - 144#64) 8 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace ∧
              BitVec.truncate 16 (sf1.readReg64 .x0) = (computeAtPure a.poly a.x).value ∧
              M.liveBytes (M.stepEvents (rustDeallocEvents 8 2) st) ≤ M.liveBytes st⌝ ∗
             gf16SliceAt a.p_coeffs a.poly.coefficients ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (rustDeallocEvents 8 2) st) sf1 ∗
             stackAt s0.sp computeAtStack ∗ R)) ∧
        sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  wp_conv_pre =>
    rw [insert_emp_memRegion_after_w1 p_xs w1 a.poly.coefficients.length (by omega)]
  apply powers_from_61974_placed_sepWP ext a (by omega) s0.sp p_xs hsp0 hp_xs_al
    4#64 (fun h => by omega) w1 v120 (s0.readReg64 Reg.lr) _ s _
    hcl hpc hrun hsp hx0 hx19 hx20 hx21
  intro sf1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hx1_1 hx19_1 hx20_1 hx23_1 hx25_1 hx27_1 _hx29_1 hvregs1
  have htr1' : sf1.trace = s0.trace := by rw [htr1, htr]
  have hvregs1' : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by rw [hvregs1, hvregs0]
  have hlen_pow : (computeAtPowersPure a.poly.coefficients.length a.x).length = 2 := by
    rw [computeAtPowersPure_length]; omega
  wp_conv_pre => rw [powers_to_dot_frame]
  by_cases hnil : a.poly.coefficients = []
  · have hlen0 : a.poly.coefficients.length = 0 := by simp [hnil]
    rw [hlen0] at hx1_1 hx20_1
    change sf1.readReg64 .x1 = 2#64 at hx1_1
    change sf1.readReg64 .x20 = 0#64 at hx20_1
    wp_steps 4
    refine sepWP_expose_state fun s2 hs2 => ?_
    have hvm_sf2 : VmPreserved s s2 := by
      rw [hs2]; exact hvm1.trans (by simp only [wp_norm, arm64_norm])
    subst hs2
    apply SepWP.fold
      (gf16Slice2_rest4_entails_memRegion8 p_xs
        (computeAtPowersPure a.poly.coefficients.length a.x) hlen_pow)
      (by sep_focus)
    wp_conv_pre =>
      rw [← A.pool_of_vmPreserved hvm_sf2,
          show (8 : Nat) = 2 * 4 from rfl,
          show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
    refine epilogue_dealloc_placed_sepWP M A lim st ext hdealloc a R s0 _ 4 (by omega) (by omega)
      p_xs hp_xs_ne (BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
      (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      hsp0 (by simpa [arm64_norm, wp_norm] using htr1')
      (by simpa [arm64_norm, wp_norm] using hvregs1') ?_
    have hp_nil : a.poly = ⟨[]⟩ := by
      cases hp : a.poly with
      | mk cs =>
        have : cs = [] := by simpa [hp] using hnil
        subst this; rfl
    rw [hp_nil, computeAtPure_nil a.x]
    rfl
  · have hlen_pos : 0 < a.poly.coefficients.length := List.length_pos_iff.mpr hnil
    apply dot_from_61ab4_placed_vm_sepWP ext a hlen_pos (by omega)
      s0.sp p_xs hsp0 hp_xs_al (s0.readReg64 Reg.lr) _ sf1 _
      (by exact hcl1) hpc1 hrun1 hsp1 hx1_1 hx19_1 hx20_1 hx23_1 hx25_1 hx27_1
    intro sf2 _hcl2 hpc2 hrun2 hsp2 htr2 hvm2 hx20_2 _hx29_2 hvregs2
    have hvm_sf2 : VmPreserved s sf2 := hvm1.trans hvm2
    apply SepWP.fold
      (gf16Slice2_rest4_entails_memRegion8 p_xs
        (computeAtPowersPure a.poly.coefficients.length a.x) hlen_pow)
      (by sep_focus)
    wp_conv_pre =>
      rw [← A.pool_of_vmPreserved hvm_sf2,
          show (8 : Nat) = 2 * 4 from rfl,
          show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
    refine epilogue_dealloc_placed_sepWP M A lim st ext hdealloc a R s0 sf2 4 (by omega) (by omega)
      p_xs hp_xs_ne (BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
      hpc2 hrun2 hsp2 hsp0 (by rw [htr2, htr1']) (by rw [hvregs2, hvregs1']) hx20_2

set_option maxHeartbeats 1600000 in
/-- Budget-threaded phase composition from `+0x60` to return on Block `371` for `2 ≤ len` (`cap_xs = len`). -/
theorem from_61974_ge2_placed_sepWP [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (a : ComputeAtArgs) (R : SepProp) (s0 s : State)
    (hlen_ge2 : 2 ≤ a.poly.coefficients.length)
    (hlen_bound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63)
    (p_xs : BitVec 64) (hp_xs_ne : p_xs ≠ 0#64) (hp_xs_al : p_xs &&& 1#64 = 0#64)
    (w1 : BitVec 16) (v120 : BitVec 64)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (htr : s.trace = s0.trace)
    (hvregs0 : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = p_xs)
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx21 : BitVec.truncate 16 (s.readReg64 .x21) = a.x.value) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((p_xs ↦₁₆ 1#16) ∗
       ((p_xs + 2#64) ↦₁₆ w1) ∗
       memRegion (p_xs + 4#64) (2 * (a.poly.coefficients.length - 2)) ∗
       ((s0.sp - 136#64) ↦₆₄ BitVec.ofNat 64 a.poly.coefficients.length) ∗
       ((s0.sp - 128#64) ↦₆₄ p_xs) ∗
       ((s0.sp - 120#64) ↦₆₄ v120) ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       A.live p_xs (2 * a.poly.coefficients.length) 2 ∗
       A.pool lim st s ∗
       stackAt (s0.sp - 144#64) growOneStack ∗
       memRegion (s0.sp - 144#64) 8 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace ∧
              BitVec.truncate 16 (sf1.readReg64 .x0) = (computeAtPure a.poly a.x).value ∧
              M.liveBytes (M.stepEvents (rustDeallocEvents (2 * a.poly.coefficients.length) 2) st) ≤
                M.liveBytes st⌝ ∗
             gf16SliceAt a.p_coeffs a.poly.coefficients ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (rustDeallocEvents (2 * a.poly.coefficients.length) 2) st) sf1 ∗
             stackAt s0.sp computeAtStack ∗ R)) ∧
        sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1) := by
  apply powers_from_61974_placed_sepWP ext a hlen_bound s0.sp p_xs hsp0 hp_xs_al
    (BitVec.ofNat 64 a.poly.coefficients.length) (fun _ => rfl) w1 v120
    (s0.readReg64 Reg.lr) _ s _
    hcl hpc hrun hsp hx0 hx19 hx20 hx21
  intro sf1 hcl1 hpc1 hrun1 hsp1 htr1 hvm1 hx1_1 hx19_1 hx20_1 hx23_1 hx25_1 hx27_1 _hx29_1 hvregs1
  have htr1' : sf1.trace = s0.trace := by rw [htr1, htr]
  have hvregs1' : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by rw [hvregs1, hvregs0]
  have hlen_pow :
      (computeAtPowersPure a.poly.coefficients.length a.x).length =
        a.poly.coefficients.length := by
    rw [computeAtPowersPure_length]; omega
  wp_conv_pre => rw [powers_to_dot_ge2_frame]
  apply dot_from_61ab4_placed_vm_sepWP ext a (by omega) hlen_bound
    s0.sp p_xs hsp0 hp_xs_al (s0.readReg64 Reg.lr) _ sf1 _
    (by exact hcl1) hpc1 hrun1 hsp1 hx1_1 hx19_1 hx20_1 hx23_1 hx25_1 hx27_1
  intro sf2 _hcl2 hpc2 hrun2 hsp2 htr2 hvm2 hx20_2 _hx29_2 hvregs2
  have hvm_sf2 : VmPreserved s sf2 := hvm1.trans hvm2
  have hent_ge2 :
      gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ⊢
        memRegion p_xs (2 * a.poly.coefficients.length) := by
    have h := gf16SliceAt_entails_memRegion p_xs
      (computeAtPowersPure a.poly.coefficients.length a.x) (by rw [hlen_pow]; omega)
    rwa [hlen_pow] at h
  apply SepWP.fold hent_ge2 (by sep_focus)
  wp_conv_pre => rw [← A.pool_of_vmPreserved hvm_sf2]
  exact epilogue_dealloc_placed_sepWP M A lim st ext hdealloc a R s0 sf2 a.poly.coefficients.length
    (by omega) hlen_bound p_xs hp_xs_ne
    (BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
    hpc2 hrun2 hsp2 hsp0 (by rw [htr2, htr1']) (by rw [hvregs2, hvregs1']) hx20_2

end LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.PhaseBudget
