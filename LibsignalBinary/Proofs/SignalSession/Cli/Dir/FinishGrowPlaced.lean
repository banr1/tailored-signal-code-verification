/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrow
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `[LibsignalPlacement]` `RawVecInner::finish_grow` (Block `587`)

Self-contained `[LibsignalPlacement]` proof of Block `587` (`finish_grow [local#10]`)
under `StoreKit.withLsCodeRoLoaded lsmpl` and `AllocContractsXCliPlaced A H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.FinishGrow

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem umulh_stride_eq_zero_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]; rfl

private theorem mul_stride_toNat_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat_p h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem beq_mul_stride_zero_eq_false_p {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat_p h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem hi_stride_eq_false_p {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]; change align.toNat ≤ 2 ^ 63; omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat_p (by omega)]
  omega

private theorem memRegion_24_p (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrowX_p (sp : BitVec 64) :
    stackAt sp finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 16384 6 (by decide)

private def finishGrowZeroSpec2XPlaced (A : RustAlloc) : Spec FinishGrowCall :=
  { finishGrowSpecX A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp finishGrowStackX }

private theorem finish_grow_zero_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_587 H) (blkPl_587).base
      (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowZeroSpec2XPlaced A)) := by
  have hshim := shim_lscro_of_cli (callerProg := lsProg_587 H) hA (stk := extHookStack) (by decide) (by decide)
  have halloc := alloc_lscro_of_cli (callerProg := lsProg_587 H) hA
  dsimp only [StoreKit.withLsCodeRoLoaded, withStack, sessionShimSpec, lsProg_587] at hshim
  dsimp only [StoreKit.withLsCodeRoLoaded, rustAllocSpecWithStack, lsProg_587] at halloc
  unfold StoreKit.withLsCodeRoLoaded finishGrowZeroSpec2XPlaced finishGrowSpecX
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  clear h
  dsimp only at *
  have hlay0 : LayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay0 with ⟨hsz_pos, hpow, hbound⟩
  have hcap0_eq : cap = 0#64 := by assumption
  have hbs0_eq : bs = [] := by assumption
  subst hcap0_eq
  subst hbs0_eq
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply StoreKit.sepWP_seq_lscro hcrl0 (mid := lsρ lsRustNoAllocShimSymCli)
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  apply StoreKit.sepWP_seq_lscro hcrl1 (mid := lsρ lsRustAllocSymCli)
  rcases hcrl1 with ⟨hcl1, hro1⟩
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  rcases hcrl2 with ⟨hcl2, hro2⟩
  wp_call halloc (new.toNat * stride.toNat, align.toNat)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat_p hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat_p hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists align
    simp only [ite_true, FinishGrowCall.oldBuf]
    wp_done

private def finishGrowNeSpec2XPlaced (A : RustAlloc) : Spec FinishGrowCall :=
  { finishGrowSpecX A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
        (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp finishGrowStackX }

private theorem finish_grow_ne_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_587 H) (blkPl_587).base
      (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowNeSpec2XPlaced A)) := by
  dsimp only [StoreKit.withLsCodeRoLoaded, finishGrowNeSpec2XPlaced, finishGrowSpecX]
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  have hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  clear h
  dsimp only [FinishGrowCall.oldBuf] at *
  have hrealloc := realloc_lscro_of_cli (callerProg := lsProg_587 H) hA
  have hlay0 : LayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay0 with ⟨hsz_pos, hpow, hbound⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat_p hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : LayoutOk (cap.toNat * stride.toNat) align.toNat := ⟨hold_pos, hpow, by omega⟩
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply StoreKit.sepWP_seq_lscro hcrl (mid := lsρ lsRustReallocSymCli)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro hrealloc hcrl1 (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat_p hlt64
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
      mul_stride_eq_ofNat_p hlt64
    simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists align
    simp only [ite_true, hcap_ne, ite_false]
    wp_done

/-- Block 587 (`finish_grow [local#10]`) satisfies `StoreKit.withLsCodeRoLoaded lsmpl (finishGrowSpecX A)`. -/
theorem cliFinishGrow_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowSpecX A)) := by
  change subroutine_ok (lsProg_587 H) (blkPl_587).base _
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcrl, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine finish_grow_zero_placed_ok_x hA x R s0 hpc hrun ?_ hsp
    refine satisfies_lscro_pre hcrl ?_
    simp only [finishGrowSpecX, finishGrowZeroSpec2XPlaced, FinishGrowCall.oldBuf, hcap0, ite_true,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨h0, h1, h2, h3, h4, h5, hbs0, _, hle, hpos, hstr, hlay⟩, hmem⟩
    exact ⟨⟨h0, h1, h2, h3, h4, h5, trivial, hbs0 trivial, hle, hpos, hstr, hlay⟩, hmem⟩
  · refine finish_grow_ne_placed_ok_x hA x R s0 hpc hrun ?_ hsp
    refine satisfies_lscro_pre hcrl ?_
    simp only [finishGrowSpecX, finishGrowNeSpec2XPlaced, FinishGrowCall.oldBuf, hcap0, ite_false,
      sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨h0, h1, h2, h3, h4, h5, _, hbs_le, hle, hpos, hstr, hlay⟩, hmem⟩
    exact ⟨⟨h0, h1, h2, h3, h4, h5, hcap0, hbs_le, hle, hpos, hstr, hlay⟩, hmem⟩

/-- Caller-block lifted `finish_grow` contract under `StoreKit.withLsCodeRoLoaded lsmpl`. -/
theorem cliFinishGrow_placed_caller_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A H) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 587)
      (StoreKit.withLsCodeRoLoaded lsmpl (finishGrowSpecX A)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 587) (cliFinishGrow_placed_ok_x hA) hi

end CryptoVerification.SignalSession.Cli.FinishGrow
