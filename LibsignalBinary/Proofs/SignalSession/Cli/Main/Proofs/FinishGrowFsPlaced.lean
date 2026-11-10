/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FinishGrowFs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-!
# Relocatable `finish_grow [local#10]` (Block `587`)

Relocatable `[LibsignalPlacement]` contracts for `finish_grow [local#10]` on Block `587` (with and
without `Spec.keepsFs`), cell-form corollaries, and cross-block lifts via `StoreKit.withLsRoCl`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

@[local simp]
theorem keepsFs_withLsCodeRoLoaded {α : Type} (spec : Spec α) (mpl : MultiPlacement) :
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded mpl spec).keepsFs =
      LibsignalPublicApi.StoreKit.withLsCodeRoLoaded mpl spec.keepsFs :=
  rfl

/-! ## 1. Arithmetic & Memory Helpers -/

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
  rw [hdiv]
  rfl

private theorem mul_stride_toNat_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat_p h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero_p {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat_p h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false_p {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero_p h0 h

private theorem hi_stride_eq_false_p {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
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

/-! ## 2. Block `587` Zero-Cap & Nonzero-Cap Symbolic Execution -/

private def finishGrowZeroSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
  { finishGrowSpecX A with
      pre := fun x s =>
        ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
          s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
          x.cap = 0#64 ∧ x.bs = [] ∧
          x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
          LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
        memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp finishGrowStackX }

private def finishGrowNeSpec2X (A : RustAlloc) : Spec FinishGrowCall :=
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

set_option maxHeartbeats 1000000 in
private theorem finish_grow_zero_blk587_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (finishGrowZeroSpec2X A)) := by
  have hshim := hC.shim2_rocl (prog := lsProg_587 H) (i := 587)
  have halloc := hC.alloc_rocl (prog := lsProg_587 H) (i := 587)
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, session2ShimSpecX, lsProg_587] at hshim
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustAllocSpecWithStack, lsProg_587] at halloc
  unfold LibsignalPublicApi.StoreKit.withLsCodeRoLoaded finishGrowZeroSpec2X finishGrowSpecX
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨hsz_pos, hpow, hbound⟩
  have hcap_eq : cap = 0#64 := by assumption
  have hbs_eq : bs = [] := by assumption
  subst hcap_eq
  subst hbs_eq
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  simp only [wp_norm] at hcrl2
  have ⟨hcl2, hro2⟩ := hcrl2
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

set_option maxHeartbeats 1000000 in
private theorem finish_grow_zero_fs_blk587_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hCF : AllocContractsFsPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (finishGrowZeroSpec2X A).keepsFs) := by
  have hshim := hCF.shim2_rocl (prog := lsProg_587 H) (i := 587)
  have halloc := hCF.alloc_rocl (prog := lsProg_587 H) (i := 587)
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, Spec.keepsFs, session2ShimSpecX, lsProg_587] at hshim
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, Spec.keepsFs, rustAllocSpecWithStack, lsProg_587] at halloc
  unfold LibsignalPublicApi.StoreKit.withLsCodeRoLoaded Spec.keepsFs finishGrowZeroSpec2X finishGrowSpecX
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨hsz_pos, hpow, hbound⟩
  have hcap_eq : cap = 0#64 := by assumption
  have hbs_eq : bs = [] := by assumption
  subst hcap_eq
  subst hbs_eq
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := ⟨hsz_pos, hpow, hbound⟩
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  simp only [wp_norm] at hcrl2
  have ⟨hcl2, hro2⟩ := hcrl2
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

set_option maxHeartbeats 1000000 in
private theorem finish_grow_ne_blk587_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (finishGrowNeSpec2X A)) := by
  have hrealloc := hC.realloc_rocl (prog := lsProg_587 H) (i := 587)
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustReallocExternSpecWithStack, lsProg_587] at hrealloc
  unfold LibsignalPublicApi.StoreKit.withLsCodeRoLoaded finishGrowNeSpec2X finishGrowSpecX
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨hsz_pos, hpow, hbound⟩
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
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustReallocSymCli) hcrl0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs)
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
    simp only [ite_true, FinishGrowCall.oldBuf, hcap_ne, ite_false]
    wp_done

set_option maxHeartbeats 1000000 in
private theorem finish_grow_ne_fs_blk587_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hCF : AllocContractsFsPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (finishGrowNeSpec2X A).keepsFs) := by
  have hrealloc := hCF.realloc_rocl (prog := lsProg_587 H) (i := 587)
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, Spec.keepsFs,
    rustReallocExternSpecWithStack, lsProg_587] at hrealloc
  unfold LibsignalPublicApi.StoreKit.withLsCodeRoLoaded Spec.keepsFs finishGrowNeSpec2X finishGrowSpecX
  simp only [memRegion_24_p, stackAt_finishGrowX_p, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_587).rebase (blkPl_587).base H) (blkPl_587).base _
  wp_init x s0
  obtain ⟨out, cap, ptr, new, align, stride, bs⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨hsz_pos, hpow, hbound⟩
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
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustReallocSymCli) hcrl0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs)
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
    simp only [ite_true, FinishGrowCall.oldBuf, hcap_ne, ite_false]
    wp_done

/-! ## 3. Block `587` Full `finishGrowSpecX` Contracts (`cliFinishGrow_blk587_ok`, `cliFinishGrow_blk587_okFs`) -/

theorem cliFinishGrow_blk587_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (finishGrowSpecX A)) := by
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcrl, hpre0⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine finish_grow_zero_blk587_ok_x hC x R s0 hpc hrun ?_ hsp
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [finishGrowSpecX, finishGrowZeroSpec2X,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine finish_grow_ne_blk587_ok_x hC x R s0 hpc hrun ?_ hsp
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [finishGrowSpecX, finishGrowNeSpec2X,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

theorem cliFinishGrow_blk587_okFs [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hCF : AllocContractsFsPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (finishGrowSpecX A).keepsFs) := by
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcrl, hpre0⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine finish_grow_zero_fs_blk587_ok_x hCF x R s0 hpc hrun ?_ hsp
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [finishGrowSpecX, finishGrowZeroSpec2X, Spec.keepsFs,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay⟩, hmem⟩
  · refine finish_grow_ne_fs_blk587_ok_x hCF x R s0 hpc hrun ?_ hsp
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    simp only [finishGrowSpecX, finishGrowNeSpec2X, Spec.keepsFs,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay⟩, hmem⟩

/-! ## 4. `SpecRefines` Lifting & Cell-Form Corollaries (`finishGrowZeroCellsSpec`, `finishGrowNeCellsSpec`) -/

theorem SpecRefines.withLsCodeRoLoaded {α β : Type} {spec1 : Spec α} {spec2 : Spec β}
    (mpl : MultiPlacement) (href : SpecRefines spec1 spec2) :
    SpecRefines
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded mpl spec1)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded mpl spec2) := by
  intro y R s0 hpre
  obtain ⟨hinv, hpre2⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  obtain ⟨x, F, hpre1, hpost, hpan, hex, hoom⟩ := href y R s0 hpre2
  refine ⟨x, F, ?_, hpost, hpan, hex, hoom⟩
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hinv, hpre1⟩

theorem SpecRefines.apply_withLsCodeRoLoaded {α β : Type} {P : Program} {e : BitVec 64}
    {spec1 : Spec α} {spec2 : Spec β} {mpl : MultiPlacement}
    (href : SpecRefines spec1 spec2)
    (h1 : subroutine_ok P e (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded mpl spec1)) :
    subroutine_ok P e (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded mpl spec2) :=
  (href.withLsCodeRoLoaded mpl).apply_ok h1

theorem SpecRefines.apply_keepsFs_withLsCodeRoLoaded {α β : Type} {P : Program} {e : BitVec 64}
    {spec1 : Spec α} {spec2 : Spec β} {mpl : MultiPlacement}
    (href : SpecRefines spec1 spec2)
    (h1 : subroutine_ok P e (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded mpl spec1.keepsFs)) :
    subroutine_ok P e (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded mpl spec2.keepsFs) :=
  (href.withLsCodeRoLoaded mpl).apply_keepsFs h1

private theorem pull_fg0_err_p (O1 O2 O3 P A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ P ∗ A ∗ S) ∗ R = P ∗ ((A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg0_ok_p (O1 O2 O3 P L M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

private theorem pull_fg1_post_p (O1 O2 O3 P L B M A S R : SepProp) :
    (O1 ∗ O2 ∗ O3 ∗ (P ∗ L ∗ B ∗ M) ∗ A ∗ S) ∗ R =
      P ∗ ((L ∗ B ∗ M ∗ A ∗ S ∗ O1 ∗ O2 ∗ O3) ∗ R) := by ac_rfl

theorem finishGrowSpecX_refines_zeroCells (A : RustAlloc) :
    SpecRefines (finishGrowSpecX A) (GrowOne.Helpers.finishGrowZeroCellsSpec A) := by
  intro ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpre
  simp only [GrowOne.Helpers.finishGrowZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24_p, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine ⟨hcall, R, hpre0, ?_, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  intro sf hq
  simp only [finishGrowSpecX, GrowOne.Helpers.finishGrowZeroCellsSpec,
    hcall, FinishGrowCall.oldBuf, ite_true, pointsToBytes_nil, List.length_nil,
    BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
    sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
  rcases hq with ⟨tag, p', hq⟩
  refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
  by_cases htag : tag = 1#64
  · simp only [htag, ite_true] at hq ⊢
    rw [pull_fg0_err_p, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hq.1.2, hq.2⟩
  · simp only [htag, ite_false] at hq ⊢
    rw [pull_fg0_ok_p, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩

theorem finishGrowSpecX_refines_neCells (A : RustAlloc) :
    SpecRefines (finishGrowSpecX A) (GrowOne.Helpers.finishGrowNeCellsSpec A) := by
  intro ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpre
  simp only [GrowOne.Helpers.finishGrowNeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre0 : s0.mem ⊨ (finishGrowSpecX A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24_p, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine ⟨hcall, R, hpre0, ?_, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  intro sf hq
  simp only [finishGrowSpecX, GrowOne.Helpers.finishGrowNeCellsSpec,
    hcall, FinishGrowCall.oldBuf, hcap, ite_false,
    sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
  rcases hq with ⟨tag, p', hq⟩
  refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
  by_cases htag : tag = 1#64
  · simp only [htag, ite_true] at hq ⊢
    rw [pull_fg1_post_p, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
  · simp only [htag, ite_false] at hq ⊢
    rw [pull_fg1_post_p, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩

theorem finish_grow_zero_cells_blk587_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (GrowOne.Helpers.finishGrowZeroCellsSpec A)) :=
  (finishGrowSpecX_refines_zeroCells A).apply_withLsCodeRoLoaded (cliFinishGrow_blk587_ok hC)

theorem finish_grow_zero_cells_fs_blk587_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hCF : AllocContractsFsPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (GrowOne.Helpers.finishGrowZeroCellsSpec A).keepsFs) :=
  (finishGrowSpecX_refines_zeroCells A).apply_keepsFs_withLsCodeRoLoaded (cliFinishGrow_blk587_okFs hCF)

theorem finish_grow_ne_cells_blk587_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (GrowOne.Helpers.finishGrowNeCellsSpec A)) :=
  (finishGrowSpecX_refines_neCells A).apply_withLsCodeRoLoaded (cliFinishGrow_blk587_ok hC)

theorem finish_grow_ne_cells_fs_blk587_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hCF : AllocContractsFsPlaced A H) :
    subroutine_ok (lsProg_587 H) (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (GrowOne.Helpers.finishGrowNeCellsSpec A).keepsFs) :=
  (finishGrowSpecX_refines_neCells A).apply_keepsFs_withLsCodeRoLoaded (cliFinishGrow_blk587_okFs hCF)

/-! ## 5. Cross-Block Lifted Contracts (`withLsRoCl lsmpl`) -/

section CallerBlock
variable [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
  {prog : Program} {i : Nat} [IsLsBlockProg prog i H]

theorem cliFinishGrow_placed_ok_at (hC : AllocContractsXCliPlaced A H)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (finishGrowSpecX A)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (cliFinishGrow_blk587_ok hC) hi

theorem cliFinishGrow_placed_okFs_at (hCF : AllocContractsFsPlaced A H)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (finishGrowSpecX A).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (cliFinishGrow_blk587_okFs hCF) hi

theorem finish_grow_zero_cells_placed_ok_at (hC : AllocContractsXCliPlaced A H)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (GrowOne.Helpers.finishGrowZeroCellsSpec A)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (finish_grow_zero_cells_blk587_ok_x hC) hi

theorem finish_grow_zero_cells_fs_placed_ok_at (hCF : AllocContractsFsPlaced A H)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (GrowOne.Helpers.finishGrowZeroCellsSpec A).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (finish_grow_zero_cells_fs_blk587_ok_x hCF) hi

theorem finish_grow_ne_cells_placed_ok_at (hC : AllocContractsXCliPlaced A H)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (GrowOne.Helpers.finishGrowNeCellsSpec A)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (finish_grow_ne_cells_blk587_ok_x hC) hi

theorem finish_grow_ne_cells_fs_placed_ok_at (hCF : AllocContractsFsPlaced A H)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 587)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (GrowOne.Helpers.finishGrowNeCellsSpec A).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 587)
    (finish_grow_ne_cells_fs_blk587_ok_x hCF) hi

end CallerBlock

end CryptoVerification.SignalSession.Cli.MainHops
