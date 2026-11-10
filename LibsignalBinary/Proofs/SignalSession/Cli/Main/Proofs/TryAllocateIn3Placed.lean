/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSitesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Relocatable `<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` Contract

Relocatable (`[LibsignalPlacement]`) plain and `.keepsFs` contracts for `try_allocate_in [local#2]`
on Block `588`, lifted to arbitrary caller blocks via `StoreKit.withLsRoCl`.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Bin

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Arithmetic and Memory Helpers -/

private theorem umulh_stride_eq_zero_p {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
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
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_tryAllocateInX_p (sp : BitVec 64) :
    stackAt sp finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp 16384 6 (by decide)

/-! ## Base Contracts on Block `588` -/

set_option maxHeartbeats 1000000 in
private theorem tryAllocateIn3_blk588_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A H) :
    subroutine_ok (lsProg_588 H) (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (tryAllocateInSpecOf finishGrowStackX A)) := by
  have hshim := hA.shim2_rocl (prog := lsProg_588 H) (i := 588)
  have halloc := hA.alloc_rocl (prog := lsProg_588 H) (i := 588)
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, session2ShimSpecX, lsProg_588] at hshim
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustAllocSpecWithStack, lsProg_588] at halloc
  unfold LibsignalPublicApi.StoreKit.withLsCodeRoLoaded tryAllocateInSpecOf
  simp only [memRegion_24_p, stackAt_tryAllocateInX_p,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_588).rebase (blkPl_588).base H) (blkPl_588).base _
  wp_init x s0
  obtain ⟨out, new, align, stride⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨hsz_pos, hpow, hbound⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  have ⟨hcl2, hro2⟩ := hcrl2
  wp_call halloc (new.toNat * stride.toNat, align.toNat)
  wp_steps
  wp_if hoom
  · have hoom0 : sf_1.readReg64 Reg.x0 = 0 := hoom
    simp only [hoom0, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 0#64
    simp only [ite_true]
    wp_done
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done

set_option maxHeartbeats 1000000 in
private theorem tryAllocateIn3_blk588_ok_xFs [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hCF : AllocContractsFsPlaced A H) :
    subroutine_ok (lsProg_588 H) (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (tryAllocateInSpecOf finishGrowStackX A).keepsFs) := by
  have hshim := hCF.shim2_rocl (prog := lsProg_588 H) (i := 588)
  have halloc := hCF.alloc_rocl (prog := lsProg_588 H) (i := 588)
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, Spec.keepsFs, session2ShimSpecX, lsProg_588] at hshim
  dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, Spec.keepsFs, rustAllocSpecWithStack, lsProg_588] at halloc
  unfold LibsignalPublicApi.StoreKit.withLsCodeRoLoaded Spec.keepsFs tryAllocateInSpecOf
  simp only [memRegion_24_p, stackAt_tryAllocateInX_p,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_588).rebase (blkPl_588).base H) (blkPl_588).base _
  wp_init x s0
  obtain ⟨out, new, align, stride⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hlay : LayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hlay with ⟨hsz_pos, hpow, hbound⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  apply LibsignalPublicApi.StoreKit.sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  have ⟨hcl2, hro2⟩ := hcrl2
  wp_call halloc (new.toNat * stride.toNat, align.toNat)
  wp_steps
  wp_if hoom
  · have hoom0 : sf_1.readReg64 Reg.x0 = 0 := hoom
    simp only [hoom0, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 0#64
    simp only [ite_true]
    wp_done
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done

/-! ## Stack-Framed and Cross-Block Contracts -/

theorem tryAllocateIn3_blk588_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_588 H) (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (tryAllocateInSpecOf resStack A)) := by
  let F : TryAllocateInCall → State → SepProp :=
    fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - finishGrowStackX)
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp resStack =
        memRegion (sp - BitVec.ofNat 64 resStack) (resStack - finishGrowStackX) ∗
        stackAt sp finishGrowStackX := by
    intro sp
    have hsum : finishGrowStackX + (resStack - finishGrowStackX) = resStack :=
      Nat.add_sub_of_le hres
    have h1 := stackAt_split_bottom_open sp finishGrowStackX (resStack - finishGrowStackX) (by omega)
    rw [hsum] at h1
    exact h1
  refine subroutine_ok_frame_weaken F (tryAllocateIn3_blk588_ok_x hC) ?_ ?_ ?_
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro x s0
    exact ByteSlice.entails_of_eq (by
      dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, tryAllocateInSpecOf, F]
      rw [hsplit s0.sp]
      ac_rfl)
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, tryAllocateInSpecOf, F]
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro tag
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro p'
      rw [hsplit s0.sp]
      ac_rfl)
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, tryAllocateInSpecOf]
      exact pure_false_sepConj _)

theorem tryAllocateIn3_blk588_okFs [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_588 H) (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (tryAllocateInSpecOf resStack A).keepsFs) := by
  let F : TryAllocateInCall → State → SepProp :=
    fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - finishGrowStackX)
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp resStack =
        memRegion (sp - BitVec.ofNat 64 resStack) (resStack - finishGrowStackX) ∗
        stackAt sp finishGrowStackX := by
    intro sp
    have hsum : finishGrowStackX + (resStack - finishGrowStackX) = resStack :=
      Nat.add_sub_of_le hres
    have h1 := stackAt_split_bottom_open sp finishGrowStackX (resStack - finishGrowStackX) (by omega)
    rw [hsum] at h1
    exact h1
  refine subroutine_ok_frame_weaken F (tryAllocateIn3_blk588_ok_xFs hCF) ?_ ?_ ?_
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro x s0
    exact ByteSlice.entails_of_eq (by
      dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs, tryAllocateInSpecOf, F]
      rw [hsplit s0.sp]
      ac_rfl)
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs, tryAllocateInSpecOf, F]
      rw [sepConj_assoc]
      congr 1
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro tag
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro p'
      rw [hsplit s0.sp]
      ac_rfl)
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, Spec.keepsFs, tryAllocateInSpecOf]
      exact pure_false_sepConj _)

/-- Cross-block `tryAllocateIn3` contract for any caller block `prog` (`IsLsBlockProg prog i H`). -/
theorem tryAllocateIn3_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    {resStack : Nat} (hC : AllocContractsXCliPlaced A H)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (tryAllocateInSpecOf resStack A)) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 588)
    (tryAllocateIn3_blk588_ok hC hres hres64) hi

/-- Cross-block `.keepsFs` `tryAllocateIn3` contract for any caller block `prog`. -/
theorem tryAllocateIn3_placed_okFs_at [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    {resStack : Nat} (hCF : AllocContractsFsPlaced A H)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (tryAllocateInSpecOf resStack A).keepsFs) :=
  LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block (i := i) (j := 588)
    (tryAllocateIn3_blk588_okFs hCF hres hres64) hi

theorem tryAllocateIn3_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (tryAllocateInSpecOf resStack A)) :=
  tryAllocateIn3_placed_ok_at (prog := lsProg_617 H) (i := 617) hC hres hres64

theorem tryAllocateIn3_placed_okFs [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {resStack : Nat}
    (hCF : AllocContractsFsPlaced A H)
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_617 H) (lsmpl.base 588)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (tryAllocateInSpecOf resStack A).keepsFs) :=
  tryAllocateIn3_placed_okFs_at (prog := lsProg_617 H) (i := 617) hCF hres hres64

end CryptoVerification.SignalSession.Cli.MainHops
