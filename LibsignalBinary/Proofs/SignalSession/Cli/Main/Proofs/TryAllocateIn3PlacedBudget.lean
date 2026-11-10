/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3Placed
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers

/-!
# Budget-Threaded Relocatable `try_allocate_in [local#2]` Contract

Total-correctness (`RustCliAllocBudget`) plain and `.keepsFs` contracts for
`<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` on Block `588` under
`[LibsignalPlacement]`, lifted cross-block via `StoreKit.withLsRoCl`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3PlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded ls_subroutine_ok_rocl_of_block sepWP_seq_lscro withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack finishGrowStackX)
open CryptoVerification.E2E.Pqxdh.Shared (TryAllocateInCall)
open CryptoVerification.E2E.Bin (stackAt_split_bottom_open)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (subroutine_ok_frame_weaken)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_588 blkPl_588 lsProg_588)
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize MaxAlignedAllocAlign mallocngAlignedEffSize)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents OomPreserved RustCliAllocBudget
   RustLayoutOk VmPreserved not_nullAllowed_of_fitsAllocEvents rustAllocEvents
   rustCliAllocBudgetExternSpecWithStack rustCliAllocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (shimSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (TryAllocateInEnv fitsEvents_tryAllocateIn_of_fitsEnv tryAllocateInCondSpecOf
   tryAllocateInEnv_events tryAllocateInEvents tryAllocateInSpecOf)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

/-- Total-correctness (`FitsEnv`) contract for `try_allocate_in` under `RustLayoutOk` (`x.align.toNat ≤ 2 ^ 31`). -/
def tryAllocateInRustSpecOf {M : AllocCostModel} (resStack : Nat) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryAllocateInCall × M.σ) :=
  { tryAllocateInSpecOf resStack A lim with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
        s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
        0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
        FitsEnv M lim st (TryAllocateInEnv x)⌝ ∗
      memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp resStack }

theorem tryAllocateInSpecOf_pre_to_rust {M : AllocCostModel} {resStack : Nat}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (x : TryAllocateInCall) (st : M.σ)
    (halign : x.align.toNat ≤ 2 ^ 31) (s : State) (R : SepProp)
    (h : s.mem ⊨ (tryAllocateInSpecOf resStack A lim).pre (x, st) s ∗ R) :
    s.mem ⊨ (tryAllocateInRustSpecOf resStack A lim).pre (x, st) s ∗ R := by
  dsimp only [tryAllocateInSpecOf, tryAllocateInRustSpecOf] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨⟨hx0, hx1, hx2, hx3, hnew, hstr, hlay, hfit⟩, hm⟩
  exact ⟨⟨hx0, hx1, hx2, hx3, hnew, hstr, ⟨hlay, halign⟩, hfit⟩, hm⟩

private theorem instantiate_post_exists {α : Sort _} {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp} {Q : α → State → SepProp} {oom : State → SepProp}
    (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Q w sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom) :
    SepWP prog target_pc s P (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (∃∗ a, Q a sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  refine SepWP.mono h fun sf P_f _ _ ⟨hq, hsp, hcs⟩ => ⟨fun hm => ?_, hsp, hcs⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨w, hq hm⟩

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
theorem tryAllocateIn3_blk588_ok_x_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_588 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_588 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack))) :
    subroutine_ok (lsProg_588 H) (lsmpl.base 588)
      (withLsCodeRoLoaded lsmpl (tryAllocateInRustSpecOf finishGrowStackX A lim)) := by
  dsimp only [withLsRoCl, shimSpecWithStack, lsProg_588] at hshim
  simp only [withLsRoCl, rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    Bool.false_eq_true, ↓reduceIte, lsProg_588] at halloc
  unfold withLsCodeRoLoaded tryAllocateInRustSpecOf tryAllocateInSpecOf
  simp only [memRegion_24_p, stackAt_tryAllocateInX_p,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_588).rebase (blkPl_588).base H) (blkPl_588).base _
  wp_init x s0
  obtain ⟨⟨out, new, align, stride⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  have hfitEnv : FitsEnv M lim st (TryAllocateInEnv ⟨out, new, align, stride⟩) := by assumption
  have hfit : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) :=
    fitsEvents_tryAllocateIn_of_fitsEnv M lim st ⟨out, new, align, stride⟩ hfitEnv
  rcases hrlay with ⟨⟨hsz_pos, _hpow, hbound⟩, _halign⟩
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := ⟨⟨hsz_pos, _hpow, hbound⟩, _halign⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  change SepWP (lsProg_588 H) _ _ _ _ _
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl1
  change SepWP ((blkPC_588).rebase (blkPl_588).base H) _ _ _ _ _
  wp_call hshim ()
  apply ProofLib.SepWP.transport_budgetPool (by assumption)
  change SepWP (lsProg_588 H) _ _ _ _ _
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  have ⟨hcl2, hro2⟩ := hcrl2
  change SepWP ((blkPC_588).rebase (blkPl_588).base H) _ _ _ _ _
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hret_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by tauto)
  change SepWP (lsProg_588 H) _ _ _ _ _
  wp_steps_sync_pool (s0.readReg64 Reg.x30)
  apply instantiate_post_exists (tryAllocateInEvents ⟨out, new, align, stride⟩)
  apply instantiate_post_exists (sf_1.readReg64 Reg.x0)
  have hev : TryAllocateInEnv ⟨out, new, align, stride⟩
      (tryAllocateInEvents ⟨out, new, align, stride⟩) :=
    tryAllocateInEnv_events _
  wp_done

set_option maxHeartbeats 1000000 in
theorem tryAllocateIn3_blk588_ok_xFs_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok (lsProg_588 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_588 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs)) :
    subroutine_ok (lsProg_588 H) (lsmpl.base 588)
      (withLsCodeRoLoaded lsmpl (tryAllocateInRustSpecOf finishGrowStackX A lim).keepsFs) := by
  dsimp only [withLsRoCl, Spec.keepsFs, shimSpecWithStack, lsProg_588] at hshim
  simp only [withLsRoCl, Spec.keepsFs, rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    Bool.false_eq_true, ↓reduceIte, lsProg_588] at halloc
  unfold withLsCodeRoLoaded Spec.keepsFs tryAllocateInRustSpecOf tryAllocateInSpecOf
  simp only [memRegion_24_p, stackAt_tryAllocateInX_p,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  change subroutine_ok ((blkPC_588).rebase (blkPl_588).base H) (blkPl_588).base _
  wp_init x s0
  obtain ⟨⟨out, new, align, stride⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  have hfitEnv : FitsEnv M lim st (TryAllocateInEnv ⟨out, new, align, stride⟩) := by assumption
  have hfit : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) :=
    fitsEvents_tryAllocateIn_of_fitsEnv M lim st ⟨out, new, align, stride⟩ hfitEnv
  rcases hrlay with ⟨⟨hsz_pos, _hpow, hbound⟩, _halign⟩
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := ⟨⟨hsz_pos, _hpow, hbound⟩, _halign⟩
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero_p hlt64
  have hhi := hi_stride_eq_false_p hbound
  have hcbz := beq_mul_stride_zero_eq_false_p hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat_p hlt64
  change SepWP (lsProg_588 H) _ _ _ _ _
  apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl1
  simp only [wp_norm] at hcrl1
  have ⟨hcl1, hro1⟩ := hcrl1
  apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl1
  change SepWP ((blkPC_588).rebase (blkPl_588).base H) _ _ _ _ _
  wp_call hshim ()
  apply ProofLib.SepWP.transport_budgetPool (by assumption)
  change SepWP (lsProg_588 H) _ _ _ _ _
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcrl2
  simp only [wp_norm] at hcrl2
  have ⟨hcl2, hro2⟩ := hcrl2
  change SepWP ((blkPC_588).rebase (blkPl_588).base H) _ _ _ _ _
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hret_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (by tauto)
  change SepWP (lsProg_588 H) _ _ _ _ _
  wp_steps_sync_pool (s0.readReg64 Reg.x30)
  apply instantiate_post_exists (tryAllocateInEvents ⟨out, new, align, stride⟩)
  apply instantiate_post_exists (sf_1.readReg64 Reg.x0)
  have hev : TryAllocateInEnv ⟨out, new, align, stride⟩
      (tryAllocateInEvents ⟨out, new, align, stride⟩) :=
    tryAllocateInEnv_events _
  wp_done

/-! ## Stack-Framed and Cross-Block Contracts -/

theorem tryAllocateIn3_blk588_ok_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hshim : subroutine_ok (lsProg_588 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_588 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_588 H) (lsmpl.base 588)
      (withLsCodeRoLoaded lsmpl (tryAllocateInRustSpecOf resStack A lim)) := by
  let F : TryAllocateInCall × M.σ → State → SepProp :=
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
  refine subroutine_ok_frame_weaken F (tryAllocateIn3_blk588_ok_x_of_hooks hshim halloc) ?_ ?_ ?_
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro x s0
    exact ByteSlice.entails_of_eq (by
      dsimp only [withLsCodeRoLoaded, tryAllocateInRustSpecOf, tryAllocateInSpecOf, F]
      rw [hsplit s0.sp]
      sep_ac_rfl)
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [withLsCodeRoLoaded, tryAllocateInRustSpecOf, tryAllocateInSpecOf, F]
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro evs
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro p'
      rw [hsplit s0.sp]
      sep_ac_rfl)
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [withLsCodeRoLoaded, tryAllocateInRustSpecOf, tryAllocateInSpecOf]
      exact pure_false_sepConj _)

theorem tryAllocateIn3_blk588_okFs_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {resStack : Nat}
    (hshim : subroutine_ok (lsProg_588 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_588 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs))
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (lsProg_588 H) (lsmpl.base 588)
      (withLsCodeRoLoaded lsmpl (tryAllocateInRustSpecOf resStack A lim).keepsFs) := by
  let F : TryAllocateInCall × M.σ → State → SepProp :=
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
  refine subroutine_ok_frame_weaken F (tryAllocateIn3_blk588_ok_xFs_of_hooks hshim halloc) ?_ ?_ ?_
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · intro x s0
    exact ByteSlice.entails_of_eq (by
      dsimp only [withLsCodeRoLoaded, Spec.keepsFs, tryAllocateInRustSpecOf, tryAllocateInSpecOf, F]
      rw [hsplit s0.sp]
      sep_ac_rfl)
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [withLsCodeRoLoaded, Spec.keepsFs, tryAllocateInRustSpecOf, tryAllocateInSpecOf, F]
      rw [sepConj_assoc]
      congr 1
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro evs
      rw [sepExists_sepConj_left]
      apply sepExists_congr; intro p'
      rw [hsplit s0.sp]
      sep_ac_rfl)
  · intro x s0 sf
    exact ByteSlice.entails_of_eq (by
      dsimp only [withLsCodeRoLoaded, Spec.keepsFs, tryAllocateInRustSpecOf, tryAllocateInSpecOf]
      exact pure_false_sepConj _)

theorem tryAllocateIn3_placed_ok_of_hooks_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    {resStack : Nat}
    (hshim : subroutine_ok (lsProg_588 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack)))
    (halloc : subroutine_ok (lsProg_588 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)))
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 588)
      (withLsRoCl lsmpl (tryAllocateInRustSpecOf resStack A lim)) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 588)
    (tryAllocateIn3_blk588_ok_of_hooks hshim halloc hres hres64) hi

theorem tryAllocateIn3_placed_okFs_of_hooks_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {prog : Program} {i : Nat} [IsLsBlockProg prog i H]
    {resStack : Nat}
    (hshim : subroutine_ok (lsProg_588 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsRoCl lsmpl (shimSpecWithStack extHookStack).keepsFs))
    (halloc : subroutine_ok (lsProg_588 H) (lsρ lsRustAllocSymCli)
      (withLsRoCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack).keepsFs))
    (hres : finishGrowStackX ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 588)
      (withLsRoCl lsmpl (tryAllocateInRustSpecOf resStack A lim).keepsFs) :=
  ls_subroutine_ok_rocl_of_block (i := i) (j := 588)
    (tryAllocateIn3_blk588_okFs_of_hooks hshim halloc hres hres64) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3PlacedBudget
