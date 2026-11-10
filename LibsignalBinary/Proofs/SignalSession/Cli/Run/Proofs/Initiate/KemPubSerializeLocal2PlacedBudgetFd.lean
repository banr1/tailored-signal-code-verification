/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Budget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Placed
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.RegChain

/-!
# Filesystem- and FD-Preserving Relocatable Proof of `<kem::Key<Public>>::serialize [local#1]`

Lifts the budget-threaded `[LibsignalPlacement]` contracts for `<kem::Key<Public>>::serialize [local#1]`
(block `523`) to `.keepsFs` and `withFdsGe3Closed` across caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2PlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl)
open CryptoVerification.CliHandshake.Placed (blkPC_523 blkPl_523 lsProg_523)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_plain
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.RustHeap (LayoutOk)
open CryptoVerification.SignalSession
  (CliHooks lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.KemPubSerializeLocal2
  (kemPubSerFixedStk)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved rustAllocEvents subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomSpecWithStack subroutine_ok_rustCliAllocNoOom_withStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (subroutine_ok_withFdsGe3Closed_of_keepsFs
   subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Budget
  (kemPubSerializeFullAtStkSpec kemPubSerializeValAtStkSpec)

private theorem stackAt_kemPubSerFixed_placed_fd (sp : BitVec 64) :
    stackAt sp kemPubSerFixedStk =
      stackAt (sp - 48#64) extHookStack ∗ ProofLib.cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_1569_split_placed_fd (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), ProofLib.memRegion_one]

private theorem sp_sub_48_add_48_placed_fd (sp : BitVec 64) : (sp - 48#64) + 48#64 = sp := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sp_sub_48_add_48_placed_fd BitVec.toNat_zero

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1200000 in
theorem kemPubKeySerialize_local2_fixed_keepsFs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {W : CliHooks} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H) :
    subroutine_ok (lsProg_523 H) (blkPl_523).base
      (kemPubSerializeValAtStkSpec M A lim kemPubSerFixedStk).keepsFs := by
  have hshim : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ lsRustNoAllocShimSymCli)
      rustAllocShimVmSpec :=
    ls_hook_ok_ultra_of_mem hh.shimVm
  have halloc : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ lsRustAllocSymCli)
      (rustCliAllocNoOomSpecWithStack M A lim false extHookStack) :=
    subroutine_ok_rustCliAllocNoOom_withStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_ultra_of_mem hh.rawAlloc))
  have hmemcpy : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ memcpyName)
      allocMemcpyVmSpec :=
    ls_hook_ok_ultra_of_mem hh.allocMemcpyVm
  clear hh
  dsimp only [rustAllocShimVmSpec] at hshim
  dsimp only [allocMemcpyVmSpec] at hmemcpy
  simp only [Spec.keepsFs, kemPubSerializeValAtStkSpec, stackAt_kemPubSerFixed_placed_fd]
  cells_unfold
  dsimp only [lsProg_523] at hshim halloc hmemcpy ⊢
  wpp_init g s0
  obtain ⟨⟨boxPtr, pkBytes⟩, st⟩ := g
  dsimp only at *
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  have hrlay : RustLayoutOk 1569 1 := ⟨hlay, by decide⟩
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_523).ρ lsRustNoAllocShimSymCli)
  wp_call hshim ()
  have htr_sf : sf.trace = s0.trace := (‹AllocCallPreserved _ sf›).2.1
  have hfs_sf : sf.fs = s0.fs := (‹AllocCallPreserved _ sf›).1
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool ((blkPl_523).ρ lsRustAllocSymCli)
  wp_call halloc (1569, 1, st)
  have htr_sf1 : sf_1.trace = s0.trace :=
    (‹AllocCallPreserved _ sf_1›).2.1.trans htr_sf
  have hfs_sf1 : sf_1.fs = s0.fs :=
    (‹AllocCallPreserved _ sf_1›).1.trans hfs_sf
  have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  simp only [memRegion_1569_split_placed_fd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  rename_i b0
  wp_steps_sync_pool ((blkPl_523).ρ memcpyName)
  have hlen_lt : pkBytes.length < 2 ^ 64 := by rw [‹pkBytes.length = 1568›]; decide
  rw [← ‹pkBytes.length = 1568›]
  wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, pkBytes)
  have htr_sf2 : sf_2.trace = s0.trace :=
    (‹AllocCallPreserved _ sf_2›).2.1.trans htr_sf1
  have hfs_sf2 : sf_2.fs = s0.fs :=
    (‹AllocCallPreserved _ sf_2›).1.trans hfs_sf1
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [pointsToBytes_cons]
  wp_done

private theorem memRegion_bound_of_pointsTo64_placed_fd {m : Memory} {b a v : BitVec 64} {n : Nat}
    {R : SepProp} (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

private theorem stackAt_sub_split_placed_fd (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

theorem kemPubKeySerialize_local2_full_keepsFs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {W : CliHooks} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_523 H) (lsmpl.base 523)
      (kemPubSerializeFullAtStkSpec M A lim stk).keepsFs := by
  refine subroutine_ok.of_codeLoaded fun ((keyRef, kpkPtr, kpk), st) R s0 hpc hrun hpre hsp _hL => ?_
  have hle : kemPubSerFixedStk ≤ stk := by
    dsimp [kemPubSerFixedStk]; omega
  have hbound_mem : s0.mem ⊨ memRegion (s0.sp - BitVec.ofNat 64 stk) stk ∗
      ((keyRef ↦₆₄ kpkPtr) ∗
       (⌜s0.readReg64 .x0 = kpkPtr ∧ s0.readReg64 .x1 = 1568#64 ∧ kpk.length = 1568 ∧
          FitsEvents M lim st (rustAllocEvents 1569 1)⌝ ∗
        ((keyRef + 8#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ kpk) ∗ A.pool lim st s0 ∗ R)) := by
    dsimp only [Spec.keepsFs, kemPubSerializeFullAtStkSpec, stackAt] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  have hhi : stk ≤ 2 ^ 64 := memRegion_bound_of_pointsTo64_placed_fd hbound_mem
  have hsplit := stackAt_sub_split_placed_fd s0.sp hle hhi
  let F : SepProp :=
    (keyRef ↦₆₄ kpkPtr) ∗ ((keyRef + 8#64) ↦₆₄ 1568#64) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kemPubSerFixedStk)
  have hpre' : s0.mem ⊨ (kemPubSerializeValAtStkSpec M A lim kemPubSerFixedStk).keepsFs.pre
      ((kpkPtr, kpk), st) s0 ∗ (F ∗ R) := by
    dsimp only [Spec.keepsFs, kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine (kemPubKeySerialize_local2_fixed_keepsFs_placed_ok hh).mono_outcome
    ((kpkPtr, kpk), st) (F ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_hpan, hpost⟩ | ⟨_code, _hex, hpost⟩ | ⟨_hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.keepsFs, kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · dsimp only [Spec.keepsFs, kemPubSerializeValAtStkSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact hpost.1.elim
  · exact (allowPanic_not_exited hpost).elim
  · dsimp only [Spec.keepsFs, kemPubSerializeValAtStkSpec] at hpost
    rw [satisfies_pure_sepConj] at hpost
    exact hpost.1.elim

/-- Caller-block transfer of `.keepsFs` fixed-stack `<kem::Key<Public>>::serialize [local#1]`. -/
theorem kemPubKeySerialize_local2_fixed_keepsFs_rocl_ok [LibsignalPlacement]
    {prog : Program} {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {W : CliHooks} {H : LibsignalHooks}
    [IsLsBlockProg prog i H]
    (hh : RunHooksPlaced W A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 523)
      (withLsCodeRoLoaded lsmpl
        (kemPubSerializeValAtStkSpec M A lim kemPubSerFixedStk)).keepsFs := by
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (kemPubKeySerialize_local2_fixed_keepsFs_placed_ok hh)) hi
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [Spec.keepsFs, withLsRoCl, withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq.2)

/-- Caller-block transfer of `.keepsFs` variable-stack `<kem::Key<Public>>::serialize [local#1]`. -/
theorem kemPubKeySerialize_local2_full_keepsFs_rocl_ok [LibsignalPlacement]
    {prog : Program} {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {W : CliHooks} {H : LibsignalHooks}
    [IsLsBlockProg prog i H]
    (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 523)
      (withLsCodeRoLoaded lsmpl (kemPubSerializeFullAtStkSpec M A lim stk)).keepsFs := by
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (kemPubKeySerialize_local2_full_keepsFs_placed_ok hh hstk)) hi
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [Spec.keepsFs, withLsRoCl, withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq.2)

/-- Caller-block `withFdsGe3Closed` fixed-stack contract for `<kem::Key<Public>>::serialize [local#1]`. -/
theorem kemPubKeySerialize_local2_fixed_fds_rocl_ok [LibsignalPlacement]
    {prog : Program} {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {W : CliHooks} {H : LibsignalHooks}
    [IsLsBlockProg prog i H]
    (hh : RunHooksPlaced W A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 523)
      (withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (kemPubSerializeValAtStkSpec M A lim kemPubSerFixedStk))) :=
  subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs
    (kemPubKeySerialize_local2_fixed_keepsFs_rocl_ok hh hi)

/-- Caller-block `withFdsGe3Closed` variable-stack contract for `<kem::Key<Public>>::serialize [local#1]`. -/
theorem kemPubKeySerialize_local2_full_fds_rocl_ok [LibsignalPlacement]
    {prog : Program} {i : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {W : CliHooks} {H : LibsignalHooks}
    [IsLsBlockProg prog i H]
    (hh : RunHooksPlaced W A lim H)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 523)
      (withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (kemPubSerializeFullAtStkSpec M A lim stk))) :=
  subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs
    (kemPubKeySerialize_local2_full_keepsFs_rocl_ok hh hstk hi)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2PlacedBudgetFd

end
