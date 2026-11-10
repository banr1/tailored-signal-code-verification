/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudgetAux
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure

/-!
# Budget-Threaded Relocatable Drop Glue Proof for `Stores`

Proves the `RustCliAllocBudget M` contract `dropStoresSpecPlaced` for
`core::ptr::drop_glue::<Stores>` on block `550` under `[LibsignalPlacement]`, and transfers it to
caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (arrayAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (dirAt dirEntryAt)
open CryptoVerification.SignalSession.Cli.MainHops (storesAt)
open CryptoVerification.SignalSession.Cli.Placed (
  blkLib_550 blkPl_550 instIsLsBlockProg_549 instIsLsBlockProg_550 lsProg_549 lsProg_550
)
open CryptoVerification.SignalSession.Cli.Put.Helpers (stackAt_sub_split)
open CryptoVerification.SignalSession.Cli.RunProofs (DropDirPairGhost DropStoresGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Helpers (
  Saved48Preserved add_32_add_48 add_32_neg_24 add_32_neg_24_assoc add_32_neg_32
  add_32_neg_32_assoc add_32_neg_8 add_32_neg_8_assoc add_32_sub_24 add_32_sub_24_assoc
  add_32_sub_32 add_32_sub_32_assoc add_32_sub_8 add_32_sub_8_assoc add_one_sub_one
  dirRawAt dirRawAt_expose_off exists_two_pow_eight exists_two_pow_one idExactStk mul_48_reg
  ofNat_beq_zero_false pos_of_beq_zero_false post_dir_loop_weaken_off reg_fp_eq reg_lr_eq
  reg_x0_eq reg_x19_eq reg_x1_eq reg_x20_eq reg_x21_eq reg_x22_eq reg_x23_eq reg_x24_eq
  reg_x25_eq reg_x26_eq reg_x27_eq reg_x28_eq reg_x2_eq roPathAt
  stackAt_id_split_bottom stackAt_stores_split storesExactStk stores_cap0_ret_weaken
  stores_entry_raw_ro stores_tail_dealloc_post stores_tail_dealloc_pre_weaken
  sub_24_of_add_32 sub_32_of_add_32 sub_8_of_add_32 weaken_perm
)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget RustLayoutOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresBudget (
  dropDirPairSpec dropStoresSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudgetAux (
  cliDropIdentityFiles_placed_ok dropDirPairSpecPlaced dropStoresRawSpecPlaced
  dropStoresSpecPlaced freeOnlyPool freeOnlyPool_keep freeOnlyPool_step_dealloc
  freeOnlyPool_step_evs sepWP_let_state seq_cleanX_placed stores_dir_onetime_placed
  stores_dir_sessions_placed stores_dir_signed_placed stores_loop3_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudgetAux (
  dropStoresSpecPlaced dropDirPairSpecPlaced cliDropIdentityFiles_placed_ok
)

section DropStoresMainPlacedBudget

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] exists_two_pow_one exists_two_pow_eight
attribute [local wp_norm, local arm64_norm]
  sub_32_of_add_32 sub_24_of_add_32 sub_8_of_add_32
  add_32_sub_32 add_32_sub_32_assoc add_32_sub_24 add_32_sub_24_assoc
  add_32_sub_8 add_32_sub_8_assoc
  add_32_neg_32 add_32_neg_32_assoc add_32_neg_24 add_32_neg_24_assoc
  add_32_neg_8 add_32_neg_8_assoc add_one_sub_one
attribute [local simp, local wp_norm, local arm64_norm]
  reg_x0_eq reg_x1_eq reg_x2_eq reg_x19_eq reg_x20_eq reg_x21_eq reg_x22_eq
  reg_x23_eq reg_x24_eq reg_x25_eq reg_x26_eq reg_x27_eq reg_x28_eq
  reg_fp_eq reg_lr_eq

private def dropDirPairFreePoolSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropDirPairGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      dirAt A.repAlloc x.a x.d0 ∗ dirAt A.repAlloc (x.a + 0x28#64) x.d1 ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 80 ∗ freeOnlyPool A lim st sf ∗ stackAt s0.sp stk

private theorem freeOnlyPool_join {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (evs₁ : List AllocEvent)
    (h1 : ∀ ev ∈ evs₁, ∃ al sz, ev = .free al sz) :
    freeOnlyPool A lim (M.stepEvents evs₁ st) s ⊢ freeOnlyPool A lim st s := by
  nth_rw 1 [freeOnlyPool]
  apply Entails.sepExists_elim; intro evs₂
  apply Entails.pure_left; intro h2
  exact freeOnlyPool_step_evs A lim st s evs₁ evs₂ h1 h2

set_option maxHeartbeats 1600000 in
private theorem cliDropStores_placed_ok_exact [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_550 H) (blkPl_550).base (dropStoresRawSpecPlaced M A lim) := by
  unfold dropStoresRawSpecPlaced withLsCodeRoLoaded
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_550 H) hA
  have hid0 : subroutine_ok (lsProg_550 H) (lsmpl.base 549)
      (dropDirPairSpecPlaced M A lim idExactStk) :=
    ls_transfer_lscro (callerProg := lsProg_550 H) (j := 549)
      (cliDropIdentityFiles_placed_ok hA idExactStk (le_refl _) (by decide)) (by decide)
  have hid : subroutine_ok (lsProg_550 H) (lsmpl.base 549)
      (withLsCodeRoLoaded lsmpl (dropDirPairFreePoolSpec M A lim idExactStk)) := by
    refine subroutine_ok_mono hid0 (fun _ _ _ h => h) ?_
    intro ⟨x, st⟩ R s0 sf hpost
    dsimp only [dropDirPairSpecPlaced, withLsCodeRoLoaded, dropDirPairSpec,
      dropDirPairFreePoolSpec] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply Entails.sepExists_elim; intro evs
    apply Entails.pure_left; rintro ⟨htr, hevs⟩
    refine Entails.pure_right htr ?_
    exact sepConj_mono_right (sepConj_mono_left (freeOnlyPool_keep A lim st sf evs hevs))
  clear hid0
  have hsigned := fun st => stores_dir_signed_placed hA st
  have honetime := fun st => stores_dir_onetime_placed hA st
  have hsessions := fun st => stores_dir_sessions_placed hA st
  have hloop3 := fun st => stores_loop3_placed hA st
  clear hA
  dsimp only [withLsCodeRoLoaded, lsProg_550, RustCliAllocBudget.live, ↓reduceIte,
    dropDirPairSpecPlaced, dropDirPairFreePoolSpec, dropDirPairSpec, BitVec.ofNat_eq_ofNat]
    at hdealloc hid hsigned honetime hsessions hloop3 ⊢
  wp_init x s0
  obtain ⟨⟨a, g⟩, st⟩ := x
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := ‹_›
  subst ‹s0.readReg64 _ = a›
  set p0 := s0.readReg64 (Reg.gpr 0#5)
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_stores_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine seq_cleanX_placed
    (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 0 + 4#64))
    (P_mid := fun sm => memRegion p0 80 ∗
      dirRawAt A.repAlloc (p0 + 80#64) g.signed.changed ∗
      dirAt A.repAlloc (p0 + 120#64) g.kyber.oneTime ∗
      dirAt A.repAlloc (p0 + 160#64) g.kyber.lastResort ∗
      dirRawAt A.repAlloc (p0 + 200#64) g.oneTime.changed ∗
      dirRawAt A.repAlloc (p0 + 240#64) g.sessions.changed ∗
      dirRawAt A.repAlloc (p0 + 280#64) g.pub.changed ∗
      freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) idExactStk ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
    hcrl0 ?_ ?_
  · apply sepWP_seq_lscro (mid := lsmpl.base 549) hcrl0
    wp_steps_sync_pool (lsmpl.base 549)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_c0
    have ⟨hcl_c0, hro_c0⟩ := hcrl_c0
    wp_call hid (DropDirPairGhost.mk p0 g.identity.own g.identity.peers, st)
    try wp_done
  ·
    intro s1 hpc1 hrun1 hcrl1 hq1
    rw [stackAt_id_split_bottom (s0.sp - 48#64)]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      dirRawAt A.repAlloc (p0 + 80#64) g.signed.changed ∗ freeOnlyPool A lim st s1 ∗
      stackAt (s0.sp - 48#64) extHookStack ∗
      (memRegion p0 80 ∗
        dirAt A.repAlloc (p0 + 120#64) g.kyber.oneTime ∗
        dirAt A.repAlloc (p0 + 160#64) g.kyber.lastResort ∗
        dirRawAt A.repAlloc (p0 + 200#64) g.oneTime.changed ∗
        dirRawAt A.repAlloc (p0 + 240#64) g.sessions.changed ∗
        dirRawAt A.repAlloc (p0 + 280#64) g.pub.changed ∗
        memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by sep_ac_rfl)) ?_
    refine seq_cleanX_placed
      (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 3 + 4#64))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
      hcrl1
      (hsigned st s0 (s0.sp - 48#64) p0 hfsp_align g.signed.changed s1 _
        hpc1 hrun1 hcrl1 hq1.1 hq1.2) ?_
    intro s2 hpc2 hrun2 hcrl2
      ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    have hp0_160 : p0 + 160#64 = (p0 + 120#64) + 40#64 := by bv_omega
    rw [hp0_160]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      dirAt A.repAlloc (p0 + 120#64) g.kyber.oneTime ∗
      dirAt A.repAlloc ((p0 + 120#64) + 40#64) g.kyber.lastResort ∗
      freeOnlyPool A lim st s2 ∗
      (memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗ stackAt (s0.sp - 48#64) extHookStack) ∗
      (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗
        dirRawAt A.repAlloc (p0 + 200#64) g.oneTime.changed ∗
        dirRawAt A.repAlloc (p0 + 240#64) g.sessions.changed ∗
        dirRawAt A.repAlloc (p0 + 280#64) g.pub.changed ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by sep_ac_rfl)) ?_
    rw [← stackAt_id_split_bottom (s0.sp - 48#64)]
    refine seq_cleanX_placed
      (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 4 + 4#64))
      (P_mid := fun sm => memRegion (p0 + 120#64) 80 ∗ freeOnlyPool A lim st sm ∗
        stackAt (s0.sp - 48#64) idExactStk ∗
        (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗
          dirRawAt A.repAlloc (p0 + 200#64) g.oneTime.changed ∗
          dirRawAt A.repAlloc (p0 + 240#64) g.sessions.changed ∗
          dirRawAt A.repAlloc (p0 + 280#64) g.pub.changed ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
      hcrl2 ?_ ?_
    · conv => arg 4; dsimp only [freeOnlyPool]
      wp_pull_exists; rename_i evs_pre2
      refine SepWP.focus_pure (by sep_focus) fun hevs_pre2 => ?_
      apply sepWP_seq_lscro (mid := lsmpl.base 549) hcrl2
      wp_steps_sync_pool (lsmpl.base 549)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl_c2
      have ⟨hcl_c2, hro_c2⟩ := hcrl_c2
      wp_call hid
        (DropDirPairGhost.mk (p0 + 120#64) g.kyber.oneTime g.kyber.lastResort,
          M.stepEvents evs_pre2 st)
      try rw [hsp_2]
      apply SepWP.fold (freeOnlyPool_join A lim st _ evs_pre2 hevs_pre2) (by sep_focus)
      try wp_done
    ·
      intro s3 hpc3 hrun3 hcrl3 hq3
      rw [stackAt_id_split_bottom (s0.sp - 48#64)]
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A.repAlloc (p0 + 200#64) g.oneTime.changed ∗ freeOnlyPool A lim st s3 ∗
        stackAt (s0.sp - 48#64) extHookStack ∗
        (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
          dirRawAt A.repAlloc (p0 + 240#64) g.sessions.changed ∗
          dirRawAt A.repAlloc (p0 + 280#64) g.pub.changed ∗
          memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by sep_ac_rfl)) ?_
      refine seq_cleanX_placed
        (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 7 + 4#64))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
        hcrl3
        (honetime st s0 (s0.sp - 48#64) p0 hfsp_align g.oneTime.changed s3 _
          hpc3 hrun3 hcrl3 hq3.1 hq3.2) ?_
      intro s4 hpc4 hrun4 hcrl4 hq4
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A.repAlloc (p0 + 240#64) g.sessions.changed ∗ freeOnlyPool A lim st s4 ∗
        stackAt (s0.sp - 48#64) extHookStack ∗
        (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
          memRegion (p0 + 200#64) 40 ∗
          dirRawAt A.repAlloc (p0 + 280#64) g.pub.changed ∗
          memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by sep_ac_rfl)) ?_
      refine seq_cleanX_placed
        (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "bl" 10 + 4#64))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = p0)
        hcrl4
        (hsessions st s0 (s0.sp - 48#64) p0 hfsp_align g.sessions.changed s4 _
          hpc4 hrun4 hcrl4 hq4.1 hq4.2) ?_
      intro s5 hpc5 hrun5 hcrl5
        ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
      have ho7_8 : (p0 + 280#64) + 8#64 = p0 + 288#64 := by bv_omega
      have ho7_16 : (p0 + 280#64) + 16#64 = p0 + 296#64 := by bv_omega
      have ho7_24 : (p0 + 280#64) + 24#64 = p0 + 304#64 := by bv_omega
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A.repAlloc (p0 + 280#64) g.pub.changed ∗
        (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
          memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
          freeOnlyPool A lim st s5 ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          stackAt (s0.sp - 48#64) extHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by sep_ac_rfl)) ?_
      refine SepWP.weaken_pre
        (sepConj_mono_left
          (dirRawAt_expose_off A.repAlloc p0 280#64 288#64 296#64 304#64
            ho7_8 ho7_16 ho7_24 g.pub.changed)) ?_
      wp_pull_exists
      rename_i cap7 ptr7
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ⌜g.pub.changed.length ≤ cap7.toNat ∧ cap7.toNat * 48 < 2 ^ 63 ∧
          g.pub.changed.length * 48 < 2 ^ 63 ∧ ptr7 ≠ 0⌝ ∗
        (((p0 + 280#64) ↦₆₄ cap7) ∗ ((p0 + 288#64) ↦₆₄ ptr7) ∗
          ((p0 + 296#64) ↦₆₄ BitVec.ofNat 64 g.pub.changed.length) ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr7 g.pub.changed ∗
          (if cap7 = 0 then emp
           else A.repAlloc.live ptr7 (cap7.toNat * 48) 8 ∗
             memRegion (ptr7 + BitVec.ofNat 64 (g.pub.changed.length * 48))
               ((cap7.toNat - g.pub.changed.length) * 48)) ∗
          memRegion (p0 + 304#64) 16 ∗
          (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
            memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
            freeOnlyPool A lim st s5 ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
            stackAt (s0.sp - 48#64) extHookStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) by sep_ac_rfl)) ?_
      refine SepWP.pure_elim ?_
      rintro ⟨hlen7_le, hcap7_lt, hlen7_lt, hptr7_ne⟩
      refine seq_cleanX_placed
        (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b" 7 + 4#64))
        (P_mid := fun sm => ((p0 + 280#64) ↦₆₄ cap7) ∗ ((p0 + 288#64) ↦₆₄ ptr7) ∗
          ((p0 + 296#64) ↦₆₄ BitVec.ofNat 64 g.pub.changed.length) ∗
          memRegion ptr7 (g.pub.changed.length * 48) ∗
          (if cap7 = 0 then emp
           else A.repAlloc.live ptr7 (cap7.toNat * 48) 8 ∗
             memRegion (ptr7 + BitVec.ofNat 64 (g.pub.changed.length * 48))
               ((cap7.toNat - g.pub.changed.length) * 48)) ∗
          memRegion (p0 + 304#64) 16 ∗
          (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
            memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
            freeOnlyPool A lim st sm ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
            stackAt (s0.sp - 48#64) extHookStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 (Reg.gpr 19#5) = p0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr7)
        hcrl5 ?_ ?_
      · cases hc7 : g.pub.changed with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
          conv => arg 4; dsimp only [freeOnlyPool]
          wp_pull_exists; rename_i evs_7n
          refine SepWP.focus_pure (by sep_focus) fun hevs_7n => ?_
          wp_steps_sync_pool
            ((blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b" 7 + 4#64))
          apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_7n hevs_7n) (by sep_focus)
          try wp_done
        | cons hd tl =>
          rw [hc7] at hlen7_lt
          have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
          conv => arg 4; dsimp only [freeOnlyPool]
          wp_pull_exists; rename_i evs_7p
          refine SepWP.focus_pure (by sep_focus) fun hevs_7p => ?_
          apply sepWP_seq_lscro
            (mid := (blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b.cond" 3 + 4#64))
            hcrl5
          have hsp16480 : s0.sp - 16480#64 = (s0.sp - 48#64) - 16432#64 := by
            simp only [BitVec.sub_sub]; rfl
          wp_steps_sync_pool
            ((blkPl_550).base + (words_insn_off% (blkLib_550).text.code "b.cond" 3 + 4#64))
          apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_7p hevs_7p) (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcrl_p
          conv => arg 4; rw [hsp16480]
          refine sepWP_let_state fun sc hsc => ?_
          have hpre_eq :
              (freeOnlyPool A lim st sc ∗ ((p0 + 280#64) ↦₆₄ cap7) ∗ ((p0 + 288#64) ↦₆₄ ptr7) ∗
                ((p0 + 296#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                arrayAt (dirEntryAt A.repAlloc) 48 ptr7 (hd :: tl) ∗
                (if cap7 = 0 then emp
                 else A.repAlloc.live ptr7 (cap7.toNat * 48) 8 ∗
                   memRegion (ptr7 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap7.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (p0 + 304#64) 16 ∗
                (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
                  memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
                  memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
                  stackAt (s0.sp - 48#64) extHookStack ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) =
              (arrayAt (dirEntryAt A.repAlloc) 48 ptr7 (hd :: tl) ∗
                freeOnlyPool A lim st sc ∗ stackAt (s0.sp - 48#64) extHookStack ∗
                (((p0 + 280#64) ↦₆₄ cap7) ∗ ((p0 + 288#64) ↦₆₄ ptr7) ∗
                  ((p0 + 296#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                  (if cap7 = 0 then emp
                   else A.repAlloc.live ptr7 (cap7.toNat * 48) 8 ∗
                     memRegion (ptr7 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                       ((cap7.toNat - (hd :: tl).length) * 48)) ∗
                  memRegion (p0 + 304#64) 16 ∗
                  (memRegion p0 80 ∗ memRegion (p0 + 80#64) 40 ∗ memRegion (p0 + 120#64) 80 ∗
                    memRegion (p0 + 200#64) 40 ∗ memRegion (p0 + 240#64) 40 ∗
                    memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
                    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))) := by
            sep_ac_rfl
          subst hsc
          rw [hpre_eq]
          refine SepWP.mono
            (hloop3 st s0 (s0.sp - 48#64) p0 ptr7 hfsp_align (hd :: tl) ptr7 _ _
              (List.cons_ne_nil _ _) hlen7_lt (by wp_norm_goal) (by wp_norm_lhs) hcrl_p
              ⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩
              hx19_5 rfl rfl rfl) ?_
          intro sm Pm _ _ hh
          exact ⟨Entails.trans hh.1 (Entails.of_eq (by sep_ac_rfl)), hh.2⟩
      · intro sm hpcm hrunm hcrlm
          ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
            hx19_m, hx20_m⟩
        refine SepWP.weaken_pre
          (post_dir_loop_weaken_off A.repAlloc p0 280#64 288#64 296#64 304#64 cap7 ptr7
            ho7_8 ho7_16 ho7_24 g.pub.changed.length hlen7_le hcap7_lt _) ?_
        conv => arg 4; dsimp only [freeOnlyPool]
        wp_pull_exists; rename_i evs_7m
        refine SepWP.focus_pure (by sep_focus) fun hevs_7m => ?_
        have hsp16480 : s0.sp - 16480#64 = (s0.sp - 48#64) - 16432#64 := by
          simp only [BitVec.sub_sub]; rfl
        by_cases hcap7 : (cap7 == 0#64) = true <;>
          simp only [hcap7, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
        · wp_steps_sync_pool (s0.readReg64 .lr)
          conv => arg 4; rw [hsp16480]
          apply SepWP.fold (freeOnlyPool_keep A lim st _ evs_7m hevs_7m) (by sep_focus)
          refine sepWP_let_state fun sc hsc => ?_
          refine SepWP.weaken_pre
            (weaken_perm
              (stores_cap0_ret_weaken p0 cap7 (freeOnlyPool A lim st sc) s0.sp
                (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
                (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
                (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
              (by subst hsc; sep_ac_rfl)) ?_
          subst hsc
          try wp_done
        · have hcap_pos := pos_of_beq_zero_false hcap7
          have hsz_pos : 0 < cap7.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
          apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrlm
          wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
          conv => arg 4; rw [hsp16480]
          refine sepWP_let_state fun sc hsc => ?_
          refine SepWP.weaken_pre
            (weaken_perm
              (stores_tail_dealloc_pre_weaken p0 cap7
                (A.repAlloc.live ptr7 (cap7.toNat * 48) 8 ∗ memRegion ptr7 (cap7.toNat * 48))
                (A.pool lim (M.stepEvents evs_7m st) sc) s0.sp
                (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
                (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
                (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
              (by subst hsc; sep_ac_rfl)) ?_
          subst hsc
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcrl_ct
          have ⟨hcl_ct, hro_ct⟩ := hcrl_ct
          rw [mul_48_reg hcap7_lt]
          have hrlay : RustLayoutOk (cap7.toNat * 48) 8 := ⟨⟨hsz_pos, ⟨3, rfl⟩, by omega⟩, by decide⟩
          wp_call hdealloc (ptr7, cap7.toNat * 48, 8, M.stepEvents evs_7m st)
          apply SepWP.fold (freeOnlyPool_step_dealloc A lim st _ evs_7m hevs_7m (cap7.toNat * 48) 8)
            (by sep_focus)
          refine sepWP_let_state fun sc2 hsc2 => ?_
          refine SepWP.weaken_pre
            (weaken_perm (stores_tail_dealloc_post p0 (freeOnlyPool A lim st sc2) s0.sp)
              (by subst hsc2; sep_ac_rfl)) ?_
          subst hsc2
          try wp_done

end DropStoresMainPlacedBudget

/-- Proves the budget-threaded `dropStoresSpecPlaced` contract on block `550` at stack budgets `96 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem cliDropStores_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_550 H) (blkPl_550).base (dropStoresSpecPlaced M A lim stk) := by
  have hexact := cliDropStores_placed_ok_exact hA
  refine subroutine_ok_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - storesExactStk)
  have hsplit : stackAt s0.sp stk = stackAt s0.sp storesExactStk ∗ F :=
    stackAt_sub_split hstk hstk64 s0.sp
  have hpre1 : s0.mem ⊨
      (dropStoresRawSpecPlaced M A lim).pre (x, st) s0 ∗
        ((roPathAt x.g.signed.path ∗ roPathAt x.g.oneTime.path ∗
          roPathAt x.g.sessions.path ∗ roPathAt x.g.pub.path) ∗ (F ∗ R)) := by
    simp only [dropStoresSpecPlaced, dropStoresRawSpecPlaced,
      withLsCodeRoLoaded, dropStoresSpec] at hpre ⊢
    rw [hsplit] at hpre
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (Entails.of_eq (show _ =
        storesAt A.repAlloc x.a x.g ∗
          (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
            ⌜s0.readReg64 .x0 = x.a ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
            A.pool lim st s0 ∗ stackAt s0.sp storesExactStk ∗ F ∗ R) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (stores_entry_raw_ro A.repAlloc x.a x.g)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hpre2 : s0.mem ⊨ (dropStoresRawSpecPlaced M A lim).pre (x, st) s0 ∗ (F ∗ R) :=
    Satisfies.drop_mid hpre1
  refine reaches_pc_mono
    (subroutine_ok_apply_full hexact (x, st) (F ∗ R) hpc hrun hpre2 hsp) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  refine ⟨?_, hcc⟩
  simp only [dropStoresSpecPlaced, dropStoresRawSpecPlaced,
    withLsCodeRoLoaded, dropStoresSpec, freeOnlyPool] at hpost ⊢
  rw [hsplit]
  refine Satisfies.mono ?_ hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro evs
  have hord :
      (⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 320 ∗
        (⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt s0.sp storesExactStk) ∗ F ∗ R =
      ⌜sf.trace = s0.trace⌝ ∗ (⌜∀ ev ∈ evs, ∃ al sz, ev = .free al sz⌝ ∗
        ((memRegion x.a 320 ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s0.sp storesExactStk ∗ F) ∗ R)) := by
    sep_ac_rfl
  rw [hord]
  apply Entails.pure_left; intro htr
  apply Entails.pure_left; intro hevs
  refine Entails.sepExists_right evs (sepConj_mono_left ?_)
  rw [pure_sepConj_of_true ⟨htr, hevs⟩]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Transfers `cliDropStores_placed_ok` to any caller block `i < 619`. -/
theorem cliDropStores_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hA : AllocContractsXCliPlaced A lim H)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_550).base (dropStoresSpecPlaced M A lim stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 550)
    (cliDropStores_placed_ok hA stk hstk hstk64) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStoresPlacedBudget
