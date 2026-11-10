/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymE
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Pre-Key Store Shims

Proves `[LibsignalPlacement]` contracts for the pre-key store `async_trait` shims in Blocks `606`
(`spkGetShim`), `608` (`pkGetShim`), `610` (`pkRemoveShim`), `611` (`kpkGetShim`), and `613`
(`kpkMarkShim`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.PkShims

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev pkShimStackPlaced : Nat := extHookStack + 32
abbrev kpkMarkShimStackPlaced : Nat := extHookStack + 48

private theorem stackAt_pkShim_placed (sp : BitVec 64) :
    stackAt sp pkShimStackPlaced =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem stackAt_kpkMarkShim_placed (sp : BitVec 64) :
    stackAt sp kpkMarkShimStackPlaced =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_16_box_placed (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u1 : BitVec 32, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₃₂ u1) ∗ ((p + 12#64) ↦₈ b0) ∗
        memRegion (p + 13#64) 3) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 4 4 (by decide),
    memRegion_split (p + 8#64 + 4#64) 1 3 (by decide),
    memRegion_one, ProofLib.memRegion_four, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_32_kpkMarkBox_placed (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b0 : BitVec 8, ∃∗ u3 : BitVec 32, ∃∗ u2 : BitVec 32,
        ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₃₂ u2) ∗
        ((p + 20#64) ↦₃₂ u3) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 4 12 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 4#64) 4 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 4#64 + 4#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_four, ProofLib.memRegion_four,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWPp_pure_mid_placed {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem pkShim_lift_stk_placed [LibsignalPlacement] {vtSym : String} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hInner : subroutine_ok prog entry (pkShimSpecPlaced vtSym A pkShimStackPlaced))
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok prog entry (pkShimSpecPlaced vtSym A stk) :=
  lift_stk_lscro (pl := lsmpl) (F := pkShimSpecPlaced vtSym A)
    (P := fun x s => ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id⌝ ∗ A.pool)
    (Q := fun x s0 sf =>
      ⌜sf.readReg64 .x1 = lsρ vtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
        A.live (sf.readReg64 .x0) 16 8 ∗ pkBoxAt (sf.readReg64 .x0) x.self x.id 0#8 ∗ A.pool)
    hInner
    (by dsimp [pkShimStackPlaced]; omega)
    (by intros; dsimp only [pkShimSpecPlaced, StoreKit.withLsCodeRoLoaded]; ac_rfl)
    (by intros; dsimp only [pkShimSpecPlaced, StoreKit.withLsCodeRoLoaded]; ac_rfl)

theorem spkGetShim_placed_fixed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_606 H) (lsmpl.base 606)
      (pkShimSpecPlaced spkGetFutVtSym A pkShimStackPlaced) := by
  have hpanic := ls_panicAt_of_cliPanic (prog := lsProg_606 H)
    (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") hpan
  unfold pkShimSpecPlaced StoreKit.withLsCodeRoLoaded
  simp only [pkBoxAt, stackAt_pkShim_placed]
  cells_unfold
  dsimp only [lsProg_606] at hpanic ⊢
  change subroutine_ok ((blkPC_606).rebase (blkPl_606).base H) (blkPl_606).base _
  wpp_init x s0
  obtain ⟨self, id⟩ := x
  dsimp only
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_606).base + 36#64)
  apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro (shim_lscro_of_cli (callerProg := (blkPC_606).rebase (blkPl_606).base H) hC (stk := extHookStack)) hcrl1 ()
  wp_steps
  wp_call_lscro (alloc_lscro_of_cli (callerProg := (blkPC_606).rebase (blkPl_606).base H) hC) hcrl_sf (16, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_placed fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_box_placed, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_placed fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem pkGetShim_placed_fixed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (pkShimSpecPlaced pkGetFutVtSym A pkShimStackPlaced) := by
  have hpanic := ls_panicAt_of_cliPanic (prog := lsProg_608 H)
    (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") hpan
  unfold pkShimSpecPlaced StoreKit.withLsCodeRoLoaded
  simp only [pkBoxAt, stackAt_pkShim_placed]
  cells_unfold
  dsimp only [lsProg_608] at hpanic ⊢
  change subroutine_ok ((blkPC_608).rebase (blkPl_608).base H) (blkPl_608).base _
  wpp_init x s0
  obtain ⟨self, id⟩ := x
  dsimp only
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_608).base + 36#64)
  apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro (shim_lscro_of_cli (callerProg := (blkPC_608).rebase (blkPl_608).base H) hC (stk := extHookStack)) hcrl1 ()
  wp_steps
  wp_call_lscro (alloc_lscro_of_cli (callerProg := (blkPC_608).rebase (blkPl_608).base H) hC) hcrl_sf (16, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_placed fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_box_placed, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_placed fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem pkRemoveShim_placed_fixed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_610 H) (lsmpl.base 610)
      (pkShimSpecPlaced pkRemoveFutVtSym A pkShimStackPlaced) := by
  have hpanic := ls_panicAt_of_cliPanic (prog := lsProg_610 H)
    (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") hpan
  unfold pkShimSpecPlaced StoreKit.withLsCodeRoLoaded
  simp only [pkBoxAt, stackAt_pkShim_placed]
  cells_unfold
  dsimp only [lsProg_610] at hpanic ⊢
  change subroutine_ok ((blkPC_610).rebase (blkPl_610).base H) (blkPl_610).base _
  wpp_init x s0
  obtain ⟨self, id⟩ := x
  dsimp only
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_610).base + 36#64)
  apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro (shim_lscro_of_cli (callerProg := (blkPC_610).rebase (blkPl_610).base H) hC (stk := extHookStack)) hcrl1 ()
  wp_steps
  wp_call_lscro (alloc_lscro_of_cli (callerProg := (blkPC_610).rebase (blkPl_610).base H) hC) hcrl_sf (16, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_placed fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_box_placed, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_placed fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem kpkGetShim_placed_fixed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (pkShimSpecPlaced kpkGetFutVtSym A pkShimStackPlaced) := by
  have hpanic := ls_panicAt_of_cliPanic (prog := lsProg_611 H)
    (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") hpan
  unfold pkShimSpecPlaced StoreKit.withLsCodeRoLoaded
  simp only [pkBoxAt, stackAt_pkShim_placed]
  cells_unfold
  dsimp only [lsProg_611] at hpanic ⊢
  change subroutine_ok ((blkPC_611).rebase (blkPl_611).base H) (blkPl_611).base _
  wpp_init x s0
  obtain ⟨self, id⟩ := x
  dsimp only
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_611).base + 36#64)
  apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro (shim_lscro_of_cli (callerProg := (blkPC_611).rebase (blkPl_611).base H) hC (stk := extHookStack)) hcrl1 ()
  wp_steps
  wp_call_lscro (alloc_lscro_of_cli (callerProg := (blkPC_611).rebase (blkPl_611).base H) hC) hcrl_sf (16, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_placed fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_box_placed, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_placed fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem kpkMarkShim_placed_fixed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_613 H) (lsmpl.base 613)
      (kpkMarkShimSpecPlaced A kpkMarkShimStackPlaced) := by
  have hpanic := ls_panicAt_of_cliPanic (prog := lsProg_613 H)
    (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") hpan
  unfold kpkMarkShimSpecPlaced StoreKit.withLsCodeRoLoaded
  simp only [kpkMarkBoxAt, stackAt_kpkMarkShim_placed]
  cells_unfold
  dsimp only [lsProg_613] at hpanic ⊢
  change subroutine_ok ((blkPC_613).rebase (blkPl_613).base H) (blkPl_613).base _
  wpp_init x s0
  obtain ⟨self, id, signedId, baseKeyA⟩ := x
  dsimp only
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 32 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_613).base + 48#64)
  apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro (shim_lscro_of_cli (callerProg := (blkPC_613).rebase (blkPl_613).base H) hC (stk := extHookStack)) hcrl1 ()
  wp_steps
  wp_call_lscro (alloc_lscro_of_cli (callerProg := (blkPC_613).rebase (blkPl_613).base H) hC) hcrl_sf (32, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_placed fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error")
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_32_kpkMarkBox_placed, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_placed fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-- The `get_signed_pre_key` shim (Block `606`) meets `pkShimSpecPlaced spkGetFutVtSym A stk`. -/
theorem spkGetShim_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_606 H) (lsmpl.base 606)
      (pkShimSpecPlaced spkGetFutVtSym A stk) :=
  pkShim_lift_stk_placed (spkGetShim_placed_fixed_ok hC hpan) hstk

/-- The `get_pre_key` shim (Block `608`) meets `pkShimSpecPlaced pkGetFutVtSym A stk`. -/
theorem pkGetShim_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (pkShimSpecPlaced pkGetFutVtSym A stk) :=
  pkShim_lift_stk_placed (pkGetShim_placed_fixed_ok hC hpan) hstk

/-- The `remove_pre_key` shim (Block `610`) meets `pkShimSpecPlaced pkRemoveFutVtSym A stk`. -/
theorem pkRemoveShim_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_610 H) (lsmpl.base 610)
      (pkShimSpecPlaced pkRemoveFutVtSym A stk) :=
  pkShim_lift_stk_placed (pkRemoveShim_placed_fixed_ok hC hpan) hstk

/-- The `get_kyber_pre_key` shim (Block `611`) meets `pkShimSpecPlaced kpkGetFutVtSym A stk`. -/
theorem kpkGetShim_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (pkShimSpecPlaced kpkGetFutVtSym A stk) :=
  pkShim_lift_stk_placed (kpkGetShim_placed_fixed_ok hC hpan) hstk

/-- The `mark_kyber_pre_key_used` shim (Block `613`) meets `kpkMarkShimSpecPlaced A stk`. -/
theorem kpkMarkShim_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_613 H) (lsmpl.base 613)
      (kpkMarkShimSpecPlaced A stk) :=
  lift_stk_lscro (pl := lsmpl) (F := kpkMarkShimSpecPlaced A)
    (P := fun x s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg32 .x1 = x.id ∧ s.readReg32 .x2 = x.signedId ∧
        s.readReg64 .x3 = x.baseKeyA⌝ ∗ A.pool)
    (Q := fun x s0 sf =>
      ⌜sf.readReg64 .x1 = lsρ kpkMarkFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
        A.live (sf.readReg64 .x0) 32 8 ∗
        kpkMarkBoxAt (sf.readReg64 .x0) x.self x.baseKeyA x.id x.signedId 0#8 ∗ A.pool)
    (kpkMarkShim_placed_fixed_ok hC hpan)
    (by dsimp [kpkMarkShimStackPlaced]; omega)
    (by intros; dsimp only [kpkMarkShimSpecPlaced, StoreKit.withLsCodeRoLoaded]; ac_rfl)
    (by intros; dsimp only [kpkMarkShimSpecPlaced, StoreKit.withLsCodeRoLoaded]; ac_rfl)

end Placed

end CryptoVerification.SignalSession.Cli.Store.PkShims
