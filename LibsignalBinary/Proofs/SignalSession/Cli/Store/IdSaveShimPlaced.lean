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
# Relocatable `<IdentityFiles as IdentityKeyStore>::save_identity` Shim

Proves `idSaveShimSpecPlaced` on Block `600` (`lsProg_600 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdSaveShim

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

abbrev idSaveShimStackPlaced : Nat := extHookStack + 48

private theorem stackAt_idSaveShim_placed (sp : BitVec 64) :
    stackAt sp idSaveShimStackPlaced =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_32_box_placed (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b0 : BitVec 8, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWPp_pure_mid_placed {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem idSaveShim_placed_fixed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_600 H) (lsmpl.base 600)
      (idSaveShimSpecPlaced A idSaveShimStackPlaced) := by
  have hpanic := ls_panicAt_of_cliPanic (prog := lsProg_600 H)
    (sym := "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error") hpan
  unfold idSaveShimSpecPlaced StoreKit.withLsCodeRoLoaded
  simp only [idSaveBoxAt, stackAt_idSaveShim_placed]
  cells_unfold
  dsimp only [lsProg_600] at hpanic ⊢
  change subroutine_ok ((blkPC_600).rebase (blkPl_600).base H) (blkPl_600).base _
  wpp_init x s0
  obtain ⟨self, addrA, keyA⟩ := x
  dsimp only
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 32 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_600).base + 44#64)
  apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro (shim_lscro_of_cli (callerProg := (blkPC_600).rebase (blkPl_600).base H) hC (stk := extHookStack)) hcrl1 ()
  wp_steps
  wp_call_lscro (alloc_lscro_of_cli (callerProg := (blkPC_600).rebase (blkPl_600).base H) hC) hcrl_sf (32, 8)
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
    simp only [hoom, ite_false, memRegion_32_box_placed, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u2 =>
      SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid_placed fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-- The `save_identity` shim (Block `600`) meets `idSaveShimSpecPlaced A stk`. -/
theorem idSaveShim_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_600 H) (lsmpl.base 600) (idSaveShimSpecPlaced A stk) :=
  lift_stk_lscro (pl := lsmpl) (F := idSaveShimSpecPlaced A)
    (P := fun x s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA⌝ ∗ A.pool)
    (Q := fun x s0 sf =>
      ⌜sf.readReg64 .x1 = lsρ idSaveFutVtSym ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
        A.live (sf.readReg64 .x0) 32 8 ∗
        idSaveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗ A.pool)
    (idSaveShim_placed_fixed_ok hC hpan)
    (by dsimp [idSaveShimStackPlaced]; omega)
    (by intros; dsimp only [idSaveShimSpecPlaced, StoreKit.withLsCodeRoLoaded]; ac_rfl)
    (by intros; dsimp only [idSaveShimSpecPlaced, StoreKit.withLsCodeRoLoaded]; ac_rfl)

theorem idSaveShim_placed_caller_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] {stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : 0x30 + extHookStack ≤ stk)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 600) (idSaveShimSpecPlaced A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 600)
    (idSaveShim_placed_ok_of_deps hC hpan hstk) hblk

end Placed

end CryptoVerification.SignalSession.Cli.Store.IdSaveShim
