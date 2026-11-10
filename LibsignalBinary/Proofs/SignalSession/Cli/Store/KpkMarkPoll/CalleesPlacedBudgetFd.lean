/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve

/-!
# `.keepsFs` Budget-Threaded Relocatable Callee Contracts for `KpkMarkPoll`

Lifts `do_reserve_and_handle` (Block `561`) and `concat [local#3]` (Block `598`) to `.keepsFs`
under `AllocContractsFsPlaced A lim H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (SepWP.instantiate_post_exists doReserveStackX extHookStack memcpyName reserveCap withStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SignalSession (lsRustAllocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.MainHops (handleErrorSymCli)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_598 blkPl_598 lsProg_561 lsProg_598)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (CliPanicHooksPlaced ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (Concat2PosCall fs_setMem_pre_mark fs_setPC_pre_mark fs_setPState_pre_mark
   fs_writeReg64_pre_mark)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   rustAllocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (session_memcpy_region_keepsFs_lscro_of_fs shim_keepsFs_lscro_of_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget (reserve1_blk561_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudgetFd
  (allocNoOomExtern_keepsFs_lscro_of_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesBudget
  (KpkConcat2PosEnv kpkConcat2PosEvents kpkConcat2PosSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux
  (kpkConcat2PosAtSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetAux
  (kpkDoReserveSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (DoReserveEnv doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace
  fs_setPC_pre_mark fs_setMem_pre_mark fs_setPState_pre_mark fs_writeReg64_pre_mark

private abbrev cliConcatStackP : Nat := 96 + extHookStack

private theorem stackAt_split_ge_p (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

private theorem subroutine_ok_frame_weaken_noPanic_p {α : Type} {prog : Program}
    {entry : BitVec 64} {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog entry spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome x (F x s0 ∗ R) s0 hpc hrun hp' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · rw [hpan] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 1. `.keepsFs` `do_reserve_and_handle` (Block `561`) -/

/-- Block `561` (`cliDoReserveName`) meets
`withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim).keepsFs`
under `AllocContractsFsPlaced A lim H` and `CliPanicHooksPlaced H`. -/
theorem kpkReserve_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : doReserveStackX ≤ resStack) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim).keepsFs) :=
  reserve1_blk561_ok hFs hstk (hpan handleErrorSymCli (by decide))

/-- Block `561` meets `withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack).keepsFs`. -/
theorem kpkReserve_at_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : doReserveStackX ≤ resStack) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack).keepsFs) := by
  have h0 := kpkReserve_keepsFs_placed_ok hFs hpan hstk
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [Spec.keepsFs, kpkDoReserveSpec] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, hmem⟩
  have hfit_env : FitsEnv M lim st (DoReserveEnv x) := fun _ heq => heq ▸ hfits
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim).keepsFs).pre (x, st) s0 ∗ R := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [Spec.keepsFs, doReserveSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit_env⟩, hmem⟩
  refine h0.mono_outcome (x, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan', hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · exact Or.inl ⟨hret, hcc, hq⟩
  · exact Or.inr (Or.inl ⟨hpan', hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem kpkReserve_at_keepsFs_caller_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    {resStack : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hpan : CliPanicHooksPlaced H)
    (hstk : doReserveStackX ≤ resStack)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack).keepsFs) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 561)
    (kpkReserve_at_keepsFs_placed_ok hFs hpan hstk) hi

/-! ## 2. `.keepsFs` `concat [local#3]` (Block `598`) on Two Non-Empty Owned Slices -/

private theorem memRegion_24_cells_p (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_cliConcat_p (sp : BitVec 64) :
    stackAt sp cliConcatStackP =
      stackAt (sp - 96#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 12 (by decide)
  have hsum : 16384 + 8 * 12 = cliConcatStackP := by decide
  rw [hsum] at h1
  change stackAt sp cliConcatStackP =
    stackAt (sp - 96#64) extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

private theorem ofNat_getLsbD_63_false_p {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_getElem_63_false_p {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false_p h

private theorem ofNat_beq_zero_false_p {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ult_of_le_p {a b : Nat} (hle : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

private theorem vecU8_of_append_pos_p {M : AllocCostModel} (A : RustCliAllocBudget M)
    (v p' : BitVec 64) (bs0 bs1 : List (BitVec 8))
    (hpos : 0 < bs0.length + bs1.length) (hlt : bs0.length + bs1.length < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗
      A.live p' (bs0.length + bs1.length) 1 ∗ (p' ↦ₛ (bs0 ++ bs1)) ⊢
      vecU8 A.repAlloc v (bs0 ++ bs1) := by
  have hlen : (bs0 ++ bs1).length = bs0.length + bs1.length := List.length_append
  rw [← hlen]
  have hne0 : BitVec.ofNat 64 (bs0 ++ bs1).length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, hlen, Nat.mod_eq_of_lt (by omega)] at ht
    change bs0.length + bs1.length = 0 at ht; omega
  have htoNat : (BitVec.ofNat 64 (bs0 ++ bs1).length).toNat = (bs0 ++ bs1).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hlen]; omega)]
  have hlt' : (bs0 ++ bs1).length < 2 ^ 63 := by rw [hlen]; exact hlt
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 (bs0 ++ bs1).length))
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  simp only [hne0, htoNat, Nat.le_refl, hlt', ↓reduceIte, RustCliAllocBudget.repAlloc,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 (bs0 ++ bs1).length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0 ++ bs1).length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' (bs0 ++ bs1).length 1 ∗ (p' ↦ₛ (bs0 ++ bs1)) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 (bs0 ++ bs1).length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0 ++ bs1).length) ∗
        A.live p' (bs0 ++ bs1).length 1 ∗ (p' ↦ₛ (bs0 ++ bs1))) by sep_ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

set_option maxHeartbeats 1600000 in
private theorem kpkConcat2_pos_at_exact_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H) :
    subroutine_ok (lsProg_598 H) (blkPl_598).base
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosAtSpec A lim cliConcatStackP).keepsFs) := by
  have hshim := shim_keepsFs_lscro_of_fs (callerProg := lsProg_598 H) hFs
    (stk := extHookStack) (by decide) (by decide)
  have halloc := allocNoOomExtern_keepsFs_lscro_of_fs (callerProg := lsProg_598 H) hFs
  have hmc := session_memcpy_region_keepsFs_lscro_of_fs (callerProg := lsProg_598 H) hFs
    (stk := extHookStack) (by decide) (by decide)
  clear hFs
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionShimBudgetSpec, lsProg_598] at hshim
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, lsProg_598] at halloc
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionMemcpyRegionBudgetSpec, lsProg_598] at hmc
  unfold withLsCodeRoLoaded Spec.keepsFs kpkConcat2PosAtSpec
  simp only [memRegion_24_cells_p, stackAt_cliConcat_p, sepExists_sepConj_left, sepExists_sepConj_right]
  change subroutine_ok ((blkPC_598).rebase (blkPl_598).base H) (blkPl_598).base _
  wp_init x s0
  obtain ⟨⟨outVec, slicesA, p0, bs0, p1, bs1⟩, st⟩ := x
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  dsimp only at *
  have hpos0 : 0 < bs0.length := ‹_›
  have hpos1 : 0 < bs1.length := ‹_›
  have hmax : bs0.length + bs1.length < 2 ^ 63 := ‹_›
  have hfit_env : FitsEnv M lim st (KpkConcat2PosEnv ⟨outVec, slicesA, p0, bs0, p1, bs1⟩) := ‹_›
  have hfit_evs : FitsEvents M lim st (rustAllocEvents (bs0.length + bs1.length) 1) :=
    hfit_env _ rfl
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have hadd_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add]
  have hsub_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
      omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le_p (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false_p (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length))[63] = false :=
    ofNat_getElem_63_false_p (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le_p (by omega) (by omega)
  have hhi1 : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
    ofNat_beq_zero_false_p (by omega) (by omega)
  have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false :=
    ofNat_beq_zero_false_p hpos0 h0_lt64
  have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false :=
    ofNat_beq_zero_false_p hpos1 h1_lt64
  have hrlay : RustLayoutOk (bs0.length + bs1.length) 1 := ⟨⟨by omega, hpow1, by omega⟩, hal1⟩
  apply sepWP_seq_lscro hcrl0 (mid := lsρ lsRustNoAllocShimSymCli)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  apply sepWP_seq_lscro hcrl1 (mid := lsρ lsRustAllocSymCli)
  rcases hcrl1 with ⟨hcl1, hro1⟩
  wp_call hshim ()
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl2
  apply sepWP_seq_lscro hcrl2 (mid := lsρ memcpyName)
  rcases hcrl2 with ⟨hcl2, hro2⟩
  wp_call halloc (bs0.length + bs1.length, 1, st)
  have hoom : sf_1.readReg64 Reg.x0 ≠ 0#64 := by tauto
  have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
  rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
  wp_steps_sync_pool (lsρ memcpyName)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl3
  apply sepWP_seq_lscro hcrl3 (mid := (blkPl_598).base + bv% (172))
  rcases hcrl3 with ⟨hcl3, hro3⟩
  wp_apply using hmc
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl3'
  apply sepWP_seq_lscro hcrl3' (mid := lsρ memcpyName)
  wp_steps_sync_pool (lsρ memcpyName)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hcl4, hro4⟩
  wp_apply using hmc
  refine ProofLib.SepWP.transport_budgetPool (by tauto) (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 .lr)
  have hfs_tot : sf_3.fs = s0.fs := by
    have hfs1 : sf.fs = s0.fs := by simpa only [wp_norm, arm64_norm] using ‹sf.fs = _›
    have hfs2 : sf_1.fs = sf.fs := by simpa only [wp_norm, arm64_norm] using ‹sf_1.fs = _›
    have hfs3 : sf_2.fs = sf_1.fs := by simpa only [wp_norm, arm64_norm] using ‹sf_2.fs = _›
    have hfs4 : sf_3.fs = sf_2.fs := by simpa only [wp_norm, arm64_norm] using ‹sf_3.fs = _›
    exact hfs4.trans (hfs3.trans (hfs2.trans hfs1))
  apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm)
    (by sep_focus)
  apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  dsimp only [kpkConcat2PosEvents, RustCliAllocBudget.repAlloc_live]
  wp_done

/-- Block `598` (`cliConcatName`) meets
`withLsCodeRoLoaded lsmpl (kpkConcat2PosAtSpec A lim stk).keepsFs`
for any `96 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem kpkConcat2_pos_at_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_598 H) (lsmpl.base 598)
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosAtSpec A lim stk).keepsFs) := by
  change subroutine_ok (lsProg_598 H) (blkPl_598).base _
  refine subroutine_ok_frame_weaken_noPanic_p
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliConcatStackP))
    (kpkConcat2_pos_at_exact_keepsFs_placed_ok hFs) ?_ ?_
  · intro x s0
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, kpkConcat2PosAtSpec, cliConcatStackP]
    rw [stackAt_split_ge_p s0.sp hstk hstk64]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro x s0 sf
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, kpkConcat2PosAtSpec, cliConcatStackP]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.of_eq (congrArg sepExists (funext fun p' => ?_))
    rw [stackAt_split_ge_p s0.sp hstk hstk64]
    sep_ac_rfl

/-- Block `598` (`cliConcatName`) meets
`withLsCodeRoLoaded lsmpl (kpkConcat2PosSpec A lim stk).keepsFs`
for any `96 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem kpkConcat2_pos_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H)
    (_hpan : CliPanicHooksPlaced H)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_598 H) (lsmpl.base 598)
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosSpec A lim stk).keepsFs) := by
  have hat := kpkConcat2_pos_at_keepsFs_placed_ok hFs stk hstk hstk64
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [Spec.keepsFs, kpkConcat2PosSpec] at hpre0
  have hbounds : 0 < x.bs0.length ∧ 0 < x.bs1.length ∧ x.bs0.length + x.bs1.length < 2 ^ 63 := by
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    exact ⟨hpre0.1.2.2.2.1, hpre0.1.2.2.2.2.1, hpre0.1.2.2.2.2.2.1⟩
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosAtSpec A lim stk).keepsFs).pre (x, st) s0 ∗ R :=
    satisfies_lscro_pre hcrl hpre0
  refine hat.mono_outcome (x, st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan', hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, kpkConcat2PosAtSpec, kpkConcat2PosSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfs_eq, hq⟩
    refine ⟨hfs_eq, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htrace, hp'⟩, hmem_f⟩
    refine ⟨kpkConcat2PosEvents x, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htrace, rfl⟩, ?_⟩
    have hfold := vecU8_of_append_pos_p A x.outVec p' x.bs0 x.bs1
      (by omega) hbounds.2.2 hp'
    have hm1 : sf.mem ⊨
        ((x.outVec ↦₆₄ BitVec.ofNat 64 (x.bs0.length + x.bs1.length)) ∗
          ((x.outVec + 8#64) ↦₆₄ p') ∗
          ((x.outVec + 16#64) ↦₆₄ BitVec.ofNat 64 (x.bs0.length + x.bs1.length)) ∗
          A.live p' (x.bs0.length + x.bs1.length) 1 ∗
          (p' ↦ₛ (x.bs0 ++ x.bs1))) ∗
        ((x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
          ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
          (x.p0 ↦ₛ x.bs0) ∗ (x.p1 ↦ₛ x.bs1) ∗
          A.pool lim (M.stepEvents (kpkConcat2PosEvents x) st) sf ∗ stackAt s0.sp stk ∗ R) := by
      convert hmem_f using 1; sep_ac_rfl
    have hm2 := Satisfies.mono (sepConj_mono_left hfold) hm1
    convert hm2 using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan', hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudgetFd
