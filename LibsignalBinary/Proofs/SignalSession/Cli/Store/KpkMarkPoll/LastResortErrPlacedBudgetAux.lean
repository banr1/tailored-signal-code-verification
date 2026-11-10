/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.DropsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Exit Event Lists & Block-`561` Reserve Wrapper for `KpkMarkPoll`

Defines `last_resort` error and append event lists, `vecU8At`/`vecU8` packing lemmas, and the
budget-threaded `Vec<u8>::reserve` contract (`kpkDoReserveSpec`) on Block `561`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetAux

open Arm64 ProofLib SepProp
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall SepWP.instantiate_post_exists doReserveStackX finishGrowStackX reserveCap
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SpqrV1.Alloc (
  DoReserveStrideCall adds_cs_eq_false reserveCapStride reserveCapStride_one reserveMinCap
  reserve_new_cap_stride_eq
)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_561 lsProg_561)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (
  ls_transfer_lscro satisfies_lscro_pre
)
open CryptoVerification.SignalSession.Cli.GrowOne.Helpers (stackAt_cliGrowOne)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers (
  sepWPp_conseq sepWPp_of_sepWP_lscro vecU8Tail
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (lift_stk_lscro_budget)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget (
  kpkErrCleanupEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlacedBudget (
  cliFinishGrow_placed_caller_ok_x
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget (
  FinishGrowNeEnv FinishGrowZeroEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.PlacedBudget (
  finish_grow_ne_cells_placed_ok_x finish_grow_zero_cells_placed_ok_x
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Event Lists for `reused`, `malformed`, and `seen ++ used` Append Exits -/

/-- Events emitted by `kpk_reused_230_placed`: 15-byte string alloc followed by error cleanup. -/
def kpkReusedEvents (usedCap seenCap fileCap : BitVec 64) : List AllocEvent :=
  rustAllocEvents 15 1 ++ kpkErrCleanupEvents usedCap seenCap fileCap

/-- Events emitted by `kpk_malformed_2a4_placed`: 14-byte string alloc followed by error cleanup. -/
def kpkMalformedEvents (usedCap seenCap fileCap : BitVec 64) : List AllocEvent :=
  rustAllocEvents 14 1 ++ kpkErrCleanupEvents usedCap seenCap fileCap

/-- Optional `Vec::reserve(37)` events emitted on `seen` before `memcpy` in `kpk_append_37c_placed`. -/
def kpkAppendReserveEvents (seenCap : BitVec 64) (seenBs : List (BitVec 8)) : List AllocEvent :=
  if (seenCap - BitVec.ofNat 64 seenBs.length).ult 37#64 then
    doReserveEvents ⟨0#64, seenCap, 0#64, seenBs, 37⟩
  else []

/-- Events emitted before `Dir::put` in `kpk_append_37c_placed` (optional `seen.reserve(37)` plus
dropping `used`). -/
def kpkAppendPrePutEvents (seenCap : BitVec 64) (seenBs : List (BitVec 8))
    (usedCap : BitVec 64) : List AllocEvent :=
  kpkAppendReserveEvents seenCap seenBs ++ optDeallocBufEvents usedCap

/-! ## 2. `vecU8At` / `vecU8` Packing & Unpacking Helpers -/

theorem vecU8At_of_flat_p (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false ptr bs ∗ vecU8Tail A cap ptr bs) ⊢
      vecU8At A v cap ptr bs := by
  unfold vecU8At vecHeader vecU8Tail bytesAt
  simp only [Bool.false_eq_true, ite_false]
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero]
  by_cases hc : cap = 0#64
  · subst hc
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hbs
    simp only [ite_true, pointsToBytes_nil, sepConj_emp]
    rw [show ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 [].length)) ∗
          ⌜[].length ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ =
        ⌜[].length ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 [].length)) by
          sep_ac_rfl]
    exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)
  · simp only [hc, ite_false]
    rw [show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by
          sep_ac_rfl]
    exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

theorem vecU8At_unpack_pos_p (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hc : cap ≠ 0#64) :
    vecU8At A v cap ptr bs =
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8At vecHeader
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [hzero, hc, ite_false, sepConj_assoc]
  sep_ac_rfl

theorem vecU8_of_grown_p (A : RustAlloc) (v v8 v16 cap ptr : BitVec 64)
    (bs : List (BitVec 8))
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16)
    (hc : cap ≠ 0#64) (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
      vecU8 A v bs := by
  subst hv8; subst hv16
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [hzero, hc, ite_false, sepConj_assoc]
  rw [show (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by
        sep_ac_rfl]
  exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

/-! ## 3. Budget-Threaded Block `561` (`do_reserve_and_handle`) under `withLsCodeRoLoaded` -/

private def kpkDoReserveRawEvents (x : DoReserveStrideCall) : List AllocEvent :=
  let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
  if x.cap = 0#64 then rustAllocEvents (newCap * x.stride.toNat) x.align.toNat
  else rustReallocEvents (x.cap.toNat * x.stride.toNat) (newCap * x.stride.toNat) x.align.toNat

private def kpkDoReserveRawSpecP {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DoReserveStrideCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.len ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = x.align ∧
      s.readReg64 .x4 = x.stride ∧
      x.len ≤ x.cap.toNat ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.ptr ≠ 0#64 ∧ 0 < x.stride.toNat ∧ x.align.toNat ≤ 2 ^ 31 ∧
      LayoutOk (newCap * x.stride.toNat) x.align.toNat ∧
      FitsEvents M lim st (kpkDoReserveRawEvents x)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
         (x.cap.toNat * x.stride.toNat - x.bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp doReserveStackX
  post := fun (x, st) s0 sf =>
    let newCap := reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0⌝ ∗
      (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (newCap * x.stride.toNat - x.bs.length)) ∗
    A.pool lim (M.stepEvents (kpkDoReserveRawEvents x) st) sf ∗ stackAt s0.sp doReserveStackX

private theorem kpkReserve_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_561 H) (blkPl_561).base
      (withLsCodeRoLoaded lsmpl (kpkDoReserveRawSpecP A lim)) := by
  have hFG : subroutine_ok (lsProg_561 H) (lsmpl.base 587)
      (withLsCodeRoLoaded lsmpl (LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowSpecX M A lim)) :=
    cliFinishGrow_placed_caller_ok_x (callerProg := lsProg_561 H) hA (by decide)
  dsimp only [withLsCodeRoLoaded]
  simp only [kpkDoReserveRawSpecP, stackAt_cliGrowOne, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  obtain ⟨⟨v, cap, ptr, bs, len, additional, align, stride⟩, st⟩ := x
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  dsimp only at *
  have hfg0 := finish_grow_zero_cells_placed_ok_x hFG
  have hfg1 := finish_grow_ne_cells_placed_ok_x hFG
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hal31 : align.toNat ≤ 2 ^ 31 := by assumption
  have hlay0 : LayoutOk (reserveCapStride stride.toNat cap.toNat len additional * stride.toNat)
      align.toNat := by assumption
  have hfits_raw : FitsEvents M lim st
      (kpkDoReserveRawEvents ⟨v, cap, ptr, bs, len, additional, align, stride⟩) := by assumption
  have hpow : ∃ k, align.toNat = 2 ^ k := hlay0.2.1
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤
        2 ^ 63 := hlay0.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hmul_pos : 0 < new.toNat * stride.toNat := Nat.mul_pos hnew_pos hstr_pos
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact hlay0
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hfit0 : FitsEnv M lim st (FinishGrowZeroEnv new stride align) := by
      unfold FinishGrowZeroEnv
      rw [FitsEnv.eq_iff]
      simpa only [kpkDoReserveRawEvents, ↓reduceIte, hnew_toNat] using hfits_raw
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [kpkDoReserveRawEvents, ↓reduceIte, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply sepWP_seq_lscro hcrl0 (mid := lsmpl.base 587)
    wp_steps_sync_pool (lsmpl.base 587)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    wp_call_lscro hfg0 hcrl1
      ((s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
    have hw_evs : w = rustAllocEvents (new.toNat * stride.toNat) align.toNat := by
      have : FinishGrowZeroEnv new stride align w := by tauto
      exact this
    subst hw_evs
    wp_steps_sync_pool (s0.readReg64 .lr)
    simp only [State.setMem_setMem]
    wp_done
  · simp only [kpkDoReserveRawEvents, hcap0, ↓reduceIte, sepConj_assoc]
    have hfit1 : FitsEnv M lim st (FinishGrowNeEnv cap new stride align) := by
      unfold FinishGrowNeEnv
      rw [FitsEnv.eq_iff]
      simpa only [kpkDoReserveRawEvents, hcap0, ↓reduceIte, hnew_toNat] using hfits_raw
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply sepWP_seq_lscro hcrl0 (mid := lsmpl.base 587)
    wp_steps_sync_pool (lsmpl.base 587)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    wp_call_lscro hfg1 hcrl1
      ((s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
    have hw_evs :
        w = rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat := by
      have : FinishGrowNeEnv cap new stride align w := by tauto
      exact this
    subst hw_evs
    wp_steps_sync_pool (s0.readReg64 .lr)
    simp only [State.setMem_setMem]
    wp_done

/-- Budget-threaded `Vec<u8>::reserve` contract at stack budget `resStack`. -/
def kpkDoReserveSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (resStack : Nat) : Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧
      s.readReg64 .x4 = 1#64 ∧ newCap + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (doReserveEvents x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp resStack
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ p' : BitVec 64, vecU8At A.repAlloc x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
      A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗ stackAt s0.sp resStack

private theorem vecU8At_eq_flat_p (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  sep_ac_rfl

private theorem kpkReserve_exact_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim doReserveStackX)) := by
  have hraw := kpkReserve_raw_placed_ok hA
  change subroutine_ok (lsProg_561 H) (blkPl_561).base _
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  simp only [kpkDoReserveSpec, vecU8At_eq_flat_p, RustCliAllocBudget.repAlloc_live_norm,
    sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfits⟩, ⟨hlen, _hcap63, hptr⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  have hevs : kpkDoReserveRawEvents xs = doReserveEvents x := by
    unfold kpkDoReserveRawEvents doReserveEvents
    simp only [xs, BitVec.toNat_ofNat, Nat.one_mod, reserveCapStride_one, Nat.mul_one]
  have hpre_raw : s0.mem ⊨
      (kpkDoReserveRawSpecP A lim).pre (xs, st) s0 ∗
        (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [kpkDoReserveRawSpecP, xs, hevs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, by decide, hlay, hfits⟩, ?_⟩
    convert hmem using 1; sep_ac_rfl
  refine hraw.mono_outcome (xs, st)
    (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R)
    s0 hpc hrun (satisfies_lscro_pre hcrl hpre_raw) hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded] at hq ⊢
    simp only [kpkDoReserveRawSpecP, kpkDoReserveSpec, vecU8At_eq_flat_p,
      RustCliAllocBudget.repAlloc_live_norm, xs, hevs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, Nat.mod_one, and_true] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem_f⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, Nat.mod_eq_of_lt hlt]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    convert hmem_f using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, kpkDoReserveRawSpecP] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, kpkDoReserveRawSpecP] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, kpkDoReserveRawSpecP] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Block `561` (`do_reserve_and_handle`) meets `withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack)`
for any `doReserveStackX ≤ resStack`. -/
theorem kpkReserve_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {resStack : Nat}
    (hA : AllocContractsXCliPlaced A lim H)
    (hstk : doReserveStackX ≤ resStack) :
    subroutine_ok (lsProg_561 H) (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack)) :=
  lift_stk_lscro_budget
    (pl := lsmpl)
    (F := fun k => withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim k))
    (P := fun (x, st) s =>
      let newCap := reserveCap x.cap.toNat x.bs.length x.additional
      ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
        (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = 1#64 ∧
        s.readReg64 .x4 = 1#64 ∧ newCap + 1 ≤ 2 ^ 63 ∧
        FitsEvents M lim st (doReserveEvents x)⌝ ∗
        vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
        A.pool lim st s)
    (Q := fun (x, st) s0 sf =>
      let newCap := reserveCap x.cap.toNat x.bs.length x.additional
      ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ p' : BitVec 64, vecU8At A.repAlloc x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
        A.pool lim (M.stepEvents (doReserveEvents x) st) sf)
    (kpkReserve_exact_placed_ok hA) hstk
    (fun ⟨x, st⟩ s k => by
      dsimp only [withLsCodeRoLoaded, kpkDoReserveSpec]
      sep_ac_rfl)
    (fun ⟨x, st⟩ s0 sf k => by
      dsimp only [withLsCodeRoLoaded, kpkDoReserveSpec]
      sep_ac_rfl)

theorem kpkReserve_caller_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    {resStack : Nat}
    (hA : AllocContractsXCliPlaced A lim H)
    (hstk : doReserveStackX ≤ resStack)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack)) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 561) (kpkReserve_placed_ok hA hstk) hi

private theorem entails_withLsCodeRoLoaded_pre_res [LibsignalPlacement]
    {s : State} {P Q F : SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : P ⊢ Q ∗ F) :
    P ⊢ (Q ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ F := by
  refine Entails.trans h ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hcrl (Entails.refl F))

/-- `SepWPp` call wrapper for `kpkDoReserveSpec` under `withLsCodeRoLoaded lsmpl`. -/
theorem kpk_call_reserve_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {resStack : Nat} {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack)))
    (xg : DoReserveCall) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.v) (hx1 : (s.readReg64 .x1).toNat = xg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = xg.additional)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap xg.cap.toNat xg.bs.length xg.additional + 1 ≤ 2 ^ 63)
    (hfit : FitsEvents M lim st (doReserveEvents xg))
    (hpre : P ⊢ (vecU8At A.repAlloc xg.v xg.cap xg.ptr xg.bs ∗
      A.pool lim st s ∗ stackAt s.sp resStack) ∗ F)
    (hnext : ∀ (sm : State) (p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → p' ≠ 0#64 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc xg.v
            (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗ F)
        Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hpre' : P ⊢ (withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack)).pre (xg, st) s ∗ F := by
    refine Entails.trans hpre ?_
    unfold withLsCodeRoLoaded kpkDoReserveSpec
    refine entails_withLsCodeRoLoaded_pre_res hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩ (Entails.refl _)
  refine sepWPp_of_sepWP_lscro hcrl (mid := ret_pc) ?_
  exact ProofLib.SepWP.call_subroutine_frame hcall hpc hrun hsp_align hlr
    (fun R hm => by
      have hm' : s.mem ⊨
          ((withLsCodeRoLoaded lsmpl (kpkDoReserveSpec A lim resStack)).pre (xg, st) s ∗ F) ∗ R :=
        Satisfies.mono (sepConj_mono_left hpre') hm
      rwa [sepConj_assoc] at hm')
    (fun _ _ _ hp => by
      simp only [kpkDoReserveSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => by
      simp only [kpkDoReserveSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun sm hpcm hrunm hspm hcsm =>
      ProofLib.SepWP.done hpcm hrunm fun hcrlm => by
        simp only [kpkDoReserveSpec, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun p' => SepWPp.pure_elim fun htrm => ?_
        have hp'_pull :
            vecU8At A.repAlloc xg.v
                (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
              (A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗
                (stackAt s.sp resStack ∗ F)) =
            (vecU8At A.repAlloc xg.v
                (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
              A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗ F := by
          sep_ac_rfl
        rw [hp'_pull]
        intro R' hm hL
        have hp'_ne : p' ≠ 0#64 := by
          have hm1 : sm.mem ⊨ vecU8At A.repAlloc xg.v
              (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
              ((A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗
                F ∗ R') := by
            simpa only [sepConj_assoc] using hm
          unfold vecU8At at hm1
          rw [sepConj_assoc] at hm1
          have hm2 := Satisfies.of_sep_left (Satisfies.of_sep_right hm1)
          rw [satisfies_pure_sepConj] at hm2
          exact hm2.1.2.2
        exact hnext sm p' hpcm hrunm hspm hcsm hcrlm htrm hp'_ne R' hm hL)
    (fun _ _ _ ho => by
      simp only [kpkDoReserveSpec] at ho
      exact (not_satisfies_false_sepConj ho).elim)

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetAux
