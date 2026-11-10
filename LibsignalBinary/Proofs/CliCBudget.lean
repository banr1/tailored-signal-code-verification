/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.DoReservePlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrowPlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ExactPlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ExactPlacedBudgetAux
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Phase23PlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.Phase23PlacedBudgetAux
public import LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ProofPlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2PlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3BranchesPlacedBudget
public import LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3PlacedBudget
public import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.DropDecodeErrorPlacedBudget
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `CliC` Aggregator and `SignedPortDepsPlaced` Discharge

Proves `<prost::error::DecodeError>::push` (Block `257`) against `decodeErrorPushBoundedSpec`,
constructs `SignedHooksPlaced` from `CodecHooksPlaced`, and discharges all four `CliC`
`SignedPortDepsPlaced` callee contracts (Blocks `559`, `546`, `558`, `555`) from external
allocator/`memcpy` hooks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.CliCBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_258 blkPl_258
  lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym
  lsRustNoAllocShimSym lsRustReallocSym lscall_blk_cl lsmpl
  sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.RustHeap (arrayAt vecAt vecBuf vecHeader vecOf)
open CryptoVerification.LibsignalTripleRatchet (
  KindNoHeap decodeErrorAtStackLen decodeErrorHookStack
  framelessMemcpySpec noAllocShimSpec stackEntryAt
)
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush (
  memRegion_split_entry vecBuf_stackEntryAt_memRegion
)
open CryptoVerification.LibsignalTripleRatchet.Prost (lsHandleAllocErrorSym)
open CryptoVerification.RecordCodecs.Placed (blkPC_257 blkPl_257 lsProg_257)
open CryptoVerification.SpqrV1.Alloc (growOneStrPairStack newCap32 newCap32_toNat)
open CryptoVerification.SpqrV1.Alloc.GrowAmortizedNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.CliC.SpqrV1.Prost.BytesMerge.ExactPlacedBudget (
  bytes_merge_3_exact_placed_ok
)
open LibsignalBinary.Proofs.CliC.SpqrV1.Varint.DecodeVarint2PlacedBudget (
  decodeVarint2_placed_ok
)
open LibsignalBinary.Proofs.CliC.SpqrV1.Varint.SkipField3PlacedBudget (
  skipField3_placed_ok
)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (
  hookSat_noAllocShimBudget_of_withVmPreserved
  hookSat_sessionShimBudget_of_withVmPreserved
)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (
  DecodeErrorPushBoundedEnv SignedHooksPlaced SignedPortDepsPlaced
  decodeErrorPushBoundedSpec decodeVarint2BudgetSpec skipField3BudgetSpec
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget (
  GrowAmortizedEnv fitsEnv_growAmortized_iff growAmortizedEvents
  growOneStrPairSpec grow_one_str_pair_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget (
  decode_error_from_placed_ok
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## Bounded `DecodeError::push` and `SignedHooksPlaced` -/

private theorem stackAt_push_growOne (sp : BitVec 64) :
    stackAt sp decodeErrorHookStack =
      memRegion (sp - 8192#64) 3920 ∗
      stackAt (sp - 64#64) growOneStrPairStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_bottom sp 4272 3920 (by decide)
  change stackAt sp decodeErrorHookStack = memRegion (sp - 8192#64) 3920 ∗ stackAt sp 4272 at h1
  have h2 := stackAt_split_cells sp 4208 8 (by decide)
  change stackAt sp 4272 =
    stackAt (sp - 64#64) growOneStrPairStack ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

private theorem vecBuf_stackEntryAt_memRegion_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (k : Nat) (cap ptr : BitVec 64)
    (hle : k ≤ cap.toNat) (hbound : cap.toNat * 32 < 2 ^ 63) :
    A.live ptr (cap.toNat * 32) 8 ∗
      arrayAt stackEntryAt 32 ptr (List.replicate k ()) ∗
      memRegion (ptr + BitVec.ofNat 64 (k * 32)) ((cap.toNat - k) * 32) =
    A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32) := by
  simpa only [RustCliAllocBudget.repAlloc_live_norm] using
    vecBuf_stackEntryAt_memRegion A.repAlloc k cap ptr hle hbound

private theorem decodeErrorPushBoundedEnv_growAmortizedEvents {n : Nat} (hn : n < 2 ^ 32) :
    DecodeErrorPushBoundedEnv n (growAmortizedEvents (BitVec.ofNat 64 n)) := by
  by_cases hn0 : n = 0
  · subst hn0
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    have h0 : BitVec.ofNat 64 0 = 0#64 := rfl
    rw [h0]
    simp only [growAmortizedEvents, ↓reduceIte,
      (by decide : (newCap32 0#64).toNat = 4)]
  · have htoNat : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hne0 : BitVec.ofNat 64 n ≠ 0#64 := fun h =>
      hn0 (by simpa [htoNat] using congrArg BitVec.toNat h)
    have hnew : (newCap32 (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [newCap32_toNat (by omega), htoNat]
    refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    simp only [growAmortizedEvents, hne0, ↓reduceIte, htoNat, hnew]

private theorem fitsEnv_growAmortized_of_decodeErrorPushBounded {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {n : Nat} (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushBoundedEnv n)) :
    FitsEnv M lim st (GrowAmortizedEnv (BitVec.ofNat 64 n)) := by
  rw [fitsEnv_growAmortized_iff]
  exact hfits _ (decodeErrorPushBoundedEnv_growAmortizedEvents hn)

theorem decode_error_push_bounded_spec_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushBoundedSpec M A lim)) := by
  have hgrow0 : subroutine_ok ((blkPC_258).rebase (blkPl_258).base H) (lsmpl.base 258)
      (withLsCodeLoaded lsmpl (growOneStrPairSpec M A lim)) :=
    grow_one_str_pair_placed_ok (M := M) (A := A) (lim := lim) (H := H)
      h_panic (hookSat_noAllocShimBudget_of_withVmPreserved hshim) halloc hrealloc
  clear h_panic hshim halloc hrealloc
  unfold lsProg_257 withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeErrorPushBoundedSpec decodeErrorAtStackLen vecOf vecAt vecHeader vecBuf
    simp only [List.length_replicate, sepExists_sepConj_left, sepExists_sepConj_right,
      RustCliAllocBudget.repAlloc_live_norm]
    simp only [stackAt_push_growOne]
  wp_init x s0
  obtain ⟨d, e, n, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hn_lt32 : n < 2 ^ 32 := by assumption
  have hfits : FitsEnv M lim st (DecodeErrorPushBoundedEnv n) := by assumption
  have hptr_ne0 : v_stk_2 ≠ 0#64 := by assumption
  obtain ⟨_hkind1, _hkind2⟩ : KindNoHeap v_stk := by assumption
  have hn_toNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  conv =>
    arg 4
    simp only [BitVec.ofNat_eq_ofNat,
      vecBuf_stackEntryAt_memRegion_budget A n v_stk_1 v_stk_2
        (by omega) (by omega)]
  by_cases heq : BitVec.ofNat 64 n = v_stk_1
  · subst v_stk_1
    have hcap_lt : (BitVec.ofNat 64 n).toNat < 2 ^ 32 := by rw [hn_toNat]; exact hn_lt32
    have hfits_grow : FitsEnv M lim st (GrowAmortizedEnv (BitVec.ofNat 64 n)) :=
      fitsEnv_growAmortized_of_decodeErrorPushBounded hn_lt32 hfits
    have hnew_toNat : (newCap32 (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [newCap32_toNat hcap_lt, hn_toNat]
    have hn_lt_new : n < (newCap32 (BitVec.ofNat 64 n)).toNat := by omega
    have hn1_le_new : n + 1 ≤ (newCap32 (BitVec.ofNat 64 n)).toNat := by omega
    have hnew_bound : (newCap32 (BitVec.ofNat 64 n)).toNat * 32 < 2 ^ 63 := by omega
    have hnew_ne0 : newCap32 (BitVec.ofNat 64 n) ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      change (newCap32 (BitVec.ofNat 64 n)).toNat = 0 at ht
      omega
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 258)
    wp_steps_sync_pool (lsmpl.base 258)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl1
    have hgrow := lscall_blk_cl
      (callerProg := (blkPC_257).rebase (blkPl_257).base H)
      (calleeProg := (blkPC_258).rebase (blkPl_258).base H)
      (j := 258) (spec := growOneStrPairSpec M A lim) hgrow0 hcl1
    wp_call hgrow ((e, BitVec.ofNat 64 n, v_stk_2), st)
    wp_simp_pre [
      memRegion_split_entry w n
        (newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    have henv : DecodeErrorPushBoundedEnv n (growAmortizedEvents (BitVec.ofNat 64 n)) :=
      decodeErrorPushBoundedEnv_growAmortizedEvents hn_lt32
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (growAmortizedEvents (BitVec.ofNat 64 n))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (newCap32 (BitVec.ofNat 64 n))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists w
    simp only [BitVec.ofNat_eq_ofNat, hnew_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion_budget A (n + 1)
        (newCap32 (BitVec.ofNat 64 n)) w hn1_le_new hnew_bound,
      memRegion_split_entry w n
        (newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound]
    wp_done
  · have hbeq : (BitVec.ofNat 64 n == v_stk_1) = false := beq_eq_false_iff_ne.mpr heq
    have hne_nat : n ≠ v_stk_1.toNat := by
      intro hnat
      apply heq
      apply BitVec.eq_of_toNat_eq
      rw [hn_toNat, hnat]
    have hn_lt_cap : n < v_stk_1.toNat := by omega
    have hn1_le_cap : n + 1 ≤ v_stk_1.toNat := by omega
    have hcap_ne0 : v_stk_1 ≠ 0#64 := by
      intro h0
      subst h0
      change n < 0 at hn_lt_cap
      omega
    wp_simp_pre [hcap_ne0, ite_false,
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    have henv : DecodeErrorPushBoundedEnv n [] := Or.inl rfl
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists []
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_1
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_2
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ite_false, M.stepEvents_nil,
      vecBuf_stackEntryAt_memRegion_budget A (n + 1) v_stk_1 v_stk_2
        hn1_le_cap (by omega),
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

theorem signedHooksPlaced_of_codecHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    SignedHooksPlaced M A lim H :=
  { dealloc := hH.dealloc
    decodeErrorFrom :=
      subroutine_ok_withLsCodeLoaded_of_plain
        (decode_error_from_placed_ok
          (hookSat_sessionShimBudget_of_withVmPreserved hH.shim) hH.alloc)
    decodeErrorPush :=
      decode_error_push_bounded_spec_placed_ok
        hH.panic_raw hH.shim hH.alloc hH.realloc }

/-! ## `SignedPortDepsPlaced` Discharge -/

private theorem decodeVarint2Spec_eq_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    decodeVarint2Spec A lim = decodeVarint2BudgetSpec M A lim := rfl

private theorem skipField3Spec_eq_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    skipField3Spec A lim = skipField3BudgetSpec M A lim := rfl

theorem signedPortDepsPlaced_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec))
    (_hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    SignedPortDepsPlaced M A lim H := by
  refine SignedPortDepsPlaced.of_prost hdealloc ?_ ?_ ?_
  · rw [← decodeVarint2Spec_eq_budget A lim]
    exact decodeVarint2_placed_ok (hookSat_sessionShimBudget_of_withVmPreserved hshim) halloc
  · rw [← skipField3Spec_eq_budget A lim]
    exact skipField3_placed_ok (hookSat_sessionShimBudget_of_withVmPreserved hshim) halloc
  · exact bytes_merge_3_exact_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_raw

theorem signedPortDepsPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    SignedPortDepsPlaced M A lim H :=
  signedPortDepsPlaced_of_hooks
    hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy hH.panic_alloc hH.panic_raw

end LibsignalBinary.Proofs.CliCBudget
