/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `<prost::error::DecodeError>::push` (Block `257`)

Proves `decodeErrorPushMergeBudgetSpec M A lim` on Block `257` (`<prost::error::DecodeError>::push`)
under `withLsCodeLoaded lsmpl` via Block `258` (`GrowAmortizedBudget.grow_one_str_pair_placed_ok`),
together with own-block `blockProgram` and cross-block `[IsLsBlockProg]` transfer corollaries.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DecodeErrorPushMergePlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_258 blkPl_258 libsignalMutatedBlocks libsignalSessionLib
  lsHandleErrorSym lsRustAllocSym lsRustNoAllocShimSym lsRustReallocSym
  ls_blockPlacement_base ls_subroutine_ok_cl_of_block ls_subroutine_ok_of_block
  lscall_blk_cl lsmpl sepWP_seq_lscl withLsCl withLsCodeLoaded
)
open CryptoVerification.RecordCodecs.Placed (blkPC_257 blkPl_257 lsProg_257)
open CryptoVerification.RustHeap (arrayAt vecAt vecBuf vecHeader vecOf)
open CryptoVerification.LibsignalTripleRatchet (
  KindNoHeap decodeErrorAtStackLen decodeErrorHookStack
  keys_ls_subroutine_ok_of_block_cro noAllocShimSpec
  stackEntryAt subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush (
  memRegion_split_entry vecBuf_stackEntryAt_memRegion
)
open CryptoVerification.SpqrV1.Alloc (growOneStrPairStack newCap32 newCap32_toNat)
open CryptoVerification.SpqrV1.Alloc.GrowAmortizedNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget (
  GrowAmortizedEnv fitsEnv_growAmortized_iff growAmortizedEvents
  growOneStrPairSpec grow_one_str_pair_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget (
  DecodeErrorPushMergeEnv decodeErrorPushMergeBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. Envelope Containment & `HookSat` Bridges -/

/-- Every `growAmortizedEvents (BitVec.ofNat 64 n)` trace (`n < 2 ^ 32`) lies in
`ChunkedDefsBudget.DecodeErrorPushMergeEnv n`. -/
theorem decodeErrorPushMergeEnv_growAmortizedEvents {n : Nat} (hn : n < 2 ^ 32) :
    DecodeErrorPushMergeEnv n (growAmortizedEvents (BitVec.ofNat 64 n)) := by
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

/-- `FitsEnv` monotonicity from `DecodeErrorPushMergeEnv n` to
`GrowAmortizedEnv (BitVec.ofNat 64 n)` (`n < 2 ^ 32`). -/
theorem fitsEnv_growAmortized_of_decodeErrorPushMerge {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {n : Nat} (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushMergeEnv n)) :
    FitsEnv M lim st (GrowAmortizedEnv (BitVec.ofNat 64 n)) := by
  rw [fitsEnv_growAmortized_iff]
  exact hfits _ (decodeErrorPushMergeEnv_growAmortizedEvents hn)

/-- Bridge `HookSat H sym (withVmPreserved noAllocShimSpec)` to `HookSat H sym noAllocShimBudgetSpec`. -/
theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym (withVmPreserved noAllocShimSpec)) :
    HookSat H sym noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-- Mangled `lsHandleErrorSym` (`_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error`) is outside
demangled `Rust.isPanicSymbol` (it is handled by `cliPanicSymbolsPlaced` in `ext`). -/
theorem isPanicSymbol_lsHandleErrorSym :
    Rust.isPanicSymbol lsHandleErrorSym = false := by
  simp [Rust.isPanicSymbol, lsHandleErrorSym]

theorem isPanicSymbol_lsRustNoAllocShimSym :
    Rust.isPanicSymbol lsRustNoAllocShimSym = false := by
  simp [Rust.isPanicSymbol, lsRustNoAllocShimSym]

theorem isPanicSymbol_lsRustAllocSym :
    Rust.isPanicSymbol lsRustAllocSym = false := by
  simp [Rust.isPanicSymbol, lsRustAllocSym]

theorem isPanicSymbol_lsRustReallocSym :
    Rust.isPanicSymbol lsRustReallocSym = false := by
  simp [Rust.isPanicSymbol, lsRustReallocSym]

/-- Lift `HookSat ext sym spec` across `Rust.withPanics ext` for any non-panic external symbol. -/
theorem hookSat_withPanics_of_not_isPanicSymbol {α : Type}
    {ext : LibsignalHooks} {sym : String} {spec : Spec α}
    (hnp : Rust.isPanicSymbol sym = false)
    (hsat : HookSat ext sym spec) :
    HookSat (Rust.withPanics ext) sym spec := by
  rcases hsat with ⟨f, hf, hok⟩
  refine ⟨f, ?_, hok⟩
  simp [Rust.withPanics, hnp, hf]

/-- `Rust.withPanics ext` preserves `ext`'s binding on mangled `lsHandleErrorSym`. -/
theorem withPanics_lsHandleErrorSym_eq (ext : LibsignalHooks) :
    Rust.withPanics ext lsHandleErrorSym = ext lsHandleErrorSym := by
  simp [Rust.withPanics, isPanicSymbol_lsHandleErrorSym]

/-! ## 2. Stack & Buffer Helpers and Block `257` Stepping Proof -/

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
  have h2 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 4208 8 (by decide)
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

/-- Relocatable `<prost::error::DecodeError>::push` (Block `257`) meets
`withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)` under `noAllocShimBudgetSpec`. -/
theorem decode_error_push_merge_placed_ok_of_budgetShim [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) := by
  have hgrow0 : subroutine_ok ((blkPC_258).rebase (blkPl_258).base H) (lsmpl.base 258)
      (withLsCodeLoaded lsmpl (growOneStrPairSpec M A lim)) :=
    grow_one_str_pair_placed_ok (M := M) (A := A) (lim := lim) (H := H)
      h_panic hshim halloc hrealloc
  clear h_panic hshim halloc hrealloc
  unfold lsProg_257 withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeErrorPushMergeBudgetSpec decodeErrorAtStackLen vecOf vecAt vecHeader vecBuf
    simp only [List.length_replicate, sepExists_sepConj_left, sepExists_sepConj_right,
      RustCliAllocBudget.repAlloc_live_norm]
    simp only [stackAt_push_growOne]
  wp_init x s0
  obtain ⟨d, e, n, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hn_lt32 : n < 2 ^ 32 := by assumption
  have hfits : FitsEnv M lim st (DecodeErrorPushMergeEnv n) := by assumption
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
      fitsEnv_growAmortized_of_decodeErrorPushMerge hn_lt32 hfits
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
    have henv : DecodeErrorPushMergeEnv n (growAmortizedEvents (BitVec.ofNat 64 n)) :=
      decodeErrorPushMergeEnv_growAmortizedEvents hn_lt32
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
    have henv : DecodeErrorPushMergeEnv n [] := Or.inl rfl
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists []
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_1
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_2
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ite_false, M.stepEvents_nil,
      vecBuf_stackEntryAt_memRegion_budget A (n + 1) v_stk_1 v_stk_2
        hn1_le_cap (by omega),
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

/-- Relocatable `<prost::error::DecodeError>::push` (Block `257`) meets
`withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)`, calling
`grow_one_str_pair_placed_ok` (Block `258`) on the slow path. -/
theorem decode_error_push_merge_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  decode_error_push_merge_placed_ok_of_budgetShim h_panic
    (hookSat_noAllocShimBudget_of_withVmPreserved hshim) halloc hrealloc

/-! ## 3. Own-Block `blockProgram` and Generic `[IsLsBlockProg]` Caller Corollaries -/

/-- Own-block `libsignalSessionLib.blockProgram lsmpl 257 H` corollary under `withLsCodeLoaded`. -/
theorem decode_error_push_merge_blockProgram_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) := by
  have hok := decode_error_push_merge_placed_ok h_panic hshim halloc hrealloc
  rwa [IsLsBlockProg.eq_blockProgram (prog := lsProg_257 H) (i := 257) (H := H),
    ls_blockPlacement_base lsmpl 257] at hok

/-- Own-block `libsignalSessionLib.blockProgram lsmpl 257 H` corollary under `withLsCodeRoLoaded`. -/
theorem decode_error_push_merge_blockProgram_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (decode_error_push_merge_blockProgram_cl h_panic hshim halloc hrealloc)

/-- Own-block `libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext)` corollary under
`withLsCodeLoaded`. -/
theorem decode_error_push_merge_blockProgram_withPanics_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks}
    (h_panic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  decode_error_push_merge_blockProgram_cl
    ((withPanics_lsHandleErrorSym_eq ext).trans h_panic)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustNoAllocShimSym hshim)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustAllocSym halloc)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustReallocSym hrealloc)

/-- Own-block `libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext)` corollary under
`withLsCodeRoLoaded`. -/
theorem decode_error_push_merge_blockProgram_withPanics_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : LibsignalHooks}
    (h_panic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (decode_error_push_merge_blockProgram_withPanics_cl h_panic hshim halloc hrealloc)

/-- Generic cross-block `[IsLsBlockProg callerProg i H]` transfer at `(lsmpl.base 257)` under
`withLsCl`. -/
theorem decode_error_push_merge_at_block_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCl lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg) (calleeProg := lsProg_257 H)
    (decode_error_push_merge_placed_ok h_panic hshim halloc hrealloc) hi

/-- Generic cross-block `[IsLsBlockProg callerProg i H]` transfer at `(lsmpl.base 257)` under
`withLsCodeLoaded`. -/
theorem decode_error_push_merge_at_block_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (calleeProg := lsProg_257 H)
    (decode_error_push_merge_placed_ok h_panic hshim halloc hrealloc) hi

/-- Generic cross-block `[IsLsBlockProg callerProg i H]` transfer at `(lsmpl.base 257)` under
`withLsCodeRoLoaded`. -/
theorem decode_error_push_merge_at_block_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (callerProg := callerProg) (calleeProg := lsProg_257 H)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (decode_error_push_merge_placed_ok h_panic hshim halloc hrealloc)) hi

/-- Generic cross-block `[IsLsBlockProg callerProg i (Rust.withPanics ext)]` transfer at
`(lsmpl.base 257)` under `withLsCodeLoaded`. -/
theorem decode_error_push_merge_at_block_withPanics_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {ext : LibsignalHooks}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h_panic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  decode_error_push_merge_at_block_cl
    ((withPanics_lsHandleErrorSym_eq ext).trans h_panic)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustNoAllocShimSym hshim)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustAllocSym halloc)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustReallocSym hrealloc) hi

/-- Generic cross-block `[IsLsBlockProg callerProg i (Rust.withPanics ext)]` transfer at
`(lsmpl.base 257)` under `withLsCodeRoLoaded`. -/
theorem decode_error_push_merge_at_block_withPanics_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {ext : LibsignalHooks}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h_panic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) :=
  decode_error_push_merge_at_block_cro
    ((withPanics_lsHandleErrorSym_eq ext).trans h_panic)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustNoAllocShimSym hshim)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustAllocSym halloc)
    (hookSat_withPanics_of_not_isPanicSymbol isPanicSymbol_lsRustReallocSym hrealloc) hi

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DecodeErrorPushMergePlacedBudget
