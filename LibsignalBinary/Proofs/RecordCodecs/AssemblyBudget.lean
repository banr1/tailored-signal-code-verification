/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.Assembly
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecodeBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFromBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserializeBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeErrorBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Record Decoder Assembly

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` assembly for
`RecordCodecs`: proves `<prost::error::DecodeError>::push` (Block `257`),
`prost::encoding::bytes::merge::<Vec<u8>>` (Block `7`), and discharges `PortDepsPlaced` from
`CodecHooksPlaced` for `PreKeyRecord::deserialize`, `IdentityKeyPair::try_from`, and
`IdentityKey::decode`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding decodeErrorPushExternSpecWithStack
open CryptoVerification CryptoVerification.RecordCodecs.Placed
open CryptoVerification.SpqrV1.Alloc.GrowAmortizedNorm
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   rustAllocEvents rustReallocEvents
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocBudgetSpecWithStack subroutine_ok_rustCliAllocBudget_withStack
   subroutine_ok_rustCliDeallocBudget_externWithStack)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorPushEnv decodeErrorPushBudgetSpec decodeErrorPushBudgetSpecWithStack
   withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (CodecHooksPlaced PortDepsPlaced DecodeErrorPushBoundedEnv
   decodeErrorPushBoundedExternBudgetSpecWithStack decodeErrorPushBoundedExternSpecWithStack
   preKeyDeserializePlacedSpec identityKeyPairTryFromPlacedSpec identityKeyDecodePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget
  (GrowAmortizedEnv growAmortizedEvents growOneStrPairSpec grow_one_str_pair_placed_ok
   fitsEnv_growAmortized_iff
   decodeErrorPushEnv_growAmortizedEvents fitsEnv_growAmortized_of_decodeErrorPush)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec framelessMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserveBudget
  (do_reserve_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.DropsBudget
  (bytesVtableDrop_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Bytes.FromBudget
  (bytesFromVec_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeErrorPushExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeRawSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget
  (bmMemcpy_placed_of_frameless bmShim_placed_of_base)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget
  (bytes_merge_placed_ok_of_contracts_x)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeErrorBudget
  (drop_decode_error_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget
  (int32_merge_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux
  (decode_varint_slow_placed_ok_x decode_varint_slow_placed_ok_with_stack_of_hooks)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldBudget
  (skipField_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
  (decode_error_from_placed_ok_gen decode_error_from_placed_ok_x decode_varint_slice_placed_ok_x)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. `HookSat` Bridges from `CodecHooksPlaced` -/

theorem hookSat_sessionShimBudget_of_withVmPreserved {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym (withVmPreserved noAllocShimSpec)) :
    HookSat H sym sessionShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hrest

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

theorem hookSat_framelessMemcpyBudget_of_withVmPreserved {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym (withVmPreserved framelessMemcpySpec)) :
    HookSat H sym framelessMemcpyBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, framelessMemcpySpec, framelessMemcpyBudgetSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

/-! ## 2. `<prost::error::DecodeError>::push` (Block `257`) -/

private theorem stackAt_push_growOne (sp : BitVec 64) :
    stackAt sp decodeErrorHookStack =
      memRegion (sp - 8192#64) 3920 ∗
      stackAt (sp - 64#64) SpqrV1.Alloc.growOneStrPairStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_bottom sp 4272 3920 (by decide)
  change stackAt sp decodeErrorHookStack = memRegion (sp - 8192#64) 3920 ∗ stackAt sp 4272 at h1
  have h2 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 4208 8 (by decide)
  change stackAt sp 4272 =
    stackAt (sp - 64#64) SpqrV1.Alloc.growOneStrPairStack ∗ cells (sp - 64#64) 8 at h2
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
    InImage.DecodeErrorPush.vecBuf_stackEntryAt_memRegion A.repAlloc k cap ptr hle hbound

/-- Relocatable `<prost::error::DecodeError>::push` (Block `257`) meets
`withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)`, calling
`grow_one_str_pair_placed_ok` (Block `258`) on the slow path. -/
theorem decode_error_push_spec_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) := by
  have hgrow0 : subroutine_ok ((blkPC_258).rebase (blkPl_258).base H) (lsmpl.base 258)
      (CryptoVerification.withLsCodeLoaded lsmpl (growOneStrPairSpec M A lim)) :=
    grow_one_str_pair_placed_ok (M := M) (A := A) (lim := lim) (H := H)
      h_panic (hookSat_noAllocShimBudget_of_withVmPreserved hshim) halloc hrealloc
  clear h_panic hshim halloc hrealloc
  unfold lsProg_257 withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeErrorPushBudgetSpec decodeErrorAtStackLen vecOf vecAt vecHeader vecBuf
    simp only [List.length_replicate, sepExists_sepConj_left, sepExists_sepConj_right,
      RustCliAllocBudget.repAlloc_live_norm]
    simp only [stackAt_push_growOne]
  wp_init x s0
  obtain ⟨d, e, n, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hn_lt32 : n < 2 ^ 32 := by assumption
  have hfits : FitsEnv M lim st (DecodeErrorPushEnv n) := by assumption
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
      fitsEnv_growAmortized_of_decodeErrorPush hn_lt32 hfits
    have hnew_toNat : (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [SpqrV1.Alloc.newCap32_toNat hcap_lt, hn_toNat]
    have hn_lt_new : n < (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat := by omega
    have hn1_le_new : n + 1 ≤ (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat := by omega
    have hnew_bound : (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat * 32 < 2 ^ 63 := by omega
    have hnew_ne0 : SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n) ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      change (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat = 0 at ht
      omega
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 258)
    wp_steps_sync_pool (lsmpl.base 258)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl1
    have hgrow := CryptoVerification.lscall_blk_cl
      (callerProg := (blkPC_257).rebase (blkPl_257).base H)
      (calleeProg := (blkPC_258).rebase (blkPl_258).base H)
      (j := 258) (spec := growOneStrPairSpec M A lim) hgrow0 hcl1
    wp_call hgrow ((e, BitVec.ofNat 64 n, v_stk_2), st)
    wp_simp_pre [
      InImage.DecodeErrorPush.memRegion_split_entry w n
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    have henv : DecodeErrorPushEnv n (growAmortizedEvents (BitVec.ofNat 64 n)) :=
      decodeErrorPushEnv_growAmortizedEvents hn_lt32
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (growAmortizedEvents (BitVec.ofNat 64 n))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists
      (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists w
    simp only [BitVec.ofNat_eq_ofNat, hnew_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion_budget A (n + 1)
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)) w hn1_le_new hnew_bound,
      InImage.DecodeErrorPush.memRegion_split_entry w n
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound]
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
      InImage.DecodeErrorPush.memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    have henv : DecodeErrorPushEnv n [] := Or.inl rfl
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists []
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_1
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_2
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ite_false, M.stepEvents_nil,
      vecBuf_stackEntryAt_memRegion_budget A (n + 1) v_stk_1 v_stk_2
        hn1_le_cap (by omega),
      InImage.DecodeErrorPush.memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

/-- Lift `withLsCodeLoaded pl (decodeErrorPushBudgetSpec M A lim)` to
`withLsCodeLoaded pl (decodeErrorPushExternSpecWithStack M A lim hookStack)` for any
`decodeErrorHookStack ≤ hookStack ≤ 2 ^ 64`. -/
theorem decodeErrorPushExternWithStack_lscl_of_spec {pl : Obj.MultiPlacement}
    {P : Program} {addr : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hookStack : Nat}
    (h : subroutine_ok P addr (withLsCodeLoaded pl (decodeErrorPushBudgetSpec M A lim)))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr
      (withLsCodeLoaded pl (decodeErrorPushExternSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n, st⟩ R s0 hpc hrun hpre hal => ?_
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [decodeErrorPushExternSpecWithStack,
    LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.decodeErrorPushExternBudgetSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, he_ne, hn, hfits⟩, hmem⟩
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp decodeErrorHookStack
      (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre_raw : s0.mem ⊨ (decodeErrorPushBudgetSpec M A lim).pre (d, e, n, st) s0 ∗ R' := by
    dsimp only [decodeErrorPushBudgetSpec, R']
    rw [hsplit] at hmem
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hn, hfits⟩, by ac_nf at hmem ⊢⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl (decodeErrorPushBudgetSpec M A lim)).pre (d, e, n, st) s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre_raw⟩
  refine h.mono_outcome (d, e, n, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hpost ⊢
    simp only [decodeErrorPushBudgetSpec, decodeErrorPushExternSpecWithStack,
      LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget.decodeErrorPushExternBudgetSpecWithStack, R',
      sepConj_assoc, sepExists_sepConj_left, satisfies_pure_sepConj, satisfies_sepExists] at hpost ⊢
    refine ⟨hpost.1, e, he_ne, ?_⟩
    rw [hsplit]
    have hm := hpost.2
    ac_nf at hm ⊢
  · dsimp only [withLsCodeLoaded, decodeErrorPushBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact hpan.1.elim
  · dsimp only [withLsCodeLoaded, decodeErrorPushBudgetSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1.elim
  · dsimp only [withLsCodeLoaded, decodeErrorPushBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.elim

/-- Relocatable `<prost::error::DecodeError>::push` (Block `257`) meets
`withLsCodeLoaded lsmpl (decodeErrorPushExternSpecWithStack M A lim (2 * extHookStack))`. -/
theorem decode_error_push_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushExternSpecWithStack M A lim (2 * extHookStack))) :=
  decodeErrorPushExternWithStack_lscl_of_spec
    (decode_error_push_spec_placed_ok h_panic hshim halloc hrealloc)

private def decodeErrorPushBoundedBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (d, e, n, st) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32 ∧ FitsEnv M lim st (DecodeErrorPushBoundedEnv n)⌝ ∗
      (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗
      A.pool lim st s ∗ stackAt s.sp decodeErrorHookStack
  post := fun (d, e, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorPushBoundedEnv n evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp decodeErrorHookStack

private theorem decodeErrorPushBoundedEnv_growAmortizedEvents {n : Nat} (hn : n < 2 ^ 32) :
    DecodeErrorPushBoundedEnv n (growAmortizedEvents (BitVec.ofNat 64 n)) := by
  by_cases hn0 : n = 0
  · subst hn0
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    have h0 : BitVec.ofNat 64 0 = 0#64 := rfl
    rw [h0]
    simp only [growAmortizedEvents, ↓reduceIte,
      (by decide : (SpqrV1.Alloc.newCap32 0#64).toNat = 4)]
  · have htoNat : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hne0 : BitVec.ofNat 64 n ≠ 0#64 := fun h =>
      hn0 (by simpa [htoNat] using congrArg BitVec.toNat h)
    have hnew : (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [SpqrV1.Alloc.newCap32_toNat (by omega), htoNat]
    refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    simp only [growAmortizedEvents, hne0, ↓reduceIte, htoNat, hnew]

private theorem fitsEnv_growAmortized_of_decodeErrorPushBounded {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {n : Nat} (hn : n < 2 ^ 32)
    (hfits : FitsEnv M lim st (DecodeErrorPushBoundedEnv n)) :
    FitsEnv M lim st (GrowAmortizedEnv (BitVec.ofNat 64 n)) := by
  rw [fitsEnv_growAmortized_iff]
  exact hfits _ (decodeErrorPushBoundedEnv_growAmortizedEvents hn)

private theorem decode_error_push_bounded_spec_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushBoundedBudgetSpec M A lim)) := by
  have hgrow0 : subroutine_ok ((blkPC_258).rebase (blkPl_258).base H) (lsmpl.base 258)
      (CryptoVerification.withLsCodeLoaded lsmpl (growOneStrPairSpec M A lim)) :=
    grow_one_str_pair_placed_ok (M := M) (A := A) (lim := lim) (H := H)
      h_panic (hookSat_noAllocShimBudget_of_withVmPreserved hshim) halloc hrealloc
  clear h_panic hshim halloc hrealloc
  unfold lsProg_257 withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeErrorPushBoundedBudgetSpec decodeErrorAtStackLen vecOf vecAt vecHeader vecBuf
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
    have hnew_toNat : (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [SpqrV1.Alloc.newCap32_toNat hcap_lt, hn_toNat]
    have hn_lt_new : n < (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat := by omega
    have hn1_le_new : n + 1 ≤ (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat := by omega
    have hnew_bound : (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat * 32 < 2 ^ 63 := by omega
    have hnew_ne0 : SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n) ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      change (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat = 0 at ht
      omega
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 258)
    wp_steps_sync_pool (lsmpl.base 258)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl1
    have hgrow := CryptoVerification.lscall_blk_cl
      (callerProg := (blkPC_257).rebase (blkPl_257).base H)
      (calleeProg := (blkPC_258).rebase (blkPl_258).base H)
      (j := 258) (spec := growOneStrPairSpec M A lim) hgrow0 hcl1
    wp_call hgrow ((e, BitVec.ofNat 64 n, v_stk_2), st)
    wp_simp_pre [
      InImage.DecodeErrorPush.memRegion_split_entry w n
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound,
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
      (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists w
    simp only [BitVec.ofNat_eq_ofNat, hnew_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion_budget A (n + 1)
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)) w hn1_le_new hnew_bound,
      InImage.DecodeErrorPush.memRegion_split_entry w n
        (SpqrV1.Alloc.newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound]
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
      InImage.DecodeErrorPush.memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega),
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
      InImage.DecodeErrorPush.memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

private theorem decodeErrorPushBoundedExternWithStack_lscl_of_spec {pl : Obj.MultiPlacement}
    {P : Program} {addr : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hookStack : Nat}
    (h : subroutine_ok P addr (withLsCodeLoaded pl (decodeErrorPushBoundedBudgetSpec M A lim)))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr
      (withLsCodeLoaded pl (decodeErrorPushBoundedExternSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n, st⟩ R s0 hpc hrun hpre hal => ?_
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [decodeErrorPushBoundedExternSpecWithStack,
    decodeErrorPushBoundedExternBudgetSpecWithStack,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, he_ne, hn, hfits⟩, hmem⟩
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp decodeErrorHookStack
      (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre_raw : s0.mem ⊨ (decodeErrorPushBoundedBudgetSpec M A lim).pre (d, e, n, st) s0 ∗ R' := by
    dsimp only [decodeErrorPushBoundedBudgetSpec, R']
    rw [hsplit] at hmem
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hn, hfits⟩, by ac_nf at hmem ⊢⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl (decodeErrorPushBoundedBudgetSpec M A lim)).pre (d, e, n, st) s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre_raw⟩
  refine h.mono_outcome (d, e, n, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hpost ⊢
    simp only [decodeErrorPushBoundedBudgetSpec, decodeErrorPushBoundedExternSpecWithStack,
      decodeErrorPushBoundedExternBudgetSpecWithStack, R',
      sepConj_assoc, sepExists_sepConj_left, satisfies_pure_sepConj, satisfies_sepExists] at hpost ⊢
    refine ⟨hpost.1, e, he_ne, ?_⟩
    rw [hsplit]
    have hm := hpost.2
    ac_nf at hm ⊢
  · dsimp only [withLsCodeLoaded, decodeErrorPushBoundedBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact hpan.1.elim
  · dsimp only [withLsCodeLoaded, decodeErrorPushBoundedBudgetSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact hex.1.elim
  · dsimp only [withLsCodeLoaded, decodeErrorPushBoundedBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.elim

private theorem decode_error_push_bounded_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushBoundedExternSpecWithStack M A lim (2 * extHookStack))) :=
  decodeErrorPushBoundedExternWithStack_lscl_of_spec
    (decode_error_push_bounded_spec_placed_ok h_panic hshim halloc hrealloc)

/-! ## 3. `bytes_merge_placed_ok_x` & `PortDepsPlaced` Assembly -/

theorem bytes_merge_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A lim)) := by
  have hshim_s := hookSat_sessionShimBudget_of_withVmPreserved hshim
  have hshim_n := hookSat_noAllocShimBudget_of_withVmPreserved hshim
  exact bytes_merge_placed_ok_of_contracts_x
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_error_from_placed_ok_x hshim_s halloc))
    (bmMemcpy_placed_of_frameless (ls_hook_ok_of_mem hmc))
    (bmShim_placed_of_base (ls_hook_ok_of_mem hshim_s))
    (Prost.subroutine_ok_withLsCl_of_plain
      (subroutine_ok_rustCliAllocBudget_withStack (stk := extHookStack) (by decide) (by decide)
        (ls_hook_ok_of_mem halloc)))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_varint_slow_placed_ok_with_stack_of_hooks
        (errStack := Prost.decodeErrorHookStackX) hshim_s halloc))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_varint_slice_placed_ok_x hshim_s halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (do_reserve_placed_ok_x hshim_n halloc hrealloc))
    (fun tmpPtr v =>
      Prost.subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok_x (callerProg := (blkPC_7).rebase (blkPl_7).base H) (i := 7)
          hdealloc (by decide) tmpPtr v v.length))

theorem bytes_merge_exact_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget.bytesMergeExactRawSpecX A lim)) := by
  have hshim_s := hookSat_sessionShimBudget_of_withVmPreserved hshim
  have hshim_n := hookSat_noAllocShimBudget_of_withVmPreserved hshim
  exact LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1Budget.bytes_merge_placed_ok_of_contracts_exact_x
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_error_from_placed_ok_x hshim_s halloc))
    (bmMemcpy_placed_of_frameless (ls_hook_ok_of_mem hmc))
    (bmShim_placed_of_base (ls_hook_ok_of_mem hshim_s))
    (Prost.subroutine_ok_withLsCl_of_plain
      (subroutine_ok_rustCliAllocBudget_withStack (stk := extHookStack) (by decide) (by decide)
        (ls_hook_ok_of_mem halloc)))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_varint_slow_placed_ok_with_stack_of_hooks
        (errStack := Prost.decodeErrorHookStackX) hshim_s halloc))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (decode_varint_slice_placed_ok_x hshim_s halloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_7).rebase (blkPl_7).base H)
      (do_reserve_placed_ok_x hshim_n halloc hrealloc))
    (fun tmpPtr v =>
      Prost.subroutine_ok_withLsCl_of_withLsCodeLoaded
        (bytesVtableDrop_placed_ok_x (callerProg := (blkPC_7).rebase (blkPl_7).base H) (i := 7)
          hdealloc (by decide) tmpPtr v v.length))

/-- Discharge all `PortDepsPlaced` callee contracts from external `CodecHooksPlaced`. -/
theorem portDepsPlaced_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    PortDepsPlaced M A lim H := by
  have hshim_s := hookSat_sessionShimBudget_of_withVmPreserved hH.shim
  exact
    { varintSlice := decode_varint_slice_placed_ok_x hshim_s hH.alloc
      int32Merge := int32_merge_placed_ok_x hshim_s hH.alloc
      skipField := skipField_placed_ok_x hshim_s hH.alloc
      dropDecodeError := drop_decode_error_placed_ok_x hH.dealloc
      bytesMerge := bytes_merge_placed_ok_x hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy
      pkTryFrom := pkTryFrom_placed_ok H
      varintSlow := decode_varint_slow_placed_ok_with_stack_of_hooks
        (errStack := 2 * extHookStack) hshim_s hH.alloc
      decodeErrorFrom := decode_error_from_placed_ok_gen hshim_s hH.alloc
      decodeErrorPush := decode_error_push_bounded_placed_ok hH.panic_raw hH.shim hH.alloc hH.realloc
      dealloc := hH.dealloc }

/-- `PreKeyRecord::deserialize` (Block `65`) under `[LibsignalPlacement]` from external hooks
`CodecHooksPlaced M A lim H`. -/
theorem preKeyRecord_deserialize_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : CodecHooksPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (blkPl_65).base (preKeyDeserializePlacedSpec A lim) :=
  PreKeyDeserializeBudget.preKeyRecord_deserialize_placed_ok (portDepsPlaced_of_hooks hH)

/-- `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`) under `[LibsignalPlacement]`
from external hooks `CodecHooksPlaced M A lim H`. -/
theorem identityKeyPair_tryFrom_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : CodecHooksPlaced M A lim H) :
    subroutine_ok (lsProg_84 H) (blkPl_84).base (identityKeyPairTryFromPlacedSpec A lim) :=
  IdentityKeyPairTryFromBudget.identityKeyPair_tryFrom_placed_ok (portDepsPlaced_of_hooks hH)

/-- `IdentityKey::decode` (Block `18`) under `[LibsignalPlacement]` for any hooks `H`. -/
theorem identityKey_decode_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedSpec A) :=
  IdentityKeyDecodeBudget.identityKey_decode_placed_ok H

end LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
