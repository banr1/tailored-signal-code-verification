/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Int32ArmsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Capacity-Bounded Loop Helpers and `<DecodeError>::push` Contracts

Bounded `<DecodeError>::push` (Block `257`) contracts over `DecodeErrorPushBoundedEnv`,
capacity-tracking `ProtoPreKeySignalMessage` invariants (`WirePreKeyCapsMatch`,
`wirePreKeyLoopCapsOf`), and slice/capacity-indexed `preKeyLoopExitPostPlaced` and
`decodeErrorPushPK_tail_placed_wpX` lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkLib_eq_111 blkPC_111 blkPC_258 blkPl_111 blkPl_258 checkBlockSymAtU
   extract_withLsCodeLoaded libsignalMutatedBlocks lsHandleErrorSym lsRustAllocSym
   lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym ls_blockPlacement_ρ
   ls_hook_ok_of_mem ls_resolve_block_ultra lscall_blk_cl lsmpl sepWP_seq_lscl
   withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecAt vecBuf vecHeader vecOf vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded blkPl_85 decodeErrorAtStackLen decodeErrorHookStack
   extHookStack noAllocShimSpec reserveCap stackEntryAt withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk bytesMergeCapOk_of_len_lt32 optU32At optVecU8At skipFieldStackX
   sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp VRegsAt entails_of_eq pure_true_emp sepExists_intro
   sliceCursorAfter_eq_take_cursorAt stackAt_sub_split tryFromPlacedProg)
open CryptoVerification.RecordCodecs.Placed (blkPC_257 blkPl_257 lsProg_257)
open CryptoVerification.SpqrV1.Alloc (growOneStrPairStack newCap32 newCap32_toNat)
open CryptoVerification.SpqrV1.Alloc.GrowAmortizedNorm
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (keepsFrozenInv_codeRoLoaded ls_subroutine_ok_cro_of_block ls_subroutine_ok_pk_of_cl
   preKeyPlacedProg withPreKeyInv)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (emptyProto)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
  (PreKeyLoopExitStatePlaced PreKeyLoopRegs WirePreKeyGhost memRegion64_split8_448
   preKeyLoopExitMem preKeyLoopExitMem_append_prefix preKeyLoopExitMem_err_intro
   subroutine_ok_withLsCodeRoLoaded_of_cl subroutine_ok_withLsCodeRoLoaded_of_plain'
   wirePreKeyAt wirePreKeyAt_split_baseKey wirePreKeyAt_split_identityKey
   wirePreKeyAt_split_kyberCt wirePreKeyAt_split_message wirePreKeyOf wirePreKeyU32s)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
  (hookSat_noAllocShimBudget_of_withVmPreserved portDepsPlaced_of_hooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowAmortizedBudget
  (GrowAmortizedEnv growAmortizedEvents growOneStrPairSpec grow_one_str_pair_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternWithStack_of_rustDealloc)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (DecodeErrorPushBoundedEnv TripleRatchetHooksWPlaced bmNextCap
   decodeErrorPushBoundedSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (SigTryFromCaps SigTryFromField SigTryFromLoopBoundedEnv TryFromLoopEnv
   fitsEnv_sigLoop_pushAfterFrom noPanicQp optFieldCapMatch optFieldCapMatch_init
   sepWPp_call_noPanic_placed sepWPp_end_noPanic_placed sepWPp_frame_noPanic)

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk

private theorem hl_bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem hl_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega
private theorem hl_bv_add_neg_64 (sp' : BitVec 64) :
    sp' + 512#64 + bv% (2 ^ 64 - 64) = sp' + 448#64 := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  hl_bv_sub_add_lit hl_bv_sub_sub_lit hl_bv_add_neg_64 BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. Bounded `<DecodeError>::push` (Block `257`) & `TripleRatchetHooksWPlaced` -/

/-- Every `growAmortizedEvents (BitVec.ofNat 64 n)` trace (`n < 2 ^ 32`) satisfies `DecodeErrorPushBoundedEnv n`. -/
theorem decodeErrorPushBoundedEnv_growAmortizedEvents {n : Nat} (hn : n < 2 ^ 32) :
    DecodeErrorPushBoundedEnv n (growAmortizedEvents (BitVec.ofNat 64 n)) := by
  by_cases hn0 : n = 0
  · subst hn0
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
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

theorem fitsEnv_growAmortized_of_decodeErrorPushBounded {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {n : Nat} (hn : n < 2 ^ 32)
    (h : FitsEnv M lim st (DecodeErrorPushBoundedEnv n)) :
    FitsEnv M lim st (GrowAmortizedEnv (BitVec.ofNat 64 n)) :=
  fun _ hevs => hevs ▸ h _ (decodeErrorPushBoundedEnv_growAmortizedEvents hn)

/-- Tight Block `257` contract at `decodeErrorHookStack` guarded by `DecodeErrorPushBoundedEnv`. -/
def decodeErrorPushBoundedBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (d, e, n, st) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32 ∧ FitsEnv M lim st (DecodeErrorPushBoundedEnv n)⌝ ∗
      (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗
      A.pool lim st s ∗ stackAt s.sp decodeErrorHookStack
  post := fun (d, e, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorPushBoundedEnv n evs⌝ ∗
        (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp decodeErrorHookStack)

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
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.vecBuf_stackEntryAt_memRegion
      A.repAlloc k cap ptr hle hbound

/-- Relocatable `<prost::error::DecodeError>::push` (Block `257`) satisfies
`withLsCodeLoaded lsmpl (decodeErrorPushBoundedBudgetSpec M A lim)`. -/
theorem decode_error_push_bounded_spec_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushBoundedBudgetSpec M A lim)) := by
  have hgrow0 : subroutine_ok ((blkPC_258).rebase (blkPl_258).base H) (lsmpl.base 258)
      (withLsCodeLoaded lsmpl (growOneStrPairSpec M A lim)) :=
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
    refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl1
    have hgrow := lscall_blk_cl
      (callerProg := (blkPC_257).rebase (blkPl_257).base H)
      (calleeProg := (blkPC_258).rebase (blkPl_258).base H)
      (j := 258) (spec := growOneStrPairSpec M A lim) hgrow0 hcl1
    wp_call hgrow ((e, BitVec.ofNat 64 n, v_stk_2), st)
    wp_simp_pre [
      CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.memRegion_split_entry w n
        (newCap32 (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_elim; intro c0
    apply ProofLib.SepWP.exists_elim; intro c1
    apply ProofLib.SepWP.exists_elim; intro c2
    apply ProofLib.SepWP.exists_elim; intro c3
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
      CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.memRegion_split_entry w n
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
      CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.memRegion_split_entry
        v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_elim; intro c0
    apply ProofLib.SepWP.exists_elim; intro c1
    apply ProofLib.SepWP.exists_elim; intro c2
    apply ProofLib.SepWP.exists_elim; intro c3
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
      CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.memRegion_split_entry
        v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

/-- Lift `decodeErrorPushBoundedBudgetSpec` to `decodeErrorPushBoundedSpecWithStack`. -/
theorem decodeErrorPushBoundedWithStack_lscl_of_spec {pl : Obj.MultiPlacement}
    {P : Program} {addr : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {hookStack : Nat}
    (h : subroutine_ok P addr (withLsCodeLoaded pl (decodeErrorPushBoundedBudgetSpec M A lim)))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr
      (withLsCodeLoaded pl (decodeErrorPushBoundedSpecWithStack M A lim hookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n, st⟩ R s0 hpc hrun hpre hal => ?_
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [decodeErrorPushBoundedSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
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
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl (decodeErrorPushBoundedBudgetSpec M A lim)).pre
      (d, e, n, st) s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hpre_raw⟩
  refine h.mono_outcome (d, e, n, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, decodeErrorPushBoundedBudgetSpec,
      decodeErrorPushBoundedSpecWithStack, R'] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    refine ⟨hpost.1, ?_⟩
    have hp := hpost.2
    rw [sepExists_sepConj_left, satisfies_sepExists] at hp ⊢
    rcases hp with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨e, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨he_ne, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hp.1, ?_⟩
    rw [hsplit]
    have hm := hp.2
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

/-- Relocatable `<prost::error::DecodeError>::push` (Block `257`) satisfies
`withLsCodeLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))`. -/
theorem decode_error_push_bounded_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl
        (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))) :=
  decodeErrorPushBoundedWithStack_lscl_of_spec
    (decode_error_push_bounded_spec_placed_ok h_panic hshim halloc hrealloc)

private theorem ls_subroutine_ok_cro_ρ85 [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg calleeProg j H] {sym : String} {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    (hentry : entry = lsmpl.base j := by rfl)
    (hres : checkBlockSymAtU j sym = true := by decide)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (tryFromPlacedProg H) ((blkPl_85).ρ sym)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [ls_blockPlacement_ρ, ls_resolve_block_ultra hres, ← hentry]
  exact ls_subroutine_ok_cro_of_block (callerProg := tryFromPlacedProg H) (i := 85) (j := j)
    hcallee (by decide) hj hj_unmut

/-- Drop-in replacement for `CalleesPlacedBudget.tripleRatchetHooksWPlaced_of_codecHooks`
discharging `TripleRatchetHooksWPlaced` from `CodecHooksPlaced`. -/
theorem tripleRatchetHooksWPlaced_of_codecHooks_e4 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    TripleRatchetHooksWPlaced A lim H := by
  have hd := portDepsPlaced_of_hooks hH
  have hpush_b := decode_error_push_bounded_placed_ok
    hH.panic_raw hH.shim hH.alloc hH.realloc
  exact
    { alloc :=
        { dealloc := subroutine_ok_withLsCodeRoLoaded_of_plain'
            (rustDeallocExternWithStack_of_rustDealloc (by decide) (by decide)
              (ls_hook_ok_of_mem hH.dealloc))
          panic_alloc := hH.panic_alloc }
      decodeErrorFrom := ls_subroutine_ok_cro_ρ85 (j := 261)
        (subroutine_ok_withLsCodeRoLoaded_of_plain' hd.decodeErrorFrom)
      decodeErrorPush := ls_subroutine_ok_cro_ρ85 (j := 257)
        (subroutine_ok_withLsCodeRoLoaded_of_cl hpush_b)
      decodeVarintSlow := ls_subroutine_ok_cro_ρ85 (j := 293)
        (subroutine_ok_withLsCodeRoLoaded_of_cl hd.varintSlow) }

/-- Discharges Block `111` (`preKeyPlacedProg H`) bounded `<DecodeError>::push` from
`CodecHooksPlaced` (for `PksmCalleesPlaced.decodeErrorPush` + `BytesArmsPlacedBudget`). -/
theorem pksmDecodeErrorPushBounded_of_codecHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))) :=
  ls_subroutine_ok_pk_of_cl (callerProg := preKeyPlacedProg H) (i := 111) (j := 257)
    (fun _ h => h.1)
    (decode_error_push_bounded_placed_ok hH.panic_raw hH.shim hH.alloc hH.realloc)

/-- Definitional bridge between `DefsBudget.bytesMergeExactRawSpecX` (proved on Block `7` in
`RecordCodecs.AssemblyBudget`) and `TryFromDefsBudget.bytesMergeExactRawSpecX` (expected by
`TryFromDepsPlaced` and `PksmCalleesPlaced`). -/
theorem bytesMergeExactRawSpecX_defs_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget.bytesMergeExactRawSpecX A lim =
      LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget.bytesMergeExactRawSpecX A lim := by
  unfold
    LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget.bytesMergeExactRawSpecX
    LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget.bytesMergeExactRawSpecGen
    LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget.bmExactPostVecGen
    LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget.bmExactCapCond
    LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.DefsBudget.bmNextCap
    LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget.bytesMergeExactRawSpecX
    LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget.bmExactPostVec
    LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget.bmNextCap
    LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecX
    LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeRawSpecGen
  rfl

/-- Block `7` (`bytes::merge`) satisfies `TryFromDefsBudget.bytesMergeExactRawSpecX` under
`[LibsignalPlacement]`. -/
theorem bytes_merge_exact_placed_ok_x_e4 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H CryptoVerification.lsMemcpySym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec)) :
    subroutine_ok ((CryptoVerification.blkPC_7).rebase (CryptoVerification.blkPl_7).base H)
      (CryptoVerification.blkPl_7).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget.bytesMergeExactRawSpecX A lim)) := by
  rw [← bytesMergeExactRawSpecX_defs_eq A lim]
  exact LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget.bytes_merge_exact_placed_ok_x
    hshim halloc hrealloc hdealloc hmc

/-! ## 2. Ghost Capacity Match Invariant for `ProtoPreKeySignalMessage` -/

/-- Maps the 4 `Option<Vec<u8>>` fields of `ProtoPreKeySignalMessage` onto `SigTryFromCaps`:
`kyberCiphertext ↔ .rk`, `baseKey ↔ .ct`, `identityKey ↔ .pq`, `message ↔ .ad`.
Defined as a conjunction (rather than a `structure`) so `WirePreKeyCapsMatch g { m with <u32> := o } caps`
is definitionally equal (`rfl`) to `WirePreKeyCapsMatch g m caps`. -/
def WirePreKeyCapsMatch (g : WirePreKeyGhost) (m : ProtoPreKeySignalMessage)
    (caps : SigTryFromCaps) : Prop :=
  optFieldCapMatch m.kyberCiphertext g.kyberCt caps.rk ∧
    optFieldCapMatch m.baseKey g.baseKey caps.ct ∧
    optFieldCapMatch m.identityKey g.identityKey caps.pq ∧
    optFieldCapMatch m.message g.message caps.ad

/-- Capacity-tracked stack `proto::wire::PreKeySignalMessage` invariant. Needs no slice-length
parameter `n` because PKSM decode arms always carry `bs.length < 2 ^ 32`, giving
`bytesMergeCapOk_of_len_lt32` unconditionally. -/
def wirePreKeyLoopCapsOf (A : RustAlloc) (a : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  ∃∗ g : WirePreKeyGhost, ⌜WirePreKeyCapsMatch g m caps⌝ ∗ wirePreKeyAt A g a m

theorem optFieldCapMatch_pksm_init {u : Option (List (BitVec 8))} {pin : VecPin} {c : Nat}
    {cap0 : BitVec 64} {bsLen : Nat}
    (hc : optFieldCapMatch u pin c) (hlen : bsLen < 2 ^ 32)
    (hcap0 : match u with | none => cap0 = 0#64 | some _ => cap0 = pin.cap) :
    BytesMergeCapOk cap0 bsLen ∧ cap0 = BitVec.ofNat 64 c ∧ cap0.toNat = c ∧ c < 2 ^ 63 := by
  cases u <;> exact optFieldCapMatch_init hc (bytesMergeCapOk_of_len_lt32 hlen) hcap0

theorem wirePreKeyAt_entails_loopCapsOf (A : RustAlloc) (g : WirePreKeyGhost)
    (a : BitVec 64) (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage)
    (hc : WirePreKeyCapsMatch g m caps) :
    wirePreKeyAt A g a m ⊢ wirePreKeyLoopCapsOf A a caps m := by
  unfold wirePreKeyLoopCapsOf
  refine Entails.trans ?_ (sepExists_intro _ g)
  rw [pure_true_emp hc, emp_sepConj]
  exact Entails.refl _

theorem wirePreKeyLoopCapsOf_entails_of (A : RustAlloc) (a : BitVec 64)
    (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage) :
    wirePreKeyLoopCapsOf A a caps m ⊢ wirePreKeyOf A a m := by
  unfold wirePreKeyLoopCapsOf wirePreKeyOf
  exact Entails.sepExists_elim fun g =>
    Entails.pure_left fun _ => sepExists_intro (fun g' => wirePreKeyAt A g' a m) g

theorem wirePreKeyOf_empty_entails_loopCapsOf (A : RustAlloc) (a : BitVec 64) :
    wirePreKeyOf A a emptyProto ⊢
      wirePreKeyLoopCapsOf A a SigTryFromCaps.zero emptyProto := by
  refine Entails.sepExists_elim fun g => ?_
  have hc0 : WirePreKeyCapsMatch ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩
      emptyProto SigTryFromCaps.zero :=
    ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩
  have heq : wirePreKeyAt A g a emptyProto =
      wirePreKeyAt A ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩ a
        emptyProto := rfl
  rw [heq]
  exact wirePreKeyAt_entails_loopCapsOf A _ a SigTryFromCaps.zero emptyProto hc0

private theorem optVecU8At_mk_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (pool : SepProp) (pin : VecPin) (a : BitVec 64) (u : Option (List (BitVec 8))) :
    optVecU8At { pool := pool, live := A.live } pin a u = optVecU8At A.repAlloc pin a u := by
  cases u <;> rfl

theorem wirePreKeyOf_mk_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (pool : SepProp) (a : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf { pool := pool, live := A.live } a m = wirePreKeyOf A.repAlloc a m := by
  simp only [wirePreKeyOf, wirePreKeyAt, optVecU8At_mk_eq]

theorem wirePreKeyLoopCapsOf_mk_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (pool : SepProp) (a : BitVec 64) (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage) :
    wirePreKeyLoopCapsOf { pool := pool, live := A.live } a caps m =
      wirePreKeyLoopCapsOf A.repAlloc a caps m := by
  simp only [wirePreKeyLoopCapsOf, wirePreKeyAt, optVecU8At_mk_eq]

theorem decodeErrorAtStackLen_mk_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (pool : SepProp) (e : BitVec 64) (n : Nat) :
    decodeErrorAtStackLen { pool := pool, live := A.live } e n =
      decodeErrorAtStackLen A.repAlloc e n :=
  rfl

theorem vecU8At_kyberCt_entails_wirePreKeyLoopCapsOf (A : RustAlloc)
    (g : WirePreKeyGhost) (sp' cap' ptr' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) (v : List (BitVec 8))
    (hc : WirePreKeyCapsMatch g m caps)
    (hcap_eq : cap'.toNat = bmNextCap caps.rk v.length)
    (hnext_lt : bmNextCap caps.rk v.length < 2 ^ 63) :
    vecU8At A (sp' + 312#64) cap' ptr' v ∗
      (optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyLoopCapsOf A (sp' + 312#64)
        (caps.set .rk (bmNextCap caps.rk v.length)) { m with kyberCiphertext := some v } := by
  refine Entails.trans ?_
    (wirePreKeyAt_entails_loopCapsOf A { g with kyberCt := ⟨cap', ptr'⟩ } (sp' + 312#64)
      (caps.set .rk (bmNextCap caps.rk v.length)) { m with kyberCiphertext := some v }
      ⟨⟨hnext_lt, hcap_eq⟩, hc.2.1, hc.2.2.1, hc.2.2.2⟩)
  rw [wirePreKeyAt_split_kyberCt A { g with kyberCt := ⟨cap', ptr'⟩ } sp'
    { m with kyberCiphertext := some v }]
  exact Entails.refl _

theorem vecU8At_baseKey_entails_wirePreKeyLoopCapsOf (A : RustAlloc)
    (g : WirePreKeyGhost) (sp' cap' ptr' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) (v : List (BitVec 8))
    (hc : WirePreKeyCapsMatch g m caps)
    (hcap_eq : cap'.toNat = bmNextCap caps.ct v.length)
    (hnext_lt : bmNextCap caps.ct v.length < 2 ^ 63) :
    vecU8At A (sp' + 336#64) cap' ptr' v ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyLoopCapsOf A (sp' + 312#64)
        (caps.set .ct (bmNextCap caps.ct v.length)) { m with baseKey := some v } := by
  refine Entails.trans ?_
    (wirePreKeyAt_entails_loopCapsOf A { g with baseKey := ⟨cap', ptr'⟩ } (sp' + 312#64)
      (caps.set .ct (bmNextCap caps.ct v.length)) { m with baseKey := some v }
      ⟨hc.1, ⟨hnext_lt, hcap_eq⟩, hc.2.2.1, hc.2.2.2⟩)
  rw [wirePreKeyAt_split_baseKey A { g with baseKey := ⟨cap', ptr'⟩ } sp'
    { m with baseKey := some v }]
  exact Entails.refl _

theorem vecU8At_identityKey_entails_wirePreKeyLoopCapsOf (A : RustAlloc)
    (g : WirePreKeyGhost) (sp' cap' ptr' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) (v : List (BitVec 8))
    (hc : WirePreKeyCapsMatch g m caps)
    (hcap_eq : cap'.toNat = bmNextCap caps.pq v.length)
    (hnext_lt : bmNextCap caps.pq v.length < 2 ^ 63) :
    vecU8At A (sp' + 360#64) cap' ptr' v ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyLoopCapsOf A (sp' + 312#64)
        (caps.set .pq (bmNextCap caps.pq v.length)) { m with identityKey := some v } := by
  refine Entails.trans ?_
    (wirePreKeyAt_entails_loopCapsOf A { g with identityKey := ⟨cap', ptr'⟩ } (sp' + 312#64)
      (caps.set .pq (bmNextCap caps.pq v.length)) { m with identityKey := some v }
      ⟨hc.1, hc.2.1, ⟨hnext_lt, hcap_eq⟩, hc.2.2.2⟩)
  rw [wirePreKeyAt_split_identityKey A { g with identityKey := ⟨cap', ptr'⟩ } sp'
    { m with identityKey := some v }]
  exact Entails.refl _

theorem vecU8At_message_entails_wirePreKeyLoopCapsOf (A : RustAlloc)
    (g : WirePreKeyGhost) (sp' cap' ptr' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) (v : List (BitVec 8))
    (hc : WirePreKeyCapsMatch g m caps)
    (hcap_eq : cap'.toNat = bmNextCap caps.ad v.length)
    (hnext_lt : bmNextCap caps.ad v.length < 2 ^ 63) :
    vecU8At A (sp' + 384#64) cap' ptr' v ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyLoopCapsOf A (sp' + 312#64)
        (caps.set .ad (bmNextCap caps.ad v.length)) { m with message := some v } := by
  refine Entails.trans ?_
    (wirePreKeyAt_entails_loopCapsOf A { g with message := ⟨cap', ptr'⟩ } (sp' + 312#64)
      (caps.set .ad (bmNextCap caps.ad v.length)) { m with message := some v }
      ⟨hc.1, hc.2.1, hc.2.2.1, ⟨hnext_lt, hcap_eq⟩⟩)
  rw [wirePreKeyAt_split_message A { g with message := ⟨cap', ptr'⟩ } sp'
    { m with message := some v }]
  exact Entails.refl _

/-! ### `u32` Field-Splitting & Update Equalities -/

def wirePreKeyVecsCapsOf (A : RustAlloc) (a : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  ∃∗ g : WirePreKeyGhost, ⌜WirePreKeyCapsMatch g m caps⌝ ∗
    optVecU8At A g.kyberCt a m.kyberCiphertext ∗
    optVecU8At A g.baseKey (a + 0x18#64) m.baseKey ∗
    optVecU8At A g.identityKey (a + 0x30#64) m.identityKey ∗
    optVecU8At A g.message (a + 0x48#64) m.message

theorem wirePreKeyLoopCapsOf_eq_vecs_u32s (A : RustAlloc) (a : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) :
    wirePreKeyLoopCapsOf A a caps m =
      wirePreKeyVecsCapsOf A a caps m ∗ optU32At (a + 0x60#64) m.registrationId ∗
      optU32At (a + 0x68#64) m.preKeyId ∗ optU32At (a + 0x70#64) m.signedPreKeyId ∗
      optU32At (a + 0x78#64) m.kyberPreKeyId := by
  unfold wirePreKeyLoopCapsOf wirePreKeyAt wirePreKeyVecsCapsOf
  simp only [sepExists_sepConj_left, sepConj_assoc]

def wirePreKeyRestCaps1 (A : RustAlloc) (sp' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsCapsOf A (sp' + 312#64) caps m ∗ optU32At (sp' + 408#64) m.registrationId ∗
    optU32At (sp' + 424#64) m.signedPreKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyLoopCapsOf_eq_preKeyId (A : RustAlloc) (sp' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) :
    wirePreKeyLoopCapsOf A (sp' + 312#64) caps m =
      optU32At (sp' + 416#64) m.preKeyId ∗ wirePreKeyRestCaps1 A sp' caps m := by
  rw [wirePreKeyLoopCapsOf_eq_vecs_u32s]; unfold wirePreKeyRestCaps1
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyLoopCapsOf_update_preKeyId (A : RustAlloc) (sp' : BitVec 64)
    (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage) (o : Option (BitVec 32)) :
    optU32At (sp' + 416#64) o ∗ wirePreKeyRestCaps1 A sp' caps m =
      wirePreKeyLoopCapsOf A (sp' + 312#64) caps { m with preKeyId := o } := by
  rw [wirePreKeyLoopCapsOf_eq_preKeyId A sp' caps { m with preKeyId := o }]; rfl

def wirePreKeyRestCaps5 (A : RustAlloc) (sp' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsCapsOf A (sp' + 312#64) caps m ∗ optU32At (sp' + 416#64) m.preKeyId ∗
    optU32At (sp' + 424#64) m.signedPreKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyLoopCapsOf_eq_regId (A : RustAlloc) (sp' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) :
    wirePreKeyLoopCapsOf A (sp' + 312#64) caps m =
      optU32At (sp' + 408#64) m.registrationId ∗ wirePreKeyRestCaps5 A sp' caps m := by
  rw [wirePreKeyLoopCapsOf_eq_vecs_u32s]; unfold wirePreKeyRestCaps5
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyLoopCapsOf_update_regId (A : RustAlloc) (sp' : BitVec 64)
    (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage) (o : Option (BitVec 32)) :
    optU32At (sp' + 408#64) o ∗ wirePreKeyRestCaps5 A sp' caps m =
      wirePreKeyLoopCapsOf A (sp' + 312#64) caps { m with registrationId := o } := by
  rw [wirePreKeyLoopCapsOf_eq_regId A sp' caps { m with registrationId := o }]; rfl

def wirePreKeyRestCaps6 (A : RustAlloc) (sp' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsCapsOf A (sp' + 312#64) caps m ∗ optU32At (sp' + 408#64) m.registrationId ∗
    optU32At (sp' + 416#64) m.preKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyLoopCapsOf_eq_signedPreKeyId (A : RustAlloc) (sp' : BitVec 64)
    (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage) :
    wirePreKeyLoopCapsOf A (sp' + 312#64) caps m =
      optU32At (sp' + 424#64) m.signedPreKeyId ∗ wirePreKeyRestCaps6 A sp' caps m := by
  rw [wirePreKeyLoopCapsOf_eq_vecs_u32s]; unfold wirePreKeyRestCaps6
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyLoopCapsOf_update_signedPreKeyId (A : RustAlloc) (sp' : BitVec 64)
    (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage) (o : Option (BitVec 32)) :
    optU32At (sp' + 424#64) o ∗ wirePreKeyRestCaps6 A sp' caps m =
      wirePreKeyLoopCapsOf A (sp' + 312#64) caps { m with signedPreKeyId := o } := by
  rw [wirePreKeyLoopCapsOf_eq_signedPreKeyId A sp' caps { m with signedPreKeyId := o }]; rfl

def wirePreKeyRestCaps7 (A : RustAlloc) (sp' : BitVec 64) (caps : SigTryFromCaps)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsCapsOf A (sp' + 312#64) caps m ∗ optU32At (sp' + 408#64) m.registrationId ∗
    optU32At (sp' + 416#64) m.preKeyId ∗ optU32At (sp' + 424#64) m.signedPreKeyId

theorem wirePreKeyLoopCapsOf_eq_kyberPreKeyId (A : RustAlloc) (sp' : BitVec 64)
    (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage) :
    wirePreKeyLoopCapsOf A (sp' + 312#64) caps m =
      optU32At (sp' + 432#64) m.kyberPreKeyId ∗ wirePreKeyRestCaps7 A sp' caps m := by
  rw [wirePreKeyLoopCapsOf_eq_vecs_u32s]; unfold wirePreKeyRestCaps7
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyLoopCapsOf_update_kyberPreKeyId (A : RustAlloc) (sp' : BitVec 64)
    (caps : SigTryFromCaps) (m : ProtoPreKeySignalMessage) (o : Option (BitVec 32)) :
    optU32At (sp' + 432#64) o ∗ wirePreKeyRestCaps7 A sp' caps m =
      wirePreKeyLoopCapsOf A (sp' + 312#64) caps { m with kyberPreKeyId := o } := by
  rw [wirePreKeyLoopCapsOf_eq_kyberPreKeyId A sp' caps { m with kyberPreKeyId := o }]; rfl

/-! ## 3. Segment Pool Sync, `preKeyLoopExitPostPlaced`, & Shared `DecodeError::push` Tail -/

theorem sepWP_seg_111 [LibsignalPlacement] {H : LibsignalHooks}
    {target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      ProofLib.SepWP ((blkPC_111).rebase (blkPl_111).base (hooksException H))
        target (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            ProofLib.SepWP (preKeyPlacedProg H) target (sm'.setMem m_real) Pm post oom)) :
    ProofLib.SepWP (preKeyPlacedProg H) target s Pre post oom :=
  sepWP_seg_ls_vm (i := 111) blkLib_eq_111 rfl hseg

theorem sepWP_done_sync_pool_111 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {H : LibsignalHooks}
    {target : BitVec 64} {s0 s sm' : State} {Pm F : SepProp}
    {post : State → SepProp → Prop}
    [hv : VRegsAt s sm']
    (hpost : ∀ m_real : Memory,
      LibsignalCodeRoLoaded lsmpl (sm'.setMem m_real).mem →
      post (sm'.setMem m_real) (A.pool lim st (sm'.setMem m_real) ∗ F))
    (hpc : sm'.pc = target := by simp only [wp_norm, arm64_norm])
    (hrun : sm'.status = .Running := by simp only [wp_norm, arm64_norm]; assumption)
    (htp : sm'.tpidrEl0 = s0.tpidrEl0 := by simp only [wp_norm, arm64_norm])
    (hPm : Pm = A.pool lim st s0 ∗ F := by sep_focus) :
    ProofLib.SepWP ((blkPC_111).rebase (blkPl_111).base (hooksException H)) target sm' Pm
      (fun sm'' Pm'' =>
        ∀ m_real : Memory, ProofLib.NonSyscallPreserved s0 (sm''.setMem m_real) →
          ProofLib.SepWP (preKeyPlacedProg H) target (sm''.setMem m_real) Pm''
            (fun sf Pf => VRegsAt s sf ∧ (LibsignalCodeRoLoaded lsmpl sf.mem → post sf Pf))) := by
  refine ProofLib.SepWP.done hpc hrun fun m_real hnsp => ?_
  have hvm := hnsp.toVmPreserved (by cases sm'; exact htp)
  rw [hPm, ← A.pool_transport lim st s0 (sm'.setMem m_real) hvm]
  have hv_real : VRegsAt s (sm'.setMem m_real) := ⟨by cases sm'; exact hv.eq⟩
  exact ProofLib.SepWP.done (by cases sm'; exact hpc) (by cases sm'; exact hrun)
    ⟨hv_real, hpost m_real⟩

/-- Exit postcondition at `+0x460` (`1120`) indexed by `(rem : Nat) (caps : SigTryFromCaps)`. -/
def preKeyLoopExitPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (rem : Nat) (caps : SigTryFromCaps)
    (s0 : State) (sp' sret len ptr0 : BitVec 64) (vb : BitVec 8) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (res : Option ProtoPreKeySignalMessage) :
    State → SepProp → Prop :=
  fun sf Pm =>
    PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb sf ∧
    ∃ evs : List AllocEvent, SigTryFromLoopBoundedEnv rem caps evs ∧
      (Pm ⊢ preKeyLoopExitMem (A.atState lim (M.stepEvents evs st) sf)
        sp' ptr bs (sf.readReg64 .x24) res)

/-- At `caps = SigTryFromCaps.zero`, `SigTryFromLoopBoundedEnv rem SigTryFromCaps.zero` is
definitionally `TryFromLoopEnv fuel rem`. -/
theorem preKeyLoopExitPostPlaced_zero_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (fuel rem : Nat)
    (s0 : State) (sp' sret len ptr0 : BitVec 64) (vb : BitVec 8) (ptr : BitVec 64)
    (bs : List (BitVec 8)) (res : Option ProtoPreKeySignalMessage) :
    preKeyLoopExitPostPlaced A lim st rem SigTryFromCaps.zero s0 sp' sret len ptr0 vb ptr bs res =
      fun sf Pm =>
        PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb sf ∧
        ∃ evs : List AllocEvent, TryFromLoopEnv fuel rem evs ∧
          (Pm ⊢ preKeyLoopExitMem (A.atState lim (M.stepEvents evs st) sf)
            sp' ptr bs (sf.readReg64 .x24) res) :=
  rfl

theorem preKeyLoopExitPostPlaced_mono_rem [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem₁ rem₂ : Nat}
    {caps : SigTryFromCaps} (hle : rem₁ ≤ rem₂) {s0 sf : State}
    {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {res : Option ProtoPreKeySignalMessage} {Pm : SepProp}
    (h : preKeyLoopExitPostPlaced A lim st rem₁ caps s0 sp' sret len ptr0 vb ptr bs res sf Pm) :
    preKeyLoopExitPostPlaced A lim st rem₂ caps s0 sp' sret len ptr0 vb ptr bs res sf Pm := by
  rcases h with ⟨hst, evs, hevs, hent⟩
  exact ⟨hst, evs, hevs.mono_rem hle, hent⟩

theorem preKeyLoopExitPostPlaced_skipStep [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {rem rem' : Nat}
    {caps : SigTryFromCaps} (hlt : rem' < rem) {s0 sf : State}
    {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {res : Option ProtoPreKeySignalMessage} {Pm : SepProp}
    (h : preKeyLoopExitPostPlaced A lim st rem' caps s0 sp' sret len ptr0 vb ptr bs res sf Pm) :
    preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res sf Pm := by
  rcases h with ⟨hst, evs, hevs, hent⟩
  exact ⟨hst, evs, .skipStep hlt hevs, hent⟩

theorem preKeyLoopExitPostPlaced_bytesStep [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (f : SigTryFromField) {rem rem' : Nat} {caps : SigTryFromCaps}
    {wt : WireType} {bs_m v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bs_m = some (v, rest))
    (hbs_le : bs_m.length ≤ rem)
    (hprog : rem' + v.length + 1 ≤ rem)
    (hcap_lt : caps.get f < 2 ^ 63)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs_m)
    {s0 sf : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {res : Option ProtoPreKeySignalMessage} {Pm : SepProp}
    (h : preKeyLoopExitPostPlaced A lim (M.stepEvents evs₁ st) rem'
      (caps.set f (bmNextCap (caps.get f) v.length))
      s0 sp' sret len ptr0 vb ptr bs res sf Pm) :
    preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res sf Pm := by
  subst hevs₁
  rcases h with ⟨hst, evs₂, hevs₂, hent⟩
  refine ⟨hst, _ ++ evs₂, .bytesStep f wt bs_m v rest hm hbs_le hprog hcap_lt hevs₂, ?_⟩
  rwa [M.stepEvents_append]

theorem preKeyLoopExitPostPlaced_append_prefix [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {s0 sf : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {k : Nat} (hk : k ≤ bs.length)
    {res : Option ProtoPreKeySignalMessage} {Pm : SepProp}
    (h : preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb
      (ptr + BitVec.ofNat 64 k) (bs.drop k) res sf Pm) :
    preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res sf
      (Pm ∗ (ptr ↦ₛ bs.take k)) := by
  rcases h with ⟨hst, evs, hevs, hent⟩
  refine ⟨hst, evs, hevs, ?_⟩
  rw [← preKeyLoopExitMem_append_prefix (A.atState lim (M.stepEvents evs st) sf)
    sp' ptr bs k hk (sf.readReg64 .x24) res]
  exact sepConj_mono_left hent

theorem advance_cursorPK_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps}
    {H : LibsignalHooks} {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr : BitVec 64} {bs rest : List (BitVec 8)} {res : Option ProtoPreKeySignalMessage}
    {R : SepProp} (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest res) (noPanicQp s0)) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ R)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt (sp' + 296#64) ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact sepWPp_frame_noPanic h (fun _ _ hqm => preKeyLoopExitPostPlaced_append_prefix hkl hqm)

theorem preKeyLoopExitMem_err_loopCaps_intro (A : RustAlloc) (sp' ptr : BitVec 64)
    (bs : List (BitVec 8)) (x24 : BitVec 64) (hx24 : x24 ≠ 0#64) (n : Nat)
    (caps : SigTryFromCaps) (mErr : ProtoPreKeySignalMessage) :
    memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ memRegion (sp' + 448#64) 64 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
      decodeErrorAtStackLen A x24 n ∗ wirePreKeyLoopCapsOf A (sp' + 312#64) caps mErr ⊢
      preKeyLoopExitMem A sp' ptr bs x24 none := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right
        (wirePreKeyLoopCapsOf_entails_of A (sp' + 312#64) caps mErr))))))))
    (preKeyLoopExitMem_err_intro A sp' ptr bs x24 hx24 n mErr)

set_option maxHeartbeats 800000 in
/-- Shared `<DecodeError>::push` tail at `+0x458..+0x45c → +0x460` (`n = 0` after `bytes::merge`
or `int32::merge` fails with `evs = rustAllocEvents 72 8`), closing `preKeyLoopExitPostPlaced`
via `fitsEnv_sigLoop_pushAfterFrom` + `SigTryFromErrTailEnv.fromPush`. -/
theorem decodeErrorPushPK_tail_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps} {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr err : BitVec 64} {bs : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_111).base + 0x458#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = sp' + 448#64)
    (herr : err ≠ 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ err) ∗ memRegion (sp' + 456#64) 56 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s ∗
        stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        wirePreKeyOf A.repAlloc (sp' + 312#64) mErr)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs none)
      (noPanicQp s0) := by
  change s.pc = (blkPl_111).base + 1112#64 at hpc
  let st_from := M.stepEvents (rustAllocEvents 72 8) st
  have hfit_push : FitsEnv M lim st_from (DecodeErrorPushBoundedEnv 0) :=
    fitsEnv_sigLoop_pushAfterFrom hfit
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 257) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st_from fun _ hcl1 => ?_
  refine sepWPp_call_noPanic_placed A lim st_from (sp' + 448#64, err, 0, st_from) hPush
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 1116#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 448#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
      stackAt sp' (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ 0 < 2 ^ 32 ∧ FitsEnv M lim st_from (DecodeErrorPushBoundedEnv 0))
    (by
      have hx0' : s.readReg64 (Reg.gpr 0#5) = sp' + 448#64 := hx0
      simp only [decodeErrorPushBoundedSpecWithStack, hsp_eq, hx0', arm64_norm, true_and]
      sep_ac_rfl)
    ⟨herr, by decide, hfit_push⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  dsimp only [decodeErrorPushBoundedSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun evs_p => ?_
  refine SepWPp.exists_pre fun err' => ?_
  refine SepWPp.pure_pre fun herr' => ?_
  refine SepWPp.pure_pre fun hevs_p => ?_
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  refine sepWPp_end_noPanic_placed hcl2 ?_
  apply sepWP_seg_111; intro _m_strip2
  wp_steps
  refine sepWP_done_sync_pool_111 A lim (M.stepEvents evs_p st_from) fun _ hcl3 => ?_
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
    by simpa [arm64_norm] using hregs2.x27, by simpa [arm64_norm] using hregs2.x25,
    by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20,
    by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcl3, by simpa [arm64_norm] using htr2.trans htr⟩,
    rustAllocEvents 72 8 ++ evs_p, .done (.fromPush hevs_p), ?_⟩
  simp only [st_from, ← M.stepEvents_append, arm64_norm]
  refine Entails.trans
    (Q := ((sp' + 448#64) ↦₆₄ err') ∗
      (A.pool lim (M.stepEvents (rustAllocEvents 72 8 ++ evs_p) st) _ ∗
        decodeErrorAtStackLen A.repAlloc err' 1 ∗
        stackAt s.sp (2 * extHookStack) ∗
        memRegion (sp' + 296#64) 16 ∗
        (ptr ↦ₛ bs) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 456#64) 56 ∗
        memRegion (sp' - BitVec.ofNat 64 (skipFieldStackX 100))
          (skipFieldStackX 100 - 2 * extHookStack) ∗
        wirePreKeyOf A.repAlloc (sp' + 312#64) mErr))
    (by simp only [arm64_norm]; apply entails_of_eq; sep_ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 448#64) err')) ?_
  refine Entails.trans ?_
    (preKeyLoopExitMem_err_intro (A.atState lim (M.stepEvents (rustAllocEvents 72 8 ++ evs_p) st) _)
      sp' ptr bs err' herr' 1 mErr)
  simp only [RustCliAllocBudget.atState, wirePreKeyOf_mk_eq, decodeErrorAtStackLen_mk_eq]
  apply entails_of_eq
  simp only [hstack, hsp_eq, memRegion64_split8_448 sp', arm64_norm]
  sep_ac_rfl

/-- Convenience wrapper accepting `wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps' mErr`. -/
theorem decodeErrorPushPK_tail_placed_wpX_caps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps caps' : SigTryFromCaps} {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr err : BitVec 64} {bs : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hpc : s.pc = (blkPl_111).base + 0x458#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = sp' + 448#64)
    (herr : err ≠ 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ err) ∗ memRegion (sp' + 456#64) 56 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s ∗
        stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps' mErr)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs none)
      (noPanicQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (wirePreKeyLoopCapsOf_entails_of A.repAlloc (sp' + 312#64) caps' mErr)))))))))
    (decodeErrorPushPK_tail_placed_wpX hPush hfit hpc hrun hregs hsp hcl htr hx0 herr)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
