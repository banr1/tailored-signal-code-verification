/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection1
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection1StepsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionAuxBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `EpochDirection::encode [local#1]` (`Block 154`)

Re-exports Steps 1–3 from `EpochDirection1StepsBudget`, proves Step 4 (`prev: Vec<u8>`) on
`lsProg_154 H`, and establishes the top-level `[LibsignalPlacement]` budget contracts for
`EpochDirection::encode [local#1]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection1Budget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_154 blkPl_148 blkPl_154 blkPl_154_ρ blkPl_157
   lsMemcpySym lsProg_148 lsProg_154 lsProg_157 lsmpl lsρ
   ls_resolve_blk_148 ls_resolve_blk_157 ls_subroutine_ok_of_block withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (WireType encodeKey)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack doReserveStackX reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost StepInv vecU8At_eq_header_sep_buf)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Varint
  (elem_len_after_reserve_not_ult elem_len_ult_spare_iff
   vecU8At_expose_slice vecU8At_pack_slice)
open CryptoVerification.SpqrV1.ProtoRepr
  (epochDirectionPBEncodedLen epochDirectionPBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero ofNat_countLeadingZeros_32
   ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt ule_self_64 ule_zero_64
   ult_self_64 ult_zero_64 zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Auth
  (authEncodeStackOf sp_sub_64_aligned vecU8At_bounds_of_satisfies)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget (sepWPp_extract_vecU8At_bounds)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (AuthEncodeCalleeSavedPlaced EncodeEpochDirectionPinnedGhost
   bs0_append_encodeEpochDirectionMsg bs0_append_epochDirectionHeaderBytes
   bs_append_epochDirectionCtrBytes_of_ne_zero bs_append_epochDirectionCtrBytes_of_zero
   bs_append_epochDirectionNextBytes_of_empty bs_append_epochDirectionNextBytes_of_ne_empty
   bs_append_epochDirectionPrevBytes_of_empty bs_append_epochDirectionPrevBytes_of_ne_empty
   cap_toNat_eq_of_beq encodeEpochDirectionMsg encodeEpochDirectionMsg_len_split
   encodeVarint_epochDirection_tag_eq_proto epochDirectionCtrBytes
   epochDirectionCtrBytes_len_of_ne_zero epochDirectionElemsAt epochDirectionHeaderBytes
   epochDirectionHeaderBytes_len_bounds epochDirectionNextBytes
   epochDirectionNextBytes_len_of_ne_empty epochDirectionPBEncodedLen_eq_fields_len
   epochDirectionPBPinnedAt_bounds_of_satisfies epochDirectionPBPinnedAt_eq_elems
   epochDirectionPrevBytes epochDirectionPrevBytes_len_of_ne_empty epochDirectionRestAt
   epochDirectionSavedFrame lt_cap_toNat_of_beq_false reserveCap_one_bounds
   subroutine_ok_withAuthEncodeCSPlaced_placed_blk
   withAuthEncodeCSPlaced zext64_orr_1_32 zext64_trunc32_orr_1 zext64_trunc32_orr_100000001)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2BaseBudget
  (do_reserve2_placed_ok do_reserve2_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeVarintDetSpecOf pushBytesStep)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1Budget
  (encode_varint2_det_placed_ok encode_varint2_det_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8EncodeEnv VecU8ReserveChain)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (EncodeEpochDirectionPinnedEnv encodeEpochDirectionPinnedSpec
   encodeEpochDirectionPinnedSpecOf encodeEpochDirectionPinnedSpecX
   encodeEpochDirectionSpec encodeEpochDirectionSpecX)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
  (EncodeEpochDirection154PinnedPlacedOk EncodeEpochDirection154PinnedPlacedOkExt
   EncodeEpochDirection154PinnedPlacedOkExtX EncodeEpochDirection154PinnedPlacedOkX
   EncodeEpochDirection154PlacedOk EncodeEpochDirection154PlacedOkExt
   EncodeEpochDirection154PlacedOkExtX EncodeEpochDirection154PlacedOkX
   epochDirection_unpinned_of_pinned_placed_x isEpochDirectionEncodePlacedProg_154
   step_ed_do_reserve2_call_placed step_ed_encode_varint_det_call_placed
   step_ed_memcpy_call_placed step_epochDir_epilogue_placed step_epochDir_len_placed
   step_epochDir_prologue_placed step_epochDir_push_ctr_tag_placed
   step_epochDir_push_next_tag_placed step_epochDir_push_prev_tag_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionAuxBudget
  (doReserve2_noAllocEnforced_ok encodeEpochDirectionPinnedCoreSpecOf
   encodeVarint2_det_noAllocEnforced_placed_ok fitsEvents_and_step_of_chain
   fitsEvents_encodeVarint_of_env noAllocEnforcedLimits sepWP_done_tpidr_placed
   sepWPp_of_sepWP_cs_placed_vm subroutine_ok_encodeEpochDirectionPinned_of_core
   vecU8ReserveChain_doReserve vecU8ReserveChain_encodeVarint withVmAnchor)

open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection1StepsBudget
  (step_ctr_1_placed step_hdr_1_placed step_next_1_placed)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_pc_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_omega
private theorem bv_bl_target (a b k : BitVec 64) : a + k + (b - a - k) = b := by bv_omega
private theorem lsmpl_base_148 [LibsignalPlacement] : lsmpl.base 148 = (blkPl_148).base := rfl
private theorem lsmpl_base_157 [LibsignalPlacement] : lsmpl.base 157 = (blkPl_157).base := rfl
private theorem blkPl_154_memcpy [LibsignalPlacement] :
    (blkPl_154).ρ "memcpy" = lsρ lsMemcpySym := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit bv_pc_add_sub_cancel bv_bl_target BitVec.toNat_zero
  blkPl_154_ρ ls_resolve_blk_148 ls_resolve_blk_157 lsmpl_base_148 lsmpl_base_157 blkPl_154_memcpy
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero ule_zero_64 ult_zero_64
  ule_self_64 ult_self_64 zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

/-! ## 1. Step 4 (`prev`) & Top-Level Block `154` Contracts -/

private theorem step_prev_from_404_1_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_154 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8))
    (d : EpochDirectionPB) (curSt : M.σ)
    (hprev_ne : d.prev.isEmpty = false) (hle : bs2.length + d.prev.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_154).base + 404#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = prevPtr) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs2.length)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool lim curSt s) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_154).base + 432#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_154 H) ret sm
        ((vecU8At A.repAlloc v curCap curPtr (bs2 ++ d.prev) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool lim curSt sm) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_154 H) ret s P Q Qp oom := by
  subst hP
  have hprev_ne_nil : d.prev ≠ [] := List.isEmpty_eq_false_iff.mp hprev_ne
  have hprev_pos : 0 < d.prev.length := List.length_pos_of_ne_nil hprev_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := curCap) (ptr := curPtr)
    (bs := bs2) (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool lim curSt s ∗ F)
    (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A.repAlloc v curCap curPtr bs2 d.prev.length hle hcap_lt hptr_ne
    hprev_pos, epochDirectionElemsAt]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := lsρ lsMemcpySym)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1 hinv1
    rw [← A.pool_of_vmPreserved hvmp1]
    refine step_ed_memcpy_call_placed hmemcpy (curPtr + BitVec.ofNat 64 bs2.length) prevPtr sp
      ((blkPl_154).base + 424#64) d.prev
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
        memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 d.prev.length)
          (curCap.toNat - bs2.length - d.prev.length) ∗
        ((dirA + 8#64) ↦₆₄ nextPtr) ∗ ((dirA + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        (nextPtr ↦ₛ d.next) ∗ ((dirA + 32#64) ↦₆₄ prevPtr) ∗
        ((dirA + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗ ((dirA + 48#64) ↦₃₂ d.ctr) ∗
        A.pool lim curSt _ ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
      (by sep_ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hvmpm
    rw [← A.pool_of_vmPreserved hvmpm]
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by
      rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs2.length := by
      rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_154).base + 432#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp2 hinv2
      refine SepWPp.weaken_pre ?_
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2))
      rw [← A.pool_of_vmPreserved hvmp2,
        ← vecU8At_pack_slice A.repAlloc v curCap curPtr bs2 d.prev hle hcap_lt hptr_ne hprev_ne_nil,
        epochDirectionElemsAt]
      exact Entails.of_eq (by sep_ac_rfl)))

private theorem step_prev_from_352_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_154 H) (blkPl_148).base
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_154 H) (blkPl_157).base
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_154 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs1 : List (BitVec 8))
    (d : EpochDirectionPB) (curSt : M.σ) (finalLen : Nat)
    (hprev_ne : d.prev.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62)
    (hle_fin : bs1.length + (epochDirectionPrevBytes d).length ≤ finalLen)
    (hEnv : FitsEnv M lim curSt (VecU8EncodeEnv curCap.toNat finalLen))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_154).base + 352#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = prevPtr)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_154).base + 432#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap3.toNat →
      (bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat →
        cap3 = curCap ∧ ptr3 = curPtr) →
      VecU8ReserveChain curCap.toNat cap3.toNat finalLen evs →
      FitsEnv M lim (M.stepEvents evs curSt) (VecU8EncodeEnv cap3.toNat finalLen) →
      SepWPp (lsProg_154 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3 (bs1 ++ epochDirectionPrevBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗
          A.pool lim (M.stepEvents evs curSt) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_154 H) ret s P Q Qp oom := by
  have hstep404 := step_prev_from_404_1_placed A lim H hmemcpy
  have hfn_ed := isEpochDirectionEncodePlacedProg_154 H
  have hprev_len := epochDirectionPrevBytes_len_of_ne_empty d hprev_ne
  refine step_epochDir_push_prev_tag_placed A.repAlloc hfn_ed v curCap curPtr prevPtr sp bs1 d hlt
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1 hvmp01
  rw [← A.pool_of_vmPreserved hvmp01]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_148).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1 hinv1
    rw [← A.pool_of_vmPreserved hvmp1]
    have hvarint_fit : (bs1 ++ [0x1a#8]).length +
        (encodeVarint (BitVec.ofNat 64 d.prev.length)).length ≤ curCap.toNat ∨
        (bs1 ++ [0x1a#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
    have hle_v : (bs1 ++ [0x1a#8]).length +
        (encodeVarint (BitVec.ofNat 64 d.prev.length)).length ≤ finalLen := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_ed_encode_varint_det_call_placed A lim henc
      (BitVec.ofNat 64 d.prev.length) v curCap curPtr sp ((blkPl_154).base + 384#64)
      (bs1 ++ [0x1a#8]) curSt hvarint_fit (fitsEvents_encodeVarint_of_env hEnv hle_v)
      (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
      (by sep_ac_rfl) ?_
    intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2 hdet2
    let evs_v := encodeVarintEvents
      (EncodeVarintGhost.mk (BitVec.ofNat 64 d.prev.length) v curCap curPtr (bs1 ++ [0x1a#8]))
    have hchain_v := vecU8ReserveChain_encodeVarint (v := v) (curPtr := curPtr) hle_v hdet2
    have hEnv_v := (fitsEvents_and_step_of_chain hEnv hchain_v).2
    let bs2 := (bs1 ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 d.prev.length)
    have hbs2_len : bs2.length + d.prev.length = bs1.length + (epochDirectionPrevBytes d).length := by
      dsimp [bs2]; rw [List.length_append, List.length_append, List.length_singleton, hprev_len]
      omega
    have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by
      rw [hcs12.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = prevPtr := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap2) (ptr := ptr2)
      (bs := bs2) (F := A.pool lim (M.stepEvents evs_v curSt) s2 ∗
        stackAt (sp - 64#64) (0x30 + resStack) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
      (by dsimp [bs2, evs_v]; sep_ac_rfl) fun hle2 hcap2_lt _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap2 ptr2 bs2, vecHeader]
    have hprev_lt63 : d.prev.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
    by_cases hneed : cap2.toNat < bs2.length + d.prev.length
    · have hfit_prev : bs2.length + d.prev.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
      have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.prev.length) = true :=
        (elem_len_ult_spare_iff hle2 hcap2_lt hprev_lt63).mpr hneed
      obtain ⟨hnot_ult, hle3, hge3, hbound_prev⟩ := elem_len_after_reserve_not_ult hfit_prev hneed
      have hchain_r := vecU8ReserveChain_doReserve v cap2 ptr2 bs2 d.prev.length finalLen
        (by omega) (by omega) hbound_prev
      obtain ⟨hfits_r, hEnv_r⟩ := fitsEvents_and_step_of_chain hEnv_v hchain_r
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_157).base)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp2 hinv2
        rw [← A.pool_of_vmPreserved hvmp2]
        refine step_ed_do_reserve2_call_placed hres A lim hdoReserve v cap2 ptr2 sp
          ((blkPl_154).base + 632#64) bs2 d.prev.length (M.stepEvents evs_v curSt)
          hbound_prev hfits_r (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
        intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
        let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length d.prev.length)
        let evs_r := doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 d.prev.length)
        change (BitVec.ofNat 64 d.prev.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true
          at hnot_ult
        have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
        have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by
          rw [hcs23.2.1]; simp only [arm64_norm, *]
        have hx21_3 : s3.readReg64 .x21 = prevPtr := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v cap3 ptr3 bs2, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_154).base + 404#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hvmp3 hinv3
          rw [← M.stepEvents_append] at hEnv_r
          rw [← A.pool_of_vmPreserved hvmp3, ← M.stepEvents_append]
          exact hstep404 v cap3 ptr3 dirA nextPtr prevPtr sp bs2 d
            (M.stepEvents (evs_v ++ evs_r) curSt) hprev_ne hle3
            (F := stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
            (fun sm hpcm hrunm hspm htrm hcsm =>
              SepWPp.weaken_pre
                (by
                  dsimp [bs2]
                  rw [bs_append_epochDirectionPrevBytes_of_ne_empty bs1 d hprev_ne]
                  exact Entails.of_eq (by sep_ac_rfl))
                (hnext sm cap3 ptr3 (evs_v ++ evs_r) hpcm hrunm hspm htrm hcsm
                  (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega))
                  (hchain_v.trans (Nat.le_refl _) hchain_r) hEnv_r))))
    · have hle_fast : bs2.length + d.prev.length ≤ cap2.toNat := by omega
      have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.prev.length) = false :=
        Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hprev_lt63).mp h)
      have hpres_all : bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat →
          cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_154).base + 404#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp2 hinv2
        rw [← A.pool_of_vmPreserved hvmp2]
        exact hstep404 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d
          (M.stepEvents evs_v curSt) hprev_ne hle_fast
          (F := stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
          (fun sm hpcm hrunm hspm htrm hcsm =>
            SepWPp.weaken_pre
              (by
                dsimp [bs2]
                rw [bs_append_epochDirectionPrevBytes_of_ne_empty bs1 d hprev_ne]
                exact Entails.of_eq (by sep_ac_rfl))
              (hnext sm cap2 ptr2 evs_v hpcm hrunm hspm htrm hcsm hge2 hpres_all hchain_v hEnv_v))))

/-- Step 4 for `encode<EpochDirection> [local#1]` (`+328 .. +432`, Block `154`). -/
theorem step_prev_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_154 H) (blkPl_148).base
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_154 H) (blkPl_157).base
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_154 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v cap2 ptr2 dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8))
    (d : EpochDirectionPB) (curSt : M.σ) (finalLen : Nat)
    (hprev_lt : d.prev.length < 2 ^ 63)
    (hfit : bs2.length + (epochDirectionPrevBytes d).length ≤ cap2.toNat ∨
      bs2.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62)
    (hle_fin : bs2.length + (epochDirectionPrevBytes d).length ≤ finalLen)
    (hEnv : FitsEnv M lim curSt (VecU8EncodeEnv cap2.toNat finalLen))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_154).base + 328#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v cap2 ptr2 bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_154).base + 432#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → AuthEncodeCalleeSavedPlaced s0 sm → cap2.toNat ≤ cap3.toNat →
      (bs2.length + (epochDirectionPrevBytes d).length ≤ cap2.toNat →
        cap3 = cap2 ∧ ptr3 = ptr2) →
      VecU8ReserveChain cap2.toNat cap3.toNat finalLen evs →
      FitsEnv M lim (M.stepEvents evs curSt) (VecU8EncodeEnv cap3.toNat finalLen) →
      SepWPp (lsProg_154 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3 (bs2 ++ epochDirectionPrevBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗
          A.pool lim (M.stepEvents evs curSt) sm ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_154 H) ret s P Q Qp oom := by
  have hstep352 := step_prev_from_352_1_placed hres A lim H henc hdoReserve hmemcpy
  subst hP
  have ⟨hprev_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := d.prev) (by omega)
  cases hp : d.prev.isEmpty
  · have hprev_len := epochDirectionPrevBytes_len_of_ne_empty d hp
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap2) (ptr := ptr2)
      (bs := bs2) (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗
        A.pool lim curSt s ∗ stackAt (sp - 64#64) (0x30 + resStack) ∗ F)
      (by sep_ac_rfl) fun hcap2_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap2 ptr2 bs2, vecHeader, epochDirectionElemsAt]
    by_cases hcap2 : cap2 == BitVec.ofNat 64 bs2.length
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_157).base)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0
        rw [← A.pool_of_vmPreserved hvmp0]
        have hcap_eq : cap2.toNat = bs2.length :=
          cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap2_le (BitVec.isLt cap2)) hcap2
        have hfit2 : bs2.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62 := by
          rcases hfit with h | h <;> omega
        obtain ⟨_, hbound1, _, _⟩ := reserveCap_one_bounds hcap_eq (by omega)
        have hchain_res := vecU8ReserveChain_doReserve v cap2 ptr2 bs2 1 finalLen
          (by omega) (by omega) hbound1
        obtain ⟨hfits_res, hEnv_res⟩ := fitsEvents_and_step_of_chain hEnv hchain_res
        refine step_ed_do_reserve2_call_placed hres A lim hdoReserve v cap2 ptr2 sp
          ((blkPl_154).base + 608#64) bs2 1 curSt hbound1 hfits_res
          (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try sep_ac_rfl)
          ?_
        intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
        let newCap1 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length 1)
        let evs_res := doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 1)
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs2, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_154).base + 352#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hvmp1 hinv1
          rw [← A.pool_of_vmPreserved hvmp1]
          exact hstep352 v newCap1 newPtr1 dirA nextPtr prevPtr sp bs2 d
            (M.stepEvents evs_res curSt) finalLen hp (by dsimp [newCap1]; omega) (Or.inr hfit2)
            hle_fin hEnv_res (F := F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
            (fun sm cap3 ptr3 evs2 hpcm hrunm hspm htrm hcsm hge2 _ hchain2 hEnv2 => by
              rw [← M.stepEvents_append] at hEnv2
              exact SepWPp.weaken_pre
                (by rw [← M.stepEvents_append]; exact Entails.of_eq (by sep_ac_rfl))
                (hnext sm cap3 ptr3 (evs_res ++ evs2) hpcm hrunm hspm htrm hcsm
                  (Nat.le_trans (by dsimp [newCap1]; omega) hge2) (fun h => absurd h (by omega))
                  (hchain_res.trans (Nat.le_refl _) hchain2) hEnv2))))
    · have hlt1 : bs2.length < cap2.toNat :=
        lt_cap_toNat_of_beq_false hcap2_le (Bool.eq_false_iff.mpr hcap2)
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_154).base + 352#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0
        rw [← A.pool_of_vmPreserved hvmp0]
        exact hstep352 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d curSt finalLen hp hlt1 hfit
          hle_fin hEnv (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try sep_ac_rfl)
          hnext)
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_154).base + 432#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0
      refine SepWPp.weaken_pre
        (by
          rw [← A.pool_of_vmPreserved hvmp0, ← M.stepEvents_nil curSt,
            bs_append_epochDirectionPrevBytes_of_empty bs2 d hp]
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ cap2 ptr2 [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (.nil _ _) hEnv))

/-! ## 2. Top-Level Relocatable Correctness of `encode<EpochDirection> [local#1]` (Block `154`) -/

theorem epochDirection1_core_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    (henc0 : subroutine_ok (lsProg_148 H) (blkPl_148).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_157 H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim)))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_154 H) (blkPl_154).base
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedCoreSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  have hfn_ed := isEpochDirectionEncodePlacedProg_154 H
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre
  dsimp only [encodeEpochDirectionPinnedCoreSpecOf, encodeEpochDirectionPinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
    satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hx1, hx2, hlen_fit, hEnv0⟩, hpre_mem⟩ := hpre_pure
  obtain ⟨hnext_lt, hprev_lt, hnext_cap0, hprev_cap0⟩ :=
    epochDirectionPBPinnedAt_bounds_of_satisfies (A := A.repAlloc) (g := x.g) (dirA := x.dirA)
      (d := x.dir) (F := vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s0 ∗
        stackAt s0.sp (authEncodeStackOf resStack) ∗ R) hpre_mem
  have hpre_rewritten : s0.mem ⊨ ((vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗
      A.pool lim st0 s0 ∗ stackAt s0.sp (authEncodeStackOf resStack)) ∗
      epochDirectionRestAt A.repAlloc x.g x.dirA x.dir) ∗ R := by
    rw [epochDirectionPBPinnedAt_eq_elems A.repAlloc x.g x.dirA x.dir hnext_cap0 hprev_cap0]
      at hpre_mem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre_mem
  refine ⟨_, R, hpre_rewritten, ?_⟩
  let finalLen := x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length
  have htot_split := encodeEpochDirectionMsg_len_split x.tag x.dir
  have htot_len := epochDirectionPBEncodedLen_eq_fields_len x.dir
  have hlen_pb_lt : epochDirectionPBEncodedLen x.dir < 2 ^ 64 := by
    rw [htot_len]; rcases hlen_fit with h | h <;> omega
  have hfit_hdr : x.bs.length + (epochDirectionHeaderBytes x.tag x.dir).length ≤ x.cap.toNat ∨
      x.bs.length + (epochDirectionHeaderBytes x.tag x.dir).length + 10 < 2 ^ 62 := by
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  have henc : subroutine_ok (lsProg_154 H) (blkPl_148).base
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)) :=
    subroutine_ok_withAuthEncodeCSPlaced_placed_blk s0 hcl0 henc0
  have hdoReserve : subroutine_ok (lsProg_154 H) (blkPl_157).base
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)) :=
    subroutine_ok_withAuthEncodeCSPlaced_placed_blk s0 hcl0 hdoReserve0
  have hmemcpy : subroutine_ok (lsProg_154 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec :=
    spqr_hook_ok_of_mem hmc
  let S := epochDirectionSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
    (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
  refine step_hdr_1_placed hres A lim H henc
    x.tag x.v x.cap x.ptr x.dirA x.g.next.ptr x.g.prev.ptr s0.sp x.bs x.dir st0 finalLen
    hnext_lt hprev_lt hlen_pb_lt hfit_hdr (by dsimp [finalLen]; omega) hEnv0
    (F := epochDirectionRestAt A.repAlloc x.g x.dirA x.dir)
    hpc hrun rfl halign rfl hw0 hx1 hx2 (AuthEncodeCalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    hge1 hpres1 hchain1 hEnv1
  let bs1 := x.bs ++ epochDirectionHeaderBytes x.tag x.dir
  let st1 := M.stepEvents evs1 st0
  have hfit_ctr : bs1.length + (epochDirectionCtrBytes x.dir).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionCtrBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs1]; rw [List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  have hle_ctr : bs1.length + (epochDirectionCtrBytes x.dir).length ≤ finalLen := by
    dsimp [bs1, finalLen]; rw [List.length_append]; omega
  refine step_ctr_1_placed hres A lim H henc hdoReserve
    x.v cap1 ptr1 x.dirA s0.sp bs1 x.dir st1 finalLen hfit_ctr hle_ctr hEnv1
    (F := epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗ S ∗
      epochDirectionRestAt A.repAlloc x.g x.dirA x.dir)
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    (by dsimp [bs1, st1, S]; sep_ac_rfl) ?_
  intro s2 cap2 ptr2 evs2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
    hge2 hpres2 hchain2 hEnv2
  let bs2 := bs1 ++ epochDirectionCtrBytes x.dir
  let st2 := M.stepEvents evs2 st1
  have hfit_next : bs2.length + (epochDirectionNextBytes x.dir).length ≤ cap2.toNat ∨
      bs2.length + (epochDirectionNextBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs2, bs1]; rw [List.length_append, List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  have hle_next : bs2.length + (epochDirectionNextBytes x.dir).length ≤ finalLen := by
    dsimp [bs2, bs1, finalLen]; rw [List.length_append, List.length_append]; omega
  refine step_next_1_placed hres A lim H henc hdoReserve hmemcpy
    x.v cap2 ptr2 x.dirA x.g.next.ptr x.g.prev.ptr s0.sp bs2 x.dir st2 finalLen
    hnext_lt hfit_next hle_next hEnv2
    (F := S ∗ epochDirectionRestAt A.repAlloc x.g x.dirA x.dir)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
    (by dsimp [bs2, st2, S]; sep_ac_rfl) ?_
  intro s3 cap3 ptr3 evs3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hcs3
    hge3 hpres3 hchain3 hEnv3
  let bs3 := bs2 ++ epochDirectionNextBytes x.dir
  let st3 := M.stepEvents evs3 st2
  have hfit_prev : bs3.length + (epochDirectionPrevBytes x.dir).length ≤ cap3.toNat ∨
      bs3.length + (epochDirectionPrevBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs3, bs2, bs1]; rw [List.length_append, List.length_append, List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  have hle_prev : bs3.length + (epochDirectionPrevBytes x.dir).length ≤ finalLen := by
    dsimp [bs3, bs2, bs1, finalLen]
    rw [List.length_append, List.length_append, List.length_append]; omega
  refine step_prev_1_placed hres A lim H henc hdoReserve hmemcpy
    x.v cap3 ptr3 x.dirA x.g.next.ptr x.g.prev.ptr s0.sp bs3 x.dir st3 finalLen
    hprev_lt hfit_prev hle_prev hEnv3
    (F := S ∗ epochDirectionRestAt A.repAlloc x.g x.dirA x.dir)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 hcs3
    (by dsimp [bs3, st3, S]) ?_
  intro s4 cap4 ptr4 evs4 hpc4 hrun4 hsp4 htr4 hcs4 hge4 hpres4 hchain4 _
  refine step_epochDir_epilogue_placed hres hfn_ed s0.sp
    (F := vecU8At A.repAlloc x.v cap4 ptr4 (bs3 ++ epochDirectionPrevBytes x.dir) ∗
      epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗
      A.pool lim (M.stepEvents evs4 st3) s4 ∗
      epochDirectionRestAt A.repAlloc x.g x.dirA x.dir)
    hpc4 hrun4 hsp4 halign htr4 hcs4 (by dsimp [S]; sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hcc hinvf hvmpf
  refine ⟨fun hm => ?_, hspf, hcc⟩
  let evsAll := ((evs1 ++ evs2) ++ evs3) ++ evs4
  have hchainAll : VecU8ReserveChain x.cap.toNat cap4.toNat finalLen evsAll :=
    (((hchain1.trans (Nat.le_refl _) hchain2).trans (Nat.le_refl _) hchain3).trans
      (Nat.le_refl _) hchain4)
  have hEnvAll : EncodeEpochDirectionPinnedEnv x evsAll := ⟨cap4.toNat, hchainAll⟩
  have hnilAll : finalLen ≤ x.cap.toNat → evsAll = [] :=
    fun hle => (hchainAll.eq_nil_of_le hle).2
  have hge_all : x.cap.toNat ≤ cap4.toNat :=
    Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 hge4))
  have hpres_all : finalLen ≤ x.cap.toNat → cap4 = x.cap ∧ ptr4 = x.ptr := by
    intro hfit_cap
    obtain ⟨hc1, hp1⟩ := hpres1 (by dsimp [finalLen] at hfit_cap; omega)
    obtain ⟨hc2, hp2⟩ := hpres2 (by dsimp [bs1, finalLen] at hfit_cap ⊢; rw [hc1, List.length_append]; omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by
      dsimp [bs2, bs1, finalLen] at hfit_cap ⊢
      rw [hc2, hc1, List.length_append, List.length_append]; omega)
    obtain ⟨hc4, hp4⟩ := hpres4 (by
      dsimp [bs3, bs2, bs1, finalLen] at hfit_cap ⊢
      rw [hc3, hc2, hc1, List.length_append, List.length_append, List.length_append]; omega)
    exact ⟨hc4.trans (hc3.trans (hc2.trans hc1)), hp4.trans (hp3.trans (hp2.trans hp1))⟩
  have hst_eq : M.stepEvents evs4 st3 = M.stepEvents evsAll st0 := by
    dsimp [evsAll, st3, st2, st1]
    rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  dsimp only [withLsCodeLoaded, encodeEpochDirectionPinnedCoreSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨evsAll, cap4, ptr4, ?_⟩
  dsimp [bs3, bs2, bs1] at hm
  rw [← A.pool_of_vmPreserved hvmpf, hst_eq] at hm
  have hgoal : sf.mem ⊨
      ⌜x.cap.toNat ≤ cap4.toNat ∧
        (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
          cap4 = x.cap ∧ ptr4 = x.ptr)⌝ ∗
      ⌜EncodeEpochDirectionPinnedEnv x evsAll ∧
        (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
          evsAll = [])⌝ ∗
      (epochDirectionPBPinnedAt A.repAlloc x.g x.dirA x.dir ∗
        vecU8At A.repAlloc x.v cap4 ptr4 (x.bs ++ encodeEpochDirectionMsg x.tag x.dir) ∗
        A.pool lim (M.stepEvents evsAll st0) sf ∗
        stackAt s0.sp (authEncodeStackOf resStack) ∗ R) := by
    simp only [satisfies_pure_sepConj]
    refine ⟨⟨hge_all, hpres_all⟩, ⟨hEnvAll, hnilAll⟩, ?_⟩
    rw [epochDirectionPBPinnedAt_eq_elems A.repAlloc x.g x.dirA x.dir hnext_cap0 hprev_cap0,
      ← bs0_append_encodeEpochDirectionMsg x.bs x.tag x.dir]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal

theorem encode_epochDirection_1_pinned_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodeEpochDirection154PinnedPlacedOk A lim H :=
  subroutine_ok_encodeEpochDirectionPinned_of_core
    (epochDirection1_core_placed_ok (by decide) A lim H
      (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc) hmc)
    (fun s0 => epochDirection1_core_placed_ok (by decide) (withVmAnchor A lim s0)
      noAllocEnforcedLimits H
      (encodeVarint2_det_noAllocEnforced_placed_ok (by decide) (withVmAnchor A lim s0) H)
      (doReserve2_noAllocEnforced_ok (withVmAnchor A lim s0)) hmc)

theorem encode_epochDirection_1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodeEpochDirection154PlacedOk A lim H :=
  epochDirection_unpinned_of_pinned_placed_x
    (encode_epochDirection_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_epochDirection_1_pinned_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodeEpochDirection154PinnedPlacedOkX A lim H :=
  subroutine_ok_encodeEpochDirectionPinned_of_core
    (epochDirection1_core_placed_ok (by decide) A lim H
      (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc) hmc)
    (fun s0 => epochDirection1_core_placed_ok (by decide) (withVmAnchor A lim s0)
      noAllocEnforcedLimits H
      (encodeVarint2_det_noAllocEnforced_placed_ok (by decide) (withVmAnchor A lim s0) H)
      (doReserve2_noAllocEnforced_ok (withVmAnchor A lim s0)) hmc)

theorem encode_epochDirection_1_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EncodeEpochDirection154PlacedOkX A lim H :=
  epochDirection_unpinned_of_pinned_placed_x
    (encode_epochDirection_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

abbrev encode_epochDirection_1_pinned_placed_ok_ext := @encode_epochDirection_1_pinned_placed_ok
abbrev encode_epochDirection_1_placed_ok_ext := @encode_epochDirection_1_placed_ok
abbrev encode_epochDirection_1_pinned_placed_ok_ext_x := @encode_epochDirection_1_pinned_placed_ok_x
abbrev encode_epochDirection_1_placed_ok_ext_x := @encode_epochDirection_1_placed_ok_x

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirection1Budget
