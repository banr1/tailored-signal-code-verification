/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudgetAux1
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Join Proofs for `<spqr::chain::Chain>::from_pb` (Block `364`)

Success-path and `params = none` code-loaded `[LibsignalPlacement]` join lemmas for Block `364`
under `RustCliAllocBudget M`, re-exporting the bad-direction and error-path lemmas from
`FromPbJoinClPlacedBudgetAux1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_364 blkPl_364 lsmpl lsρ withLsCodeLoaded withMemEq
)
open CryptoVerification.SpqrV1.Drop (dropStack32 vecCapPtrDealloc)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinBudget (
  fromPbRetPost fromPb_epilogue_dealloc_placed fromPb_epilogue_ret_placed
)
open LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudgetAux1 (
  csel_ult_sub_zero_of_le deallocFreeOnlySpec div_112_magic_nat_eq
  fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded
  pool_entails_empty_arrayAt_pool_budget sepWP_evs_dealloc sepWP_evs_nil
  sepWP_prepend_evs seq_clean_evs seq_clean_evs_lscl seq_vm_clean seq_vm_clean_lscl
  subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoEpochSliceSpec)
open CryptoVerification.LibsignalSpqrV1 (ChainEpoch Direction)
open CryptoVerification.RustHeap (arrayAt)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainEpochGhost TraceCalleeSaved arrayAt_chainEpochAt_entails_unpinned
  bitvec_low_byte_clear_zero calleeSavedFromPbAt cap_mul_112_shift_eq chainEpoch
  chainEpochAt chainEpochSize chainFromPbSubStack chainFromPb_of_ok
  chainFromPb_of_params_none chainPBHeadersAt chainPBHeadersAt_entails_memRegion_80
  chainResultAt_ok_pack csel_both_zero csel_eq_zero_if_ptr_eq csel_min_eq_of_le
  csel_sub_zero_of_le csel_ult_min_eq_of_le csel_zero_if_ptr_eq div_112_magic_eq
  err_stateDecode_pack_words joinScratchAt joinScratchAt_entails_memRegion_96
  linksRawAllocAt linksRawAllocAt_combine_memRegion memRegion_56_split_chainTail
  memRegion_88_words4_rest stackAt_subStack_split_allocHook
  stackAt_subStack_split_dropStack32 sub_links_conv_112 vecU8BufAt vecU8BufAt_entails_dealloc
)
open CryptoVerification.SpqrV1.Top.ChainFrom (ChainFromPbCall)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (chainResultAt optChainParamsPBAt)

namespace LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] csel_both_zero

@[local simp, local arm64_norm, local wp_norm]
private theorem sub_self_lsr4_mul_magic (a : BitVec 64) :
    ((a - a) >>> 4) * 0x6db6db6db6db6db7#64 = 0#64 := by
  rw [BitVec.sub_self]; rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sub_self_lsr4_bv_mul_magic (a : BitVec 64) :
    ((a - a) >>> 4#64) * 0x6db6db6db6db6db7#64 = 0#64 := by
  rw [BitVec.sub_self]; rfl

export LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudgetAux1 (
  fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded
  fromPb_bad_direction_cl_placed
  fromPb_join_err_tail_cl_placed
  fromPb_join_err_840_cl_placed
  fromPb_join_err_cl_placed
)

/-! ## Success and `params = none` Code-Loaded Join Lemmas (`blkPC_364`) -/

set_option maxHeartbeats 800000 in
theorem fromPb_join_params_none_tail_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State)
    (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 1100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx19 : s.readReg64 .x19 = 0#64) (hx20 : s.readReg64 .x20 = x.gPb.linksPtr)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx25 : s.readReg64 .x25 = x.gPb.linksCap)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗
        A.pool lim st s ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ M A lim H x
  have hep_dealloc := @fromPb_epilogue_dealloc_placed _ M A lim H hdealloc x
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hep_ret hep_dealloc hdealloc_fo hpc ⊢
  refine seq_clean_evs (mid := (blkPl_364).base + 1112#64)
    (P_evs := fun evs sm => chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗
      memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .x20 = x.gPb.linksPtr ∧ sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧
      sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool_budget A lim st s (chainEpoch A.repAlloc) 112 x.gPb.linksPtr)
      (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    have hcall := fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hchain_slice hcl
    dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hcall
    wp_call hcall (⟨x.gPb.linksPtr, []⟩, st)
    rw [hsp, memRegion_zero, emp_sepConj, ← stackAt_subStack_split_dropStack32 s0.sp]
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_subStack_split_dropStack32 s0.sp).symm)
      (by sep_focus) ?_
    have hevs_1 : FreeOnlyEvs w := by assumption
    have hacp_s0 : AllocCallPreserved s0 sf := by
      refine hacp.trans ?_
      simp only [wp_norm, arm64_norm] at *
      assumption
    rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
    refine SepWP.mono (post := fun sm Pm =>
        (Pm ⊢ chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
          memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
          linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecCapPtrDealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗
          A.pool lim (M.stepEvents w st) sm ∗
          joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
        sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .x20 = x.gPb.linksPtr ∧ sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧
        sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x25 = x.gPb.linksCap)
      ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_1, hp, hq⟩)
    wp_done
  · rintro evs1 s3 hevs1 hpc3 hrun3 ⟨hsp3, htr3, hacp3, hx20_3, hx21_3, hx22_3, hx25_3⟩
    apply sepWP_prepend_evs hevs1
    let st1 := M.stepEvents evs1 st
    rw [hpb_len]
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean_evs (mid := (blkPl_364).base + 1136#64)
      (P_evs := fun evs sm => chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗
        memRegion x.pbPtr 80 ∗
        vecCapPtrDealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp3
      by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        rw [stackAt_subStack_split_allocHook s0.sp]
        apply sepWP_evs_dealloc (x.gPb.linksCap.toNat * 112) 8
        wp_steps
        wp_call hdealloc_fo (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8, st1)
        rw [hsp3]
        have hacp_s0 : AllocCallPreserved s0 sf := by
          refine hacp3.trans ?_
          simp only [wp_norm, arm64_norm] at *
          assumption
        rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
        wp_done
    · rintro evs2 s4 hevs2 hpc4 hrun4 ⟨hsp4, htr4, hacp4, hx21_4, hx22_4⟩
      apply sepWP_prepend_evs hevs2
      let st2 := M.stepEvents evs2 st1
      have ⟨_, _, _, _, _, _, _⟩ := hacp4
      unfold vecCapPtrDealloc
      refine SepWP.focus_weaken
        (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val) (by sep_focus) ?_
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_vm_clean (mid := (blkPl_364).base + 1140#64)
          (P_mid := chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
            A.pool lim st2 s4 ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            AllocCallPreserved s0 sm) ?_ ?_
        · by_vm_steps (wp_steps; wp_done)
        · rintro s5 hpc5 hrun5 hvm5 ⟨hsp5, htr5, hacp5⟩
          rw [← A.pool_of_vmPreserved hvm5]
          exact hep_ret st2 s0 s5 hacp5 hsp0_align hpc5 hrun5 hsp5 htr5
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_vm_clean (mid := (blkPl_364).base + 1008#64)
          (P_mid := chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
            A.pool lim st2 s4 ∗
            A.repAlloc.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            AllocCallPreserved s0 sm ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · by_vm_steps (wp_steps; wp_done)
        · rintro s5 hpc5 hrun5 hvm5 ⟨hsp5, htr5, hacp5, hx0_5, hx1_5⟩
          rw [← A.pool_of_vmPreserved hvm5]
          exact hep_dealloc st2 s0 s5 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hacp5 hsp0_align hnr hn_lt hn_ne hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5

set_option maxHeartbeats 800000 in
theorem fromPb_join_ok_840_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State) (dir : Direction)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : CryptoVerification.LibsignalSpqrV1.Direction.fromI32? x.pb.direction = some dir)
    (hdir_i32 : dir.toI32 = x.pb.direction)
    (hlinks : CryptoVerification.LibsignalSpqrV1.Chain.linksFromPb x.pb.links = .ok convEpochs)
    (hconv_len : convG.length = convEpochs.length) (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ M A lim H x
  have hnone_tail := @fromPb_join_params_none_tail_cl_placed _ M A lim H hdealloc hchain_slice x
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by rw [hpb_len]; exact hlen_lt
  have hconv_le_cap : convEpochs.length ≤ x.gPb.linksCap.toNat := by rw [hpb_len]; exact hl_le
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  dsimp only [chainEpochSize, BitVec.ofNat_eq_ofNat] at hep_ret hnone_tail hpc ⊢
  cases hp : x.pb.params with
  | some cp =>
    have hfromPb_eq : CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb = .ok {
        dir := dir, currentEpoch := x.pb.currentEpoch, sendEpoch := x.pb.sendEpoch,
        nextRoot := x.pb.nextRoot, links := convEpochs, params := cp } :=
      chainFromPb_of_ok hdir hlinks hp
    rw [memRegion_88_words4_rest x.out, memRegion_56_split_chainTail x.out]
    wp_pull_exists
    refine seq_vm_clean (mid := (blkPl_364).base + 1140#64)
      (P_mid := chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
        A.pool lim st s ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp
      by_vm_steps (
        unfold chainPBHeadersAt optChainParamsPBAt joinScratchAt
        rw [hp]; dsimp only
        wp_steps
        have hhdr :
            (x.pbPtr ↦₆₄ x.gPb.linksCap) ∗ ((x.pbPtr + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
              ((x.pbPtr + 16#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
              ((x.pbPtr + 24#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.pbPtr + 32#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
              ((x.pbPtr + 40#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
              ((x.pbPtr + 48#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.pbPtr + 56#64) ↦₆₄ x.pb.sendEpoch) ∗
              (((x.pbPtr + 64#64) ↦₃₂ 1#32) ∗ ((x.pbPtr + 64#64 + 4#64) ↦₃₂ cp.maxJump) ∗
                ((x.pbPtr + 64#64 + 8#64) ↦₃₂ cp.maxOooKeys)) ∗
              ((x.pbPtr + 76#64) ↦₃₂ x.pb.direction) ⊢ memRegion x.pbPtr 80 := by
          have := chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb
          unfold chainPBHeadersAt optChainParamsPBAt at this; rw [hp] at this; exact this
        refine SepWP.focus_weaken hhdr (by sep_focus) ?_
        have hpack :
            (x.out ↦₆₄ x.gPb.linksCap) ∗ ((x.out + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
              ((x.out + 16#64) ↦₆₄ 0#64) ∗ ((x.out + 24#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
              ((x.out + 32#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.out + 40#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
              ((x.out + 48#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
              ((x.out + 56#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.out + 64#64) ↦₆₄ x.pb.sendEpoch) ∗
              ((x.out + 72#64) ↦₃₂ cp.maxJump) ∗ ((x.out + 76#64) ↦₃₂ cp.maxOooKeys) ∗
              ((x.out + 80#64) ↦₃₂ x.pb.direction) ∗ memRegion (x.out + 84#64) 4 ∗
              arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
              linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
              vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ⊢
              chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) := by
          rw [hfromPb_eq, ← hdir_i32, ← hpb_len]
          exact chainResultAt_ok_pack A.repAlloc x.out x.gPb.linksCap x.gPb.linksPtr
            x.gPb.nextRoot.cap x.gPb.nextRoot.ptr convG convEpochs x.pb.nextRoot
            x.pb.currentEpoch x.pb.sendEpoch cp dir
            hconv_len hconv_le_cap hl_lt hl_ne hn_le hn_lt hn_ne
        refine SepWP.focus_weaken hpack (by sep_focus) ?_
        refine SepWP.focus_weaken
          (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
          (by unfold joinScratchAt; sep_focus) ?_
        wp_done)
    · rintro s2 hpc2 hrun2 hvm2 ⟨hsp2, htr2, hacp2⟩
      rw [← A.pool_of_vmPreserved hvm2]
      exact hep_ret st s0 s2 hacp2 hsp0_align hpc2 hrun2 hsp2 htr2
  | none =>
    have hfromPb_eq : CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb = .error .stateDecode :=
      chainFromPb_of_params_none hdir hlinks hp
    have hcsel1 := csel_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel1_ult := csel_ult_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel2 := csel_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel2_ult := csel_ult_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel3 := csel_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
    have hcsel3_eq := csel_eq_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
    have hcsel1_pb := csel_sub_zero_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel1_ult_pb := csel_ult_sub_zero_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel2_pb := csel_min_eq_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel2_ult_pb := csel_ult_min_eq_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel3_pb := csel_zero_if_ptr_eq x.gPb.linksPtr x.pb.links.length hlen_lt
    have hcsel3_eq_pb := csel_eq_zero_if_ptr_eq x.gPb.linksPtr x.pb.links.length hlen_lt
    refine SepWP.focus_weaken
      (arrayAt_chainEpochAt_entails_unpinned A.repAlloc convG convEpochs x.gPb.linksPtr hconv_len)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (vecU8BufAt_entails_dealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
      (by sep_focus) ?_
    refine seq_vm_clean_lscl hcl (mid := (blkPl_364).base + 1044#64)
      (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        arrayAt (chainEpoch A.repAlloc) 112 x.gPb.linksPtr convEpochs ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗
        A.pool lim st s ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp
      by_vm_steps (
        unfold chainPBHeadersAt optChainParamsPBAt
        rw [hp]; dsimp only
        wp_steps
        have hhdr :
            (x.pbPtr ↦₆₄ x.gPb.linksCap) ∗ ((x.pbPtr + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
              ((x.pbPtr + 16#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
              ((x.pbPtr + 24#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.pbPtr + 32#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
              ((x.pbPtr + 40#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
              ((x.pbPtr + 48#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.pbPtr + 56#64) ↦₆₄ x.pb.sendEpoch) ∗
              (((x.pbPtr + 64#64) ↦₃₂ 0#32) ∗ memRegion (x.pbPtr + 64#64 + 4#64) 8) ∗
              ((x.pbPtr + 76#64) ↦₃₂ x.pb.direction) ⊢ memRegion x.pbPtr 80 := by
          have := chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb
          unfold chainPBHeadersAt optChainParamsPBAt at this; rw [hp] at this; exact this
        refine SepWP.focus_weaken hhdr (by sep_focus) ?_
        wp_done)
    · rintro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, htr1, hacp1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1⟩
      rw [← A.pool_of_vmPreserved hvm1]
      rw [memRegion_88_words4_rest x.out]
      wp_pull_exists
      refine seq_vm_clean_lscl hcl1 (mid := (blkPl_364).base + 1096#64)
        (P_mid := chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
          arrayAt (chainEpoch A.repAlloc) 112 x.gPb.linksPtr convEpochs ∗
          linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecCapPtrDealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗
          A.pool lim st s1 ∗
          joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sc => sc.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sc s0 ∧
          AllocCallPreserved s0 sc ∧
          sc.readReg64 .x0 = x.gPb.linksPtr ∧
          sc.readReg64 .x1 = BitVec.ofNat 64 convEpochs.length ∧
          sc.readReg64 .x19 = 0#64 ∧ sc.readReg64 .x20 = x.gPb.linksPtr ∧
          sc.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sc.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
          sc.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
      · have ⟨_, _, _, _, _, _, _⟩ := hacp1
        by_vm_steps (
          unfold joinScratchAt
          wp_steps
          refine SepWP.focus_weaken
            (err_stateDecode_pack_words A.repAlloc x.out x.pb hfromPb_eq _ _ _ (bitvec_low_byte_clear_zero _))
            (by sep_focus) ?_
          wp_done)
      · rintro sc hpc_c hrun_c hcl_c hvm_c ⟨hsp_c, htr_c, hacp_c, hx0_c, hx1_c, hx19_c, hx20_c, hx21_c, hx22_c, hx25_c⟩
        rw [← A.pool_of_vmPreserved hvm_c]
        refine seq_clean_evs_lscl hcl_c (mid := (blkPl_364).base + 1100#64)
          (P_evs := fun evs sm => chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗
            memRegion x.pbPtr 80 ∗
            memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
            linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
            vecCapPtrDealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = 0#64 ∧ sm.readReg64 .x20 = x.gPb.linksPtr ∧
            sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
            sm.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
        · rw [stackAt_subStack_split_dropStack32 s0.sp]
          have hcall := fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hchain_slice hcl_c
          dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hcall
          wp_call hcall (⟨x.gPb.linksPtr, convEpochs⟩, st)
          rw [hsp_c, ← stackAt_subStack_split_dropStack32 s0.sp]
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_subStack_split_dropStack32 s0.sp).symm)
            (by sep_focus) ?_
          have hacp_2 : AllocCallPreserved sc sf := by assumption
          have hevs_2 : FreeOnlyEvs w := by assumption
          have hacp_s0 : AllocCallPreserved s0 sf := hacp_c.trans hacp_2
          rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.mono (post := fun sm Pm =>
              (Pm ⊢ chainResultAt A.repAlloc x.out (CryptoVerification.LibsignalSpqrV1.Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
                memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
                linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
                vecCapPtrDealloc A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗
                A.pool lim (M.stepEvents w st) sm ∗
                joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
                stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
              sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
              AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = 0#64 ∧ sm.readReg64 .x20 = x.gPb.linksPtr ∧
              sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
              sm.readReg64 .x25 = x.gPb.linksCap)
            ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_2, hp, hq⟩)
          wp_done
        · rintro evs2 s2 hevs2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hacp2, hx19_2, hx20_2, hx21_2, hx22_2, hx25_2⟩
          apply sepWP_prepend_evs hevs2
          exact hnone_tail (M.stepEvents evs2 st) s0 s2 convEpochs sp0_val hcl2 hacp2 hsp0_align
            hpb_len hl_le hl_lt hn_lt hn_ne
            hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2

set_option maxHeartbeats 800000 in
theorem fromPb_join_ok_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec M A lim)))
    (x : ChainFromPbCall) (st : M.σ) (s0 s : State) (dir : Direction)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : CryptoVerification.LibsignalSpqrV1.Direction.fromI32? x.pb.direction = some dir)
    (hdir_i32 : dir.toI32 = x.pb.direction)
    (hlinks : CryptoVerification.LibsignalSpqrV1.Chain.linksFromPb x.pb.links = .ok convEpochs)
    (hconv_len : convG.length = convEpochs.length) (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx29 : s.readReg64 .fp = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
        A.pool lim st s ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost M A lim x st s0) := by
  have h840 := @fromPb_join_ok_840_cl_placed _ M A lim H hdealloc hchain_slice x
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by rw [hpb_len]; exact hlen_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hsub_conv := sub_links_conv_112 x.gPb.linksPtr convEpochs.length
  have hdiv_conv := div_112_magic_eq hconv_lt
  have hdiv_conv_nat := div_112_magic_nat_eq hconv_lt
  have hsub_pb := sub_links_conv_112 x.gPb.linksPtr x.pb.links.length
  have hdiv_pb := div_112_magic_eq hlen_lt
  have hdiv_pb_nat := div_112_magic_nat_eq hlen_lt
  dsimp only [CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at h840 hpc ⊢
  refine seq_clean_evs_lscl hcl (mid := (blkPl_364).base + 840#64)
    (P_evs := fun evs sm => memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x19 = 1#64 ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool_budget A lim st s
        (fun ep addr => CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBAt A.repAlloc addr ep) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)))
      (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps
    have hcall := fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hproto_slice hcl
    dsimp only [withMemEq, dropProtoEpochSliceSpec,
      CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hcall
    wp_call hcall (⟨x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112), []⟩, st)
    rw [hsp, memRegion_zero, emp_sepConj, ← stackAt_subStack_split_dropStack32 s0.sp]
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_subStack_split_dropStack32 s0.sp).symm)
      (by sep_focus) ?_
    have hevs_1 : FreeOnlyEvs w := by assumption
    have hacp_s0 : AllocCallPreserved s0 sf := by
      refine hacp.trans ?_
      simp only [wp_norm, arm64_norm] at *
      assumption
    rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
    refine SepWP.mono (post := fun sm Pm =>
        (Pm ⊢ memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A.repAlloc) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
          linksRawAllocAt A.repAlloc x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A.repAlloc x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
          A.pool lim (M.stepEvents w st) sm ∗
          joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack) ∧
        sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x19 = 1#64 ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.pbPtr)
      ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_1, hp, hq⟩)
    wp_done
  · rintro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hacp1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    apply sepWP_prepend_evs hevs1
    exact h840 (M.stepEvents evs1 st) s0 s1 dir convG convEpochs sp0_val hcl1 hacp1 hsp0_align
      hdir hdir_i32 hlinks hconv_len hpb_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne
      hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1

end LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudget
