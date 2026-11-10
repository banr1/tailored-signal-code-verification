/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeaderPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBranches
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesB
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Phase 2d Infrastructure & `V1State::encoded_len [local#2]` Placed Proof

Proves the `[LibsignalPlacement]` `VmPreserved` `subroutine_ok` contracts for `V1State::encoded_len [local#2]`
(`Block 405`), defines budget-threaded `StepInnerStateAt1880Placed` and the 4 `V1StateChunked1PlacedBudget`
dispatch bridges, and proves `step_encodeToVec_phase2d_placed` (`+1740 .. +1808`, `Block 426`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   blkPC_405 blkPl_405 blkPC_407 blkPl_407 blkPC_414 blkPl_414
   blkPC_405_rebase_fetch_0x7c blkPC_405_rebase_fetch_0xbc
   blkPC_405_rebase_fetch_0x104 blkPC_405_rebase_fetch_0x144
   blkPC_405_rebase_fetch_0x178 blkPC_405_rebase_fetch_0x198
   blkPC_405_rebase_fetch_0x1d8 blkPC_405_rebase_fetch_0x208
   blkPC_405_rebase_fetch_0x258 blkPC_405_rebase_fetch_0x298
   blkPC_405_rebase_fetch_0x2f4 blkPC_405_rebase_fetch_0x334
   blkPC_405_rebase_fetch_0x390 blkPC_405_rebase_fetch_0x3d0
   blkPC_405_rebase_fetch_0x400 blkPC_405_rebase_fetch_0x434
   blkPC_405_rebase_fetch_0x474 blkPC_405_rebase_fetch_0x4a8
   blkPC_405_rebase_fetch_0x4e8
   lsρ lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState V1State VersionNegotiationPB ChainPB)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeOptMessage encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (CallPinnedEncLenAtF FrozenInv PinnedEncLenGhost
   SepWPpF V1StatePBGhost
   bl_reloc_target_eq
   chunkedCt1SampledPBEncodedLen chunkedCt1SampledPBPinnedAt
   ct1Sampled_entry_pinned_wp_p2
   ct1SentPBEncodedLen ct1SentPBPinnedAt
   ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt
   hasJumpTableStepP2_placed_local2
   headerSent_entry_pinned_wp_p2
   noneCap2
   optChainPBPinnedAt optCt1SentPBPinnedAt optCt1SentPBPinnedAt_eq
   optCt1SentRest optCt1SentRest_disc_bounds
   optPolynomialDecoderPBPinnedAt optPolynomialEncoderPBPinnedAt
   optVersionNegotiationPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   v1StateInnerPBPinnedAt v1StateJumpTableBytes
   v1StateJtSymLocal2 v1StatePBEncodedLen v1StatePBEncodedLen_eq_proto v1StatePBPinnedAt
   v1State_entry_ro_pinned_wp_p2)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (EpochEncLenCalleeSaved
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv blkPC_426 blkPl_426
   encodeInner_v1_eq
   encodeToVecCalleeStackOf encodeToVecJumpTableBytes
   encodeToVecJumpTableBytesAt encodeToVecJumpTableBytes_eq
   etvJumpTableRoSym
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optCt1SentCap optPqRatchetInnerCap optPqRatchetInnerPBPinnedAt
   pqRatchetStatePBEncodedLen pqRatchetStatePBEncodedLen_eq_proto pqRatchetStatePBPinnedAt
   v1StateInnerCap v1StateInnerCap_add_two_bounds
   v1StatePBEncodedLen_lt_of_state
   withStepInv)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (LsBlocksCodeLoaded ls_subroutine_ok_blocks_vmPreserved
   ls_subroutine_ok_of_block_in subroutine_ok_of_withVmPreserved
   withLsBlocksCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec v1StateEncodedLenRoSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
  (polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks
   polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget
  (ct2SentEncodedLen_local2_pinned_placed_ok_hooks
   ekSentEncodedLen_local2_pinned_placed_ok_hooks
   headerReceivedEncodedLen_local2_pinned_placed_ok_hooks
   keysUnsampledEncodedLen_local2_pinned_placed_ok_hooks
   noHeaderReceivedEncodedLen_local2_pinned_placed_ok_hooks)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
  (ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_hooks
   ct1SentEncodedLen_local2_pinned_placed_ok_hooks
   ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_hooks
   headerSentEncodedLen_local2_pinned_placed_ok_hooks)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateBudget
  (V1StateEncodedLenLocal2PinnedPlacedOk V1StateEncodedLenLocal2PinnedPlacedOkExt
   V1StateEncodedLenLocal2PlacedOk V1StateEncodedLenLocal2PlacedOkExt)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersBudget
  (v1StateEncodedLen_ro_lscl_ok_of_pinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeVarintExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec leafEncLen48Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudget
  (step_encodeToVec_v1_ct1Acknowledged_placed
   step_encodeToVec_v1_ct1Received_placed
   step_encodeToVec_v1_ct1Sampled_placed
   step_encodeToVec_v1_ekSentCt1Received_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateChunked1PlacedBudgetAux
  (sepWPp_extract_pure)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeaderPlacedBudget
  (step_encodeToVec_inner_none_pool_placed
   step_encodeToVec_inner_some_hdr_placed
   step_encodeToVec_inner_to_1880_pool_placed
   step_encodeToVec_inner_v1_none_pool_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Placed `VmPreserved` Proofs for `V1State::encoded_len [local#2]` (`Block 405`) -/

private def v1StateLocal2Blks : List Nat :=
  [405, 400, 411, 401, 414, 415, 421, 413, 424, 404, 407, 408, 387, 389]

local instance instFrozenInvLsBlocks (blks : List Nat) (pl : MultiPlacement) :
    FrozenInv (LsBlocksCodeLoaded blks pl) where
  keeps h hkf := h.of_keepsFrozen hkf

private theorem subroutine_ok_of_sepWPpF_blocks {α : Type} {prog : Program} {entry : BitVec 64}
    {blks : List Nat} {pl : MultiPlacement} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpF (LsBlocksCodeLoaded blks pl) prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (withLsBlocksCodeLoaded blks pl spec) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsBlocksCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre'⟩
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre' hsp
  refine ⟨P, Fr, hm, ?_⟩
  have hwp0 := hwp hcl0
  intro Fr' hm' hL
  obtain ⟨sf, hsteps, hout⟩ := hwp0 Fr' hm' hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, ⟨_, hq⟩⟩ | hpan | hoom
  · exact Or.inl ⟨hpcf, hrunf, P_f, hmf, hq⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

private theorem ls_subroutine_ok_lsblocks_of_block_in {α : Type} [LibsignalPlacement]
    {callerProg calleeProg : Program} {blks : List Nat} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hj : j ∈ blks)
    (hcallee : subroutine_ok calleeProg entry (withLsBlocksCodeLoaded blks lsmpl spec)) :
    subroutine_ok callerProg entry (withLsBlocksCodeLoaded blks lsmpl spec) :=
  subroutine_ok_mono (ls_subroutine_ok_of_block_in (callerProg := callerProg) hj hcallee)
    (fun _ _ _ hp => by
      dsimp only [withLsBlocksCodeLoaded] at hp ⊢
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp
      rcases hp with ⟨hcl, hp'⟩
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcl, ?_⟩
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl, hp'⟩)
    (fun _ _ _ _ hq => hq)

private theorem callPinnedEncLenAtF_of_bl_blocks_core [LibsignalPlacement]
    {callerProg : Program} {blks : List Nat} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {k : Nat} {imm : BitVec 64}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat} {spec : Spec (PinnedEncLenGhost Ghost Model)}
    (hspec_pre : ∀ x s, spec.pre x s =
      (⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗ repr x.g x.a x.m ∗ stackAt s.sp stackSz))
    (hspec_post : ∀ x s0 sf, spec.post x s0 sf =
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
        repr x.g x.a x.m ∗ stackAt s0.sp stackSz))
    (hspec_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hspec_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hfetch : callerProg.fetch (entry + BitVec.ofNat 64 k) = some (.bl imm))
    (htarget : entry + BitVec.ofNat 64 k + imm = lsmpl.base j)
    (hcall : subroutine_ok callerProg (lsmpl.base j) (withLsBlocksCodeLoaded blks lsmpl spec))
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded blks lsmpl) callerProg entry k repr encLen stackSz := by
  intro ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound hcont hcl0
  subst hsp
  apply SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl0
    (mid := entry + BitVec.ofNat 64 (k + 4))
  wp_steps
  have hlr_eq : entry + BitVec.ofNat 64 k + 4#64 = entry + BitVec.ofNat 64 (k + 4) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine SepWP.call_subroutine_frame (x := ⟨a, g, m⟩) (F := F)
    (ret_pc := entry + BitVec.ofNat 64 (k + 4)) hcall
    (by simp_all) (by simp_all)
    (by simp only [State.spAligned, beq_iff_eq]; simp_all)
    (by simp_all) ?_ ?_ ?_ ?_ (h_oom := ?_)
  · intro R hm
    dsimp only [withLsBlocksCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm (spec.pre _ _) ⌜LsBlocksCodeLoaded blks lsmpl _⌝,
      satisfies_pure_sepConj]
    refine ⟨by simp_all, ?_⟩
    rw [hspec_pre]
    simp only [sepConj_assoc, satisfies_pure_sepConj, arm64_norm]
    refine ⟨⟨by simp_all, hbound⟩, ?_⟩
    convert hm using 1
    · sep_ac_rfl
    · rfl
  · intro R' sf _ hpan
    dsimp only [withLsBlocksCodeLoaded] at hpan
    rw [hspec_panic, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · intro R' code sf _ hex
    dsimp only [withLsBlocksCodeLoaded] at hex
    rw [hspec_exit, satisfies_pure_sepConj] at hex
    exact hex.1
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [withLsBlocksCodeLoaded]
    rw [hspec_post]
    simp only [arm64_norm] at hsp_sf ⊢
    apply SepWP.weaken_pre
      (P' := ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen m) ∧ sf.trace = s.trace⌝ ∗
        ((repr g a m ∗ stackAt s.sp stackSz) ∗ F))
    · exact Entails.of_eq (by sep_ac_rfl)
    · apply SepWP.pure_elim
      rintro ⟨hx0_sf, htr_sf⟩
      apply SepWP.done hpc_sf hrun_sf
      have ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩ := hcs_sf
      have hcs_saved : EpochEncLenCalleeSaved s sf := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
      have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := by
        simp_all
      intro hcl_sf
      exact hcont sf hpc_sf hrun_sf hsp_sf htr_sf hx0_sf hcs_saved hfp_sf hcl_sf
  · intro R' sf _ hoom
    dsimp only [withLsBlocksCodeLoaded] at hoom
    rw [hspec_oom] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

private theorem callPinnedEncLenAtF_of_bl_blocks_plain [LibsignalPlacement]
    {callerProg calleeProg : Program} {blks : List Nat} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {k : Nat} {imm : BitVec 64}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat} {spec : Spec (PinnedEncLenGhost Ghost Model)}
    (hspec_pre : ∀ x s, spec.pre x s =
      (⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗ repr x.g x.a x.m ∗ stackAt s.sp stackSz))
    (hspec_post : ∀ x s0 sf, spec.post x s0 sf =
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
        repr x.g x.a x.m ∗ stackAt s0.sp stackSz))
    (hspec_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hspec_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hj : j ∈ blks)
    (hfetch : callerProg.fetch (entry + BitVec.ofNat 64 k) = some (.bl imm))
    (htarget : entry + BitVec.ofNat 64 k + imm = lsmpl.base j)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) spec)
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded blks lsmpl) callerProg entry k repr encLen stackSz :=
  callPinnedEncLenAtF_of_bl_blocks_core hspec_pre hspec_post hspec_panic hspec_exit
    hfetch htarget (ls_subroutine_ok_of_block_in (callerProg := callerProg) hj hcallee) hspec_oom

private theorem callPinnedEncLenAtF_of_bl_blocks_lsblocks [LibsignalPlacement]
    {callerProg calleeProg : Program} {blks : List Nat} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {k : Nat} {imm : BitVec 64}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat} {spec : Spec (PinnedEncLenGhost Ghost Model)}
    (hspec_pre : ∀ x s, spec.pre x s =
      (⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗ repr x.g x.a x.m ∗ stackAt s.sp stackSz))
    (hspec_post : ∀ x s0 sf, spec.post x s0 sf =
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
        repr x.g x.a x.m ∗ stackAt s0.sp stackSz))
    (hspec_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hspec_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hj : j ∈ blks)
    (hfetch : callerProg.fetch (entry + BitVec.ofNat 64 k) = some (.bl imm))
    (htarget : entry + BitVec.ofNat 64 k + imm = lsmpl.base j)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsBlocksCodeLoaded blks lsmpl spec))
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded blks lsmpl) callerProg entry k repr encLen stackSz :=
  callPinnedEncLenAtF_of_bl_blocks_core hspec_pre hspec_post hspec_panic hspec_exit
    hfetch htarget (ls_subroutine_ok_lsblocks_of_block_in (callerProg := callerProg) hj hcallee) hspec_oom

private theorem chunkedCt1Sampled_on_v1StateLocal2Blks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_407).rebase (blkPl_407).base (hooksException H))
      (blkPl_407).base
      (withLsBlocksCodeLoaded v1StateLocal2Blks lsmpl
        (CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec A)) := by
  refine subroutine_ok_of_sepWPpF_blocks ?_
  refine ct1Sampled_entry_pinned_wp_p2 (LsBlocksCodeLoaded v1StateLocal2Blks lsmpl) _ A _
    (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_blocks_plain (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (by simp only [arm64_norm]; rfl) (by rw [bl_reloc_target_eq])
      (subroutine_ok_of_withVmPreserved
        (ct1SentEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks_plain (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (by simp only [arm64_norm]; rfl) (by rw [bl_reloc_target_eq])
      (subroutine_ok_of_withVmPreserved
        (polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks_plain (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (by simp only [arm64_norm]; rfl) (by rw [bl_reloc_target_eq])
      (subroutine_ok_of_withVmPreserved
        (polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))

private theorem chunkedHeaderSent_on_v1StateLocal2Blks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_414).rebase (blkPl_414).base (hooksException H))
      (blkPl_414).base
      (withLsBlocksCodeLoaded v1StateLocal2Blks lsmpl
        (CryptoVerification.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLenPinnedSpec A)) := by
  refine subroutine_ok_of_sepWPpF_blocks ?_
  refine headerSent_entry_pinned_wp_p2 (LsBlocksCodeLoaded v1StateLocal2Blks lsmpl) _ A _
    (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_blocks_plain (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (by simp only [arm64_norm]; rfl) (by rw [bl_reloc_target_eq])
      (subroutine_ok_of_withVmPreserved
        (ekSentEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks_plain (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (by simp only [arm64_norm]; rfl) (by rw [bl_reloc_target_eq])
      (subroutine_ok_of_withVmPreserved
        (polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks_plain (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (by simp only [arm64_norm]; rfl) (by rw [bl_reloc_target_eq])
      (subroutine_ok_of_withVmPreserved
        (polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))

local macro "v1State_bl_blocks_plain " fetchLem:ident calleeOk:ident A:term:max H:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_blocks_plain (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      ($fetchLem _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm])
      (subroutine_ok_of_withVmPreserved ($calleeOk $A (hooksException $H))))

local macro "v1State_bl_blocks_lsblocks " fetchLem:ident calleeOk:ident A:term:max H:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_blocks_lsblocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      ($fetchLem _ _) (by rw [bl_reloc_target_eq]; simp only [arm64_norm])
      ($calleeOk $A $H))

theorem v1StateEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_405).rebase (blkPl_405).base H)
      (blkPl_405).base
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A (lsρ v1StateJtSymLocal2))) := by
  refine ls_subroutine_ok_blocks_vmPreserved
    (progQ := (blkPC_405).rebase (blkPl_405).base (hooksException H))
    (blks := v1StateLocal2Blks) (i := 405)
    (by decide) (by decide) (by decide +kernel) (hok := subroutine_ok_of_sepWPpF_blocks ?_)
  refine v1State_entry_ro_pinned_wp_p2 (LsBlocksCodeLoaded v1StateLocal2Blks lsmpl) _ A _
    (lsρ v1StateJtSymLocal2)
    (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩)
    (hasJumpTableStepP2_placed_local2 (hooksException H))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x400 keysUnsampledEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x258 headerSentEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x298 polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_lsblocks blkPC_405_rebase_fetch_0x178 chunkedHeaderSent_on_v1StateLocal2Blks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x198 ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x1d8 polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x7c ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0xbc polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x434 noHeaderReceivedEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x474 polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x2f4 headerReceivedEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x334 polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_lsblocks blkPC_405_rebase_fetch_0x208 chunkedCt1Sampled_on_v1StateLocal2Blks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x390 ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x3d0 polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x104 ct1SentEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x144 polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x4a8 ct2SentEncodedLen_local2_pinned_placed_ok_hooks A H
  · exact v1State_bl_blocks_plain blkPC_405_rebase_fetch_0x4e8 polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A H

theorem v1StateEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_405).rebase (blkPl_405).base H)
      (blkPl_405).base
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A (lsρ v1StateJtSymLocal2))) :=
  v1StateEncodedLen_ro_lscl_ok_of_pinned
    (v1StateEncodedLen_local2_pinned_placed_ok_hooks A H)

theorem v1StateEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    V1StateEncodedLenLocal2PinnedPlacedOkExt A ext :=
  v1StateEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem v1StateEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    V1StateEncodedLenLocal2PlacedOkExt A ext :=
  v1StateEncodedLen_ro_lscl_ok_of_pinned
    (v1StateEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem v1StateEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    V1StateEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  v1StateEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem v1StateEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    V1StateEncodedLenLocal2PlacedOk C A ctl abs :=
  v1StateEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## 2. Budget-Threaded `StepInnerStateAt1880Placed`, 4 Chunked1 Dispatch Bridges & Phase 2d -/

private theorem cap_xor_top_eq_of_eq {cap x : BitVec 64}
    (hx : x < 0x8000000000000000#64) (hcap : cap = 0x8000000000000000#64 + x) :
    cap ^^^ 0x8000000000000000#64 = x := by
  bv_bits

/-- Execute the `.rodata` half-word (`↦₁₆ᵣ`) jump-table dispatch at `+1880 .. +1896` (`Block 426`)
from `(blkPl_426).base + 1880#64` to `(blkPl_426).base + off`, preserving `StepInvVm`. -/
macro "step_etv_jump16_to_placed " off:num s1:term:max idx:term:max hx8:term:max : tactic =>
  `(tactic| (
    have _hx8 : ($s1).readReg64 .x8 = $idx := $hx8
    generalize _hro : (blkPl_426).ρ etvJumpTableRoSym = roBase at *
    dsimp only [encodeToVecJumpTableBytesAt]
    apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + BitVec.ofNat 64 $off)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    subst _hro))

/-- Budget-threaded stepping obligation from `(blkPl_426).base + 1880#64` (jump-table dispatch)
to `(blkPl_426).base + 1808#64` (epilogue) for a `V1State.InnerState` value `is`. -/
def StepInnerStateAt1880Placed [LibsignalPlacement] (resStack : Nat)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State)) (s0 : State) (is : V1State.InnerState) : Prop :=
  ∀ (a sp cap ptr : BitVec 64) (g : V1StatePBGhost) (bs : List (BitVec 8)),
    v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 →
    bs.length + (V1State.InnerState.encode is).length ≤ cap.toNat →
    sp &&& 15#64 = 0#64 →
    ∀ {ret : BitVec 64} {s : State} {P F : SepProp}
      {Q Qp : State → SepProp → Prop} {oom : State → SepProp},
      s.pc = (blkPl_426).base + 1880#64 →
      s.status = .Running →
      s.sp = sp - 144#64 →
      s.trace = s0.trace →
      s.readReg64 .x8 =
        (if BitVec.ult (v1StateInnerCap g is ^^^ 0x8000000000000000#64) 11#64
         then v1StateInnerCap g is ^^^ 0x8000000000000000#64 else 7#64) →
      s.readReg64 .x9 = (blkPl_426).ρ etvJumpTableRoSym →
      s.readReg64 .x20 = a →
      s.readReg64 .x21 = a + 128#64 →
      s.readReg64 .x28 = v1StateInnerCap g is →
      StepInv s0 s →
      P = (v1StateInnerPBPinnedAt A.repAlloc g (a + 128#64) is ∗
        ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
        vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F →
      (∀ sm : State,
        sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running →
        sm.sp = sp - 144#64 → sm.trace = s0.trace →
        sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
        StepInv s0 sm →
        SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
          ((v1StateInnerPBPinnedAt A.repAlloc g (a + 128#64) is ∗
            ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ V1State.InnerState.encode is) ∗
            A.pool lim st sm ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom) →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom

theorem step_encodeToVec_v1_ct1Sampled_at_1880_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {s0 : State}
    (hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 407)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A.repAlloc) chunkedCt1SampledPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.Ct1Sampled) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.ct1Sampled v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  simp only [v1StateInnerPBPinnedAt, v1StateInnerCap] at hx8 hx28 ⊢
  refine sepWPp_extract_pure
    (((optCt1SentCap g.b.gCt1Sampled.uc v.uc ^^^ 0x8000000000000000#64).ult 11#64) = false)
    (fun R' hm => by
      dsimp only [chunkedCt1SampledPBPinnedAt] at hm
      rw [optCt1SentPBPinnedAt_eq A.repAlloc g.b.gCt1Sampled.uc (a + 128#64) v.uc] at hm
      have hm' : s.mem ⊨ optCt1SentRest A.repAlloc g.b.gCt1Sampled.uc (a + 128#64) v.uc ∗
          (((a + 128#64) ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc) ∗
           optPolynomialEncoderPBPinnedAt A.repAlloc g.b.gCt1Sampled.sendingCt1 (a + 128#64 + 128#64) v.sendingCt1 ∗
           optPolynomialDecoderPBPinnedAt A.repAlloc g.b.gCt1Sampled.receivingEk (a + 128#64 + 184#64) v.receivingEk ∗
           ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
           vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
           stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        convert hm using 1; sep_ac_rfl
      exact (optCt1SentRest_disc_bounds hm').2.2)
    fun hult => ?_
  simp only [hult, Bool.false_eq_true, ↓reduceIte] at hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2620 s 7#64 hx8
  intro hinv1
  refine step_encodeToVec_v1_ct1Sampled_placed hres A lim st H
    hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec
    a sp cap ptr g.b.gCt1Sampled v bs hv_len hfit halign
    (F := encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_ekSentCt1Received_at_1880_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {s0 : State}
    (hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.EkSentCt1Received) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.ekSentCt1Received v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 4#64 := by
    rw [hx8, show v1StateInnerCap g (.ekSentCt1Received v) = 0x8000000000000004#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000004#64) (x := 4#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 1976 s 4#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240]
  refine step_encodeToVec_v1_ekSentCt1Received_placed hres A lim st H
    hekLen hpolyDecLen hvarint hekEnc hpolyDec
    a sp cap ptr g.a.gEkSentCt1Received v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000004#64) ∗
      memRegion (a + 128#64 + 152#64) 72 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_ct1Acknowledged_at_1880_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {s0 : State}
    (hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen)))
    (hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hct1SentEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 319)
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)))
    (hpolyDec : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 315)
      (withStepInv s0 (etvPolyDecoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.Ct1Acknowledged) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.ct1Acknowledged v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 9#64 := by
    rw [hx8, show v1StateInnerCap g (.ct1Acknowledged v) = 0x8000000000000009#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000009#64) (x := 9#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2076 s 9#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h264 : (a + 128#64) + 136#64 = a + 264#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h264]
  refine step_encodeToVec_v1_ct1Acknowledged_placed hres A lim st H
    hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec
    a sp cap ptr g.b.gCt1Acknowledged v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000009#64) ∗
      memRegion (a + 128#64 + 176#64) 48 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h264, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_encodeToVec_v1_ct1Received_at_1880_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {s0 : State}
    (hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)))
    (hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hekEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 318)
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)))
    (hpolyEnc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 316)
      (withStepInv s0 (etvPolyEncoderBudgetExactSpecOf resStack A lim)))
    (v : V1State.Chunked.Ct1Received) :
    StepInnerStateAt1880Placed resStack A lim st H s0 (.ct1Received v) := by
  intro a sp cap ptr g bs hv_len hfit halign ret s P F Q Qp oom
    hpc hrun hsp htr hx8 hx9 hx20 hx21 hx28 hinv0 hP hnext
  subst hP
  have hx8' : s.readReg64 .x8 = 3#64 := by
    rw [hx8, show v1StateInnerCap g (.ct1Received v) = 0x8000000000000003#64 from rfl,
      cap_xor_top_eq_of_eq (cap := 0x8000000000000003#64) (x := 3#64) (by decide) rfl]
    decide
  clear hx8
  rw [encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  step_etv_jump16_to_placed 2520 s 3#64 hx8'
  intro hinv1
  have h136 : (a + 128#64) + 8#64 = a + 136#64 := by bv_omega
  have h240 : (a + 128#64) + 112#64 = a + 240#64 := by bv_omega
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240]
  refine step_encodeToVec_v1_ct1Received_placed hres A lim st H
    hekLen hpolyEncLen hvarint hekEnc hpolyEnc
    a sp cap ptr g.a.gCt1Received v bs hv_len hfit halign
    (F := ((a + 128#64) ↦₆₄ 0x8000000000000003#64) ∗
      memRegion (a + 128#64 + 168#64) 56 ∗
      encodeToVecJumpTableBytesAt ((blkPl_426).ρ etvJumpTableRoSym) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
    (by dsimp only [encodeToVecJumpTableBytesAt]; rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
  simp only [arm64_norm] at hx27m hfpm
  refine SepWPp.weaken_pre ?_
    (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
  dsimp only [v1StateInnerPBPinnedAt]
  rw [h136, h240, encodeToVecJumpTableBytes_eq ((blkPl_426).ρ etvJumpTableRoSym)]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Step `+1740 .. +1808` (`Block 426`): encodes `st_pb.inner` into
`vecU8At A.repAlloc (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st_pb)) ptr`,
producing `PqRatchetState.encodeRaw st_pb` while threading `A.pool lim st`. -/
theorem step_encodeToVec_phase2d_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    (roV1 : BitVec 64)
    {s0 s : State}
    (hv1Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc roV1)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hInnerAt1880 : ∀ is : V1State.InnerState,
      StepInnerStateAt1880Placed resStack A lim st H s0 is)
    (sret a sp ptr : BitVec 64) (g : PqRatchetStatePBGhost) (st_pb : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st_pb < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a) (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st_pb.inner)
    (hfp : s.readReg64 .fp = sp - 96#64) (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g a st_pb ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
      vecU8At A.repAlloc (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st_pb)) ptr
        (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st_pb.versionNegotiation ++
          encodeOptMessage ChainPB.encodeRaw 2#32 st_pb.chain) ∗
      A.pool lim st s ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running →
      sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = sret → sm.readReg64 .fp = sp - 96#64 → StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g a st_pb ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
          vecU8At A.repAlloc (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st_pb)) ptr
            (PqRatchetState.encodeRaw st_pb) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st_pb)
  let bs0 := encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st_pb.versionNegotiation ++
    encodeOptMessage ChainPB.encodeRaw 2#32 st_pb.chain
  have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st_pb := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases hin : st_pb.inner with
  | none =>
    rw [hin] at hx28
    refine step_encodeToVec_inner_none_pool_placed A lim st H sp
      (F := pqRatchetStatePBPinnedAt A.repAlloc g a st_pb ∗
        (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
        ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
        vecU8At A.repAlloc (sp - 120#64) cap ptr bs0 ∗
        stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
      hpc hrun hsp htr hx28 hinv0 (by dsimp only [cap, bs0]; sep_ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hx27m hfpm hinv_m
    rw [hx27] at hx27m; rw [hfp] at hfpm
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm hx27m hfpm hinv_m)
    have henc : PqRatchetState.encodeRaw st_pb = bs0 := by
      unfold PqRatchetState.encodeRaw
      rw [hin]; simp only [bs0, List.append_nil]
    rw [henc]
    dsimp only [cap, bs0]
    exact Entails.of_eq (by sep_ac_rfl)
  | some inner =>
    cases inner with
    | v1 v1 =>
      rw [hin] at hx28
      have ⟨hv1_len64, _, _⟩ := v1StatePBEncodedLen_lt_of_state hin hlen
      have hv1_all : bs0.length + (PqRatchetState.Inner.encode (.v1 v1)).length ≤ cap.toNat := by
        rw [hcap_toNat, ← pqRatchetStatePBEncodedLen_eq_proto st_pb]
        unfold PqRatchetState.encodeRaw
        rw [hin]; simp only [bs0, List.length_append]
        exact Nat.le_refl _
      rw [encodeInner_v1_eq v1] at hv1_all
      simp only [List.length_append, List.length_singleton,
        show (V1State.encodeRaw v1).length = v1StatePBEncodedLen v1 from v1StatePBEncodedLen_eq_proto v1] at hv1_all
      let F_outer : SepProp :=
        optVersionNegotiationPBPinnedAt A.repAlloc g.vn a st_pb.versionNegotiation ∗
          optChainPBPinnedAt A.repAlloc g.chain (a + 48#64) st_pb.chain ∗
          ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗ F
      refine step_encodeToVec_inner_some_hdr_placed hres A lim st H hv1Len hvarint
        a sp cap ptr g.inner v1 bs0 hv1_len64 (by omega) halign
        (F := F_outer)
        hpc hrun hsp htr hx20 hx21 hx28 hinv0
        (by unfold pqRatchetStatePBPinnedAt; rw [hin]; dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs0, F_outer]; sep_ac_rfl) ?_
      intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_20 hs1_21 hs1_27 hs1_28 hs1_fp hinv_s1
      rw [hx27] at hs1_27; rw [hfp] at hs1_fp
      let bs_hdr := (bs0 ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))
      cases his : v1.innerState with
      | none =>
        have hx28_none : s1.readReg64 .x28 = noneCap2 := by
          rw [hs1_28]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine step_encodeToVec_inner_v1_none_pool_placed A lim st H sp
          (F := v1StatePBPinnedAt A.repAlloc g.inner (a + 128#64) v1 ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs_hdr ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F_outer)
          hpcs1 hruns1 hsps1 htrs1 hx28_none hinv_s1
          (by dsimp only [bs_hdr]; sep_ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hm27 hmfp hinv_m
        rw [hs1_27] at hm27; rw [hs1_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm27 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st_pb = bs_hdr := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [List.append_nil, bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin]
        dsimp only [optPqRatchetInnerPBPinnedAt, cap, bs_hdr, F_outer]
        exact Entails.of_eq (by sep_ac_rfl)
      | some is =>
        have hx28_some : s1.readReg64 .x28 = v1StateInnerCap g.inner is := by
          rw [hs1_28]; dsimp only [optPqRatchetInnerCap]; rw [his]
        refine sepWPp_extract_pure
          ((v1StateInnerCap g.inner is + 2#64 == 0#64) = false ∧
            (v1StateInnerCap g.inner is + 2#64 != 0#64) = true)
          (fun R' hm => by
            dsimp only [v1StatePBPinnedAt] at hm
            rw [his] at hm
            dsimp only at hm
            have hm' : s1.mem ⊨ v1StateInnerPBPinnedAt A.repAlloc g.inner (a + 128#64) is ∗
                ((roV1 ↦ᵣ v1StateJumpTableBytes) ∗
                 vecU8At A.repAlloc (sp - 120#64) cap ptr bs_hdr ∗ A.pool lim st s1 ∗
                 stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F_outer ∗ R') := by
              convert hm using 1; dsimp only [bs_hdr]; sep_ac_rfl
            exact v1StateInnerCap_add_two_bounds hm')
          fun ⟨hw_beq2, hw_bne2⟩ => ?_
        refine step_encodeToVec_inner_to_1880_pool_placed A lim st H rfl sp
          (v1StateInnerCap g.inner is) hw_beq2 hw_bne2
          (F := v1StatePBPinnedAt A.repAlloc g.inner (a + 128#64) v1 ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
            vecU8At A.repAlloc (sp - 120#64) cap ptr bs_hdr ∗
            stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F_outer)
          hpcs1 hruns1 hsps1 htrs1 hx28_some hinv_s1
          (by dsimp only [bs_hdr]; sep_ac_rfl) ?_
        intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_20 hs2_21 hs2_27 hs2_28 hs2_fp hinv_s2
        rw [hs1_20] at hs2_20; rw [hs1_21] at hs2_21; rw [hs1_27] at hs2_27; rw [hs1_fp] at hs2_fp
        have hv_len64' : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64 := by
          have : v1 = ⟨some is⟩ := by cases v1; subst his; rfl
          rw [← this]; exact hv1_len64
        have his_fit : bs_hdr.length + (V1State.InnerState.encode is).length ≤ cap.toNat := by
          have hlen_is : (V1State.InnerState.encode is).length = v1StatePBEncodedLen v1 := by
            rw [← v1StatePBEncodedLen_eq_proto v1]
            dsimp only [V1State.encodedLen, V1State.encodeRaw]; rw [his]
          simp only [bs_hdr, List.length_append, List.length_singleton, hlen_is]
          omega
        refine hInnerAt1880 is a sp cap ptr g.inner bs_hdr hv_len64' his_fit halign
          hpcs2 hruns2 hsps2 htrs2 hs2_8 hs2_9 hs2_20 hs2_21 hs2_28 hinv_s2
          (F := optVersionNegotiationPBPinnedAt A.repAlloc g.vn a st_pb.versionNegotiation ∗
            optChainPBPinnedAt A.repAlloc g.chain (a + 48#64) st_pb.chain ∗
            (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F)
          (by dsimp only [v1StatePBPinnedAt, bs_hdr, F_outer]; rw [his]; dsimp only; sep_ac_rfl) ?_
        intro sm hpcm hrunm hspm htrm hm27 hmfp hinv_m
        rw [hs2_27] at hm27; rw [hs2_fp] at hmfp
        refine SepWPp.weaken_pre ?_
          (hnext sm hpcm hrunm hspm htrm hm27 hmfp hinv_m)
        have henc : PqRatchetState.encodeRaw st_pb = bs_hdr ++ V1State.InnerState.encode is := by
          unfold PqRatchetState.encodeRaw
          rw [hin]; dsimp only
          rw [encodeInner_v1_eq v1]
          dsimp only [V1State.encodeRaw]
          rw [his]
          simp only [bs0, bs_hdr, List.append_assoc]
        rw [henc]
        unfold pqRatchetStatePBPinnedAt
        rw [hin]
        dsimp only [optPqRatchetInnerPBPinnedAt, v1StatePBPinnedAt, cap]
        rw [his]
        exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlacedBudgetAux
