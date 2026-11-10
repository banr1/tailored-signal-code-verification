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
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetSubHops -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `keepsFs` Callee Contracts and `FdsGe3Closed` Helpers for Arm `R1a`

Lifts `<PublicKey as TryFrom<&[u8]>>::try_from` (Block `211`) and `IdentityKey::decode` (Block `18`)
to `.keepsFs`, and preserves `State.fs` across path-buffer deallocation (`+0x6e0 → +0x6f4`) on
Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAuxFd

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement lsLogFilterAddr ls_subroutine_ok_cl_of_plain
   lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (ls_subroutine_ok_rocl_of_block sepWPp_seq_lscro
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (lsLogOff pkTryFromPlacedSpec pkTryFromResultAt pkTryFromSpec)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (blkLib_eq_211 blkPC_211 blkPl_211)
open CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom
  (badLen_pre_weaken memRegion_40_split_badLen memRegion_40_split_badType
   memRegion_40_split_nil memRegion_40_split_ok nil_pre_weaken pointsToBytes_ok_split
   publicKey_deserialize_badKeyLength publicKey_deserialize_badKeyType
   publicKey_deserialize_nil publicKey_deserialize_ok_of_ge32
   ult_sub_of_ge33 ult_sub_of_lt32)
open CryptoVerification.RecordCodecs.Placed
  (blkLib_eq_18 blkPC_18 blkPl_18 instIsLsBlockProg_18 lsProg_18)
open CryptoVerification.RecordCodecsBinary (identityKeyResultAt)
open CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.Helpers
  (exists_ikKeyChunks_of_length_32 ikKeyChunks_ret_8 ikKeyChunks_sp_87 mask_split_64
   memRegion_48_err_split memRegion_48_ok_split memRegion_sp_88_badLen_post
   memRegion_sp_88_badType_post memRegion_sp_88_nil_post memRegion_sp_88_ok_post
   pkTryFrom_sp_88_badLen pkTryFrom_sp_88_badType pkTryFrom_sp_88_nil pkTryFrom_sp_88_ok
   pointsTo64_zext8_split publicKey_deserialize_cases sevenLo_ret_8 sevenLo_sp_87 sp_88_repack
   spe_badKeyType_post spe_noKeyType_post stackAt_ikDec_split truncate16_zeroExtend32
   truncate8_zeroExtend32 zero_orr_zext8_mask)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall ownedBytes)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Bytes InRunPlaced PanicK r1b_StackBounds runFsp runOom runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
  (r1a_CodeOk r1a_bind_sepWPp_state r1a_pool_setMem_write16 r1a_pool_setMem_write32
   r1a_pool_setMem_write32_2 r1a_pool_setMem_write64 r1a_pool_setMem_write64_2
   r1a_pool_setMem_write64_4 r1a_pool_setMem_write8)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget (pkTryFromPlacedBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  r1a_pool_setMem_write8 r1a_pool_setMem_write16 r1a_pool_setMem_write32
  r1a_pool_setMem_write32_2 r1a_pool_setMem_write64 r1a_pool_setMem_write64_2
  r1a_pool_setMem_write64_4

/-! ## `keepsFs` Proofs for `PublicKey::try_from` and `IdentityKey::decode` -/

section
attribute [local irreducible] VmPreserved

set_option maxHeartbeats 1600000 in
/-- Relocatable `<PublicKey as TryFrom<&[u8]>>::try_from` (Block `211`) preserves both `VmPreserved` and `State.fs`. -/
theorem pkTryFrom_placed_keepsFs_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedBudgetSpec.keepsFs := by
  simp only [Spec.keepsFs, pkTryFromPlacedBudgetSpec, withVmPreserved, pkTryFromPlacedSpec,
    pkTryFromSpec, lsLogOff]
  wp_init g s0
  obtain ⟨ptr, bs, out⟩ := g
  dsimp only at *
  subst h_1 h
  apply sepWP_seg_ls_vm (Q := (blkPC_211).rebase (blkPl_211).base (hooksException H))
    blkLib_eq_211 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip
  rcases bs with _ | ⟨b0, rest⟩
  · have hx1 : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using h_2
    rw [publicKey_deserialize_nil, pkTryFromResultAt,
      memRegion_40_split_nil (s0.readReg64 (Reg.gpr 8#5))]
    wp_pull_exists
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
    have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
    have hfs : _ = s0.fs := hnsp.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm hfs ⊢
    refine SepWP.weaken_pre
      (nil_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
        lsLogFilterAddr) ?_
    simp only [sepConj_assoc, *]
    wp_done
  · have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
      intro heq; rw [heq] at h_2; simp at h_2
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen : rest.length < 32
      · have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = true :=
          ult_sub_of_lt32 (by simp only [List.length_cons] at h_2; omega)
            (by simp only [List.length_cons] at h_2; omega)
        rw [publicKey_deserialize_badKeyLength rest hlen, pkTryFromResultAt,
          pointsToBytes_cons, memRegion_40_split_badLen (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
        have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
        have hfs : _ = s0.fs := hnsp.2.2.2.2.2.2
        simp only [State.setMem_setMem] at hvm hfs ⊢
        have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (rest.length + 1) := by
          apply BitVec.eq_of_toNat_eq
          simp only [List.length_cons] at h_2
          rw [h_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hx1_eq] at hvm hfs ⊢
        refine SepWP.weaken_pre
          (badLen_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
            (BitVec.ofNat 64 (rest.length + 1)) lsLogFilterAddr rest) ?_
        try simp only [sepConj_assoc, *]
        wp_done
      · have hge32 : 32 ≤ rest.length := by omega
        have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = false :=
          ult_sub_of_ge33 (by simp only [List.length_cons] at h_2; omega)
        obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
          exists_unpack64_of_length_32 (bs := rest.take 32)
            (by simp [List.length_take, Nat.min_eq_left hge32])
        rw [publicKey_deserialize_ok_of_ge32 rest hge32, pkTryFromResultAt]
        simp only [List.Vector.toList_mk, Reg.x8]
        rw [pointsToBytes_ok_split (s0.readReg64 (Reg.gpr 0#5)) hge32,
          hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
          memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        wp_steps
        wp_if hcbz9
        · wp_steps
          refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
          have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
          have hfs : _ = s0.fs := hnsp.2.2.2.2.2.2
          simp only [State.setMem_setMem] at hvm hfs ⊢
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, *]
          wp_done
        · wp_steps
          refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
          have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
          have hfs : _ = s0.fs := hnsp.2.2.2.2.2.2
          simp only [State.setMem_setMem] at hvm hfs ⊢
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, *]
          wp_done
    · rw [publicKey_deserialize_badKeyType rest hb0, pkTryFromResultAt,
        pointsToBytes_cons, memRegion_40_split_badType (s0.readReg64 (Reg.gpr 8#5))]
      wp_pull_exists
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
      have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
      have hfs : _ = s0.fs := hnsp.2.2.2.2.2.2
      simp only [State.setMem_setMem] at hvm hfs ⊢
      try simp only [sepConj_assoc, *]
      wp_done

set_option maxHeartbeats 1200000 in
/-- Relocatable `IdentityKey::decode` (Block `18`) preserves both `VmPreserved` and `State.fs`. -/
theorem identityKey_decode_keepsFs_vm_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base
      (withLsCodeLoaded lsmpl (withVmPreserved (identityKeyDecodeRawSpec A)).keepsFs) := by
  have hcall : subroutine_ok (lsProg_18 H) (lsmpl.base 211)
      (withLsCl lsmpl pkTryFromPlacedBudgetSpec.keepsFs) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_18 H) (pkTryFrom_placed_keepsFs_ok H)
  simp only [withLsCl, Spec.keepsFs, pkTryFromPlacedBudgetSpec, withVmPreserved,
    pkTryFromPlacedSpec, pkTryFromSpec, sepConj_assoc] at hcall
  simp only [withLsCodeLoaded, Spec.keepsFs, withVmPreserved, identityKeyDecodeRawSpec,
    CryptoVerification.RecordCodecsBinary.identityKeyDecodeRawSpec]
  wp_init x s0
  obtain ⟨bytesA, bytes, ret⟩ := x
  dsimp only at *
  subst h_1 h_2
  rcases publicKey_deserialize_cases bytes with
    ⟨pk, hdes, hdec⟩ | ⟨hdes, hdec⟩ | ⟨t, hdes, hdec⟩ | ⟨n, hdes, hdec⟩
  · have hbs32 : pk.bytes.toList.length = 32 := by simp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
      exists_ikKeyChunks_of_length_32 hbs32
    rw [hdec, memRegion_48_ok_split (s0.readReg64 (Reg.gpr 8#5)),
        identityKeyResultAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 8#64),
        ikKeyChunks_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_ok_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl h (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
    have hfs1 : _ = s0.fs := hnsp1.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm1 hfs1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hfs_call : sf.fs = _ := ‹_›
    have hvm_call : VmPreserved _ sf := ‹_›
    have hfs_after_call : sf.fs = s0.fs := hfs_call.trans hfs1
    have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
    rw [hdes, pkTryFrom_sp_88_ok s0.sp pk, hchunks (s0.sp - 87#64), ikKeyChunks_sp_87 s0.sp]
    simp only [sepConj_assoc]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    rw [sevenLo_sp_87 s0.sp]
    wp_steps
    rw [sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    wp_steps
    rw [sp_88_repack s0.sp]
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    have hfs2 : _ = sf.fs := hnsp2.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    have hfs_final : _ = s0.fs := hfs2.trans hfs_after_call
    clear hvm1 hvm_call hvm_after_call hvm2 hfs1 hfs_call hfs_after_call hfs2
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    rw [← sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    try simp only [sepConj_assoc, *]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_noKeyType_post A.repAlloc (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_nil_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl h (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
    have hfs1 : _ = s0.fs := hnsp1.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm1 hfs1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hfs_call : sf.fs = _ := ‹_›
    have hvm_call : VmPreserved _ sf := ‹_›
    have hfs_after_call : sf.fs = s0.fs := hfs_call.trans hfs1
    have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
    rw [hdes, pkTryFrom_sp_88_nil s0.sp]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    have hfs2 : _ = sf.fs := hnsp2.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    have hfs_final : _ = s0.fs := hfs2.trans hfs_after_call
    clear hvm1 hvm_call hvm_after_call hvm2 hfs1 hfs_call hfs_after_call hfs2
    try simp only [sepConj_assoc, *]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_badKeyType_post A.repAlloc (s0.readReg64 (Reg.gpr 8#5)) t]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badType_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl h (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
    have hfs1 : _ = s0.fs := hnsp1.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm1 hfs1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hfs_call : sf.fs = _ := ‹_›
    have hvm_call : VmPreserved _ sf := ‹_›
    have hfs_after_call : sf.fs = s0.fs := hfs_call.trans hfs1
    have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
    rw [hdes, pkTryFrom_sp_88_badType s0.sp t]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    have hfs2 : _ = sf.fs := hnsp2.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    have hfs_final : _ = s0.fs := hfs2.trans hfs_after_call
    clear hvm1 hvm_call hvm_after_call hvm2 hfs1 hfs_call hfs_after_call hfs2
    try rw [zero_orr_zext8_mask]
    rw [pointsTo64_zext8_split (s0.readReg64 (Reg.gpr 8#5)) t]
    try simp only [sepConj_assoc, *]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badLen_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl h (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
    have hfs1 : _ = s0.fs := hnsp1.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm1 hfs1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hfs_call : sf.fs = _ := ‹_›
    have hvm_call : VmPreserved _ sf := ‹_›
    have hfs_after_call : sf.fs = s0.fs := hfs_call.trans hfs1
    have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
    rw [hdes, pkTryFrom_sp_88_badLen s0.sp n]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    have hfs2 : _ = sf.fs := hnsp2.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    have hfs_final : _ = s0.fs := hfs2.trans hfs_after_call
    clear hvm1 hvm_call hvm_after_call hvm2 hfs1 hfs_call hfs_after_call hfs2
    try rw [mask_split_64] at hvm_final hfs_final ⊢
    dsimp only [identityKeyResultAt, speAt] at hvm_final hfs_final ⊢
    try simp only [sepConj_assoc, *]
    wp_done

end

theorem identityKeyDecode_keepsFs_vm_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) {ext : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_18).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (identityKeyDecodeRawSpec A)).keepsFs) := by
  have h18 : subroutine_ok ((blkPC_18).rebase (blkPl_18).base ext) (blkPl_18).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (identityKeyDecodeRawSpec A)).keepsFs) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (identityKey_decode_keepsFs_vm_placed_ok A ext)
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_18).rebase (blkPl_18).base ext) i 18 ext
    hcaller (instIsLsBlockProg_18 ext) (blkPl_18).base _
    h18 _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-! ## `State.fs`-Preserving Path-Buffer Deallocation (`+0x6e0 → +0x6f4`) -/

theorem r1a_free_path_6e0_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets} {g : RunCall} {s0 s : State} {resStack : Nat}
    {pathCap pathPtr : BitVec 64} {pathBs : Bytes} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced A lim H) (hbnd : r1b_StackBounds B resStack)
    (hpanic : PanicK g s0 Qp) (hne : pathCap ≠ 0)
    (hbase : InRunPlaced r1a_CodeOk s0 s 0x6e0)
    (hx1 : s.readReg64 .x1 = pathCap) (hx26 : s.readReg64 (.gpr 26#5) = pathPtr)
    (hk : ∀ sm : State, InRunPlaced r1a_CodeOk s0 sm 0x6f4 →
      sm.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) →
      sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) →
      sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) →
      sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) →
      sm.trace = s.trace → sm.fs = s.fs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm
        (stackAt (runFsp s0) (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents pathCap.toNat 1) st) sm ∗ F)
        Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc pathCap pathPtr (BitVec.ofNat 64 pathBs.length) pathBs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st s ∗ F) Q Qp (runOom s0) := by
  have hpc0 := hbase.pc; have := hbase.spAligned_cur; have hrun0 := hbase.run
  change s.pc = (blkPl_579).base + 1760#64 at hpc0
  apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hbase.inv
  dsimp only [runProgPlaced, lsProg_579]
  (iterate 4 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done (by simp only [lsRustDeallocSymCli, arm64_norm]) (by simp only [arm64_norm, hrun0])
  intro hinv_c; apply r1a_bind_sepWPp_state; intro sc
  have hpoolc : A.pool lim st s = A.pool lim st sc := by simp only [sc, arm64_norm]
  rw [hpoolc]
  refine r1b_call_dealloc_ownedBytes_placed (retOff := 0x6f0) hh hbnd hinv_c
    (by simp only [sc, lsRustDeallocSymCli, arm64_norm])
    (by simp only [sc, arm64_norm, hrun0]) (by simp only [sc, arm64_norm, hbase.sp])
    (by simp only [sc, arm64_norm, hbase.fp])
    (by simp only [sc, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hbase.vregs])
    hbase.spAligned
    (by simp only [sc, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [sc, arm64_norm, hx26]) (by simp only [sc, arm64_norm, hx1]) (by simp only [sc, arm64_norm])
    hne hpanic fun s1 hb1 hcs1 hfs1 htr1 => ?_
  have hx26_1 : s1.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 12#5) := by
    simpa only [sc, arm64_norm] using hcs1.2.2.2.2.2.2.2.1
  have hpc1 := hb1.pc; have := hb1.spAligned_cur; have hrun1 := hb1.run
  change s1.pc = (blkPl_579).base + 1776#64 at hpc1
  apply sepWPp_seq_lscro (mid := runPcPlaced 0x6f4) hb1.inv
  dsimp only [runProgPlaced, lsProg_579]
  (iterate 1 (wp_step; try (conv => arg 3; simp (config := { zeta := false }) only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])))
  apply SepWP.done
    (by simp only [runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd])
    (by simp only [arm64_norm, hrun1])
  intro hinv2; apply r1a_bind_sepWPp_state; intro s2
  have hpool2 :
      A.pool lim (M.stepEvents (rustDeallocEvents pathCap.toNat 1) st) s1 =
        A.pool lim (M.stepEvents (rustDeallocEvents pathCap.toNat 1) st) s2 := by
    simp only [s2, arm64_norm]
  rw [hpool2]
  exact hk s2
    ⟨by simp only [s2, runPcPlaced_eq, arm64_norm, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd],
     by simp only [s2, arm64_norm, hrun1], by simp only [s2, arm64_norm, hb1.sp],
     by simp only [s2, arm64_norm, hb1.fp], hinv2,
     by simp only [s2, calleeSavedVRegs, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg, arm64_norm, hb1.vregs],
     hb1.spAligned⟩
    (by simp only [s2, arm64_norm, hx26_1])
    (by simpa only [s2, sc, arm64_norm] using hcs1.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using hcs1.2.2.2.2.2.2.2.2.2.1)
    (by simpa only [s2, sc, arm64_norm] using htr1)
    (by simpa only [s2, sc, arm64_norm] using hfs1)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAuxFd
