/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.WP.Apply
public import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import Init.Data.String.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Helpers and VM-Preserving `IdentityKey::decode` for Budget-Threaded Arm `R1a`

Proves VM-preserving `identityKeyDecode_vm_placed_ok` (Block `18`) and provides pool-preserving
`setMem` rewrites, `.rodata` string witnesses, and post-dispatch error sub-hops on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement ls_subroutine_ok_cl_of_plain lsmpl lsroCheck
   lsro_intro_chk lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded NoFsEv TraceFsSound ls_subroutine_ok_rocl_of_block sepWPp_seq_lscro
   subroutine_ok_withLsCodeRoLoaded_of_plain subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack pkTryFromPlacedSpec pkTryFromSpec)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost protocolAddressAt speAt speWord uuidTryParse)
open CryptoVerification.RecordCodecs (decodeIdentityKey)
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
open CryptoVerification.RustHeap
  (LayoutOk RustAlloc allocFailedEvent allocFailedIn vecHeader vecU8 vecU8At)
open CryptoVerification.SignalSession
  (Inputs lsReadFileSym lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV CallW RunCall callAt cliIo cliWrOk inputOf ownedBytes parseArgs
   pointsToBytes_to_memRegion runResAt runResSize storesAt)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (entails_pure_elim_left entails_pure_intro_left ownedBytes_pure ownedBytes_to_dealloc)
open CryptoVerification.SignalSession.Cli.Path.Helpers (memRegion_1_eq_pointsTo8)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_553)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtInit1Placed AtRejectPlaced AtRunEntryPlaced Bytes InRunPlaced Init1Data
   MeAtDispatch PanicK RejectKind RunHistOk RunNeeds RunSem Words32Eq addrNameHeap addrUpperAt
   bundleFile bundlePath exceptOpt init1Cells
   protocolAddressAt_eq_parts r1b_StackBounds readBundleV rejectMem runAns runFiles runFsp
   runLocalBytes runLocals runLocalsFrom runOom runPanicProp runPcPlaced runPcPlaced_eq
   runProgPlaced runSaved)
open CryptoVerification.SignalSession.Cli.RunDrop (PlainSpeTag SpeOwned speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_panicAt_of_cliPanic)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudgetAux
  (r0_utf8_eq_flatMap_rp)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed r1b_call_dropSpeOwned_placed r1b_stackBounds_of_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (callAt_atState storesAt_opened_atState)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
  (pkTryFromPlacedBudgetSpec pkTryFrom_placed_ok)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pool-Preserving `setMem` Rewrites and `FreeOnlyEvs` Helpers -/

@[local simp, local arm64_norm, local wp_norm]
theorem r1a_pool_setMem_write8 {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (v : BitVec 8) :
    A.pool lim st (s.setMem (s.mem.write8 a v)) = A.pool lim st s :=
  A.pool_setMem_write8 lim st s a v

@[local simp, local arm64_norm, local wp_norm]
theorem r1a_pool_setMem_write16 {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (v : BitVec 16) :
    A.pool lim st (s.setMem (s.mem.write16 a v)) = A.pool lim st s :=
  A.pool_setMem_write16 lim st s a v

@[local simp, local arm64_norm, local wp_norm]
theorem r1a_pool_setMem_write32 {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (v : BitVec 32) :
    A.pool lim st (s.setMem (s.mem.write32 a v)) = A.pool lim st s :=
  A.pool_setMem_write32 lim st s a v

@[local simp, local arm64_norm, local wp_norm]
theorem r1a_pool_setMem_write32_2 {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a1 : BitVec 64) (v1 : BitVec 32) (a2 : BitVec 64) (v2 : BitVec 32) :
    A.pool lim st (s.setMem ((s.mem.write32 a1 v1).write32 a2 v2)) = A.pool lim st s :=
  A.pool_setMem_of_perm lim st s _ (by simp [Memory.perm_write32])

@[local simp, local arm64_norm, local wp_norm]
theorem r1a_pool_setMem_write64 {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a v : BitVec 64) :
    A.pool lim st (s.setMem (s.mem.write64 a v)) = A.pool lim st s :=
  A.pool_setMem_write64 lim st s a v

@[local simp, local arm64_norm, local wp_norm]
theorem r1a_pool_setMem_write64_2 {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a1 v1 a2 v2 : BitVec 64) :
    A.pool lim st (s.setMem ((s.mem.write64 a1 v1).write64 a2 v2)) = A.pool lim st s :=
  A.pool_setMem_of_perm lim st s _ (by simp [Memory.perm_write64])

@[local simp, local arm64_norm, local wp_norm]
theorem r1a_pool_setMem_write64_4 {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a1 v1 a2 v2 a3 v3 a4 v4 : BitVec 64) :
    A.pool lim st
      (s.setMem ((((s.mem.write64 a1 v1).write64 a2 v2).write64 a3 v3).write64 a4 v4)) =
      A.pool lim st s :=
  A.pool_setMem_of_perm lim st s _ (by simp [Memory.perm_write64])

theorem r1a_freeOnly_append {evs₁ evs₂ : List AllocEvent}
    (h₁ : FreeOnlyEvs evs₁) (h₂ : FreeOnlyEvs evs₂) :
    FreeOnlyEvs (evs₁ ++ evs₂) := by
  intro ev hmem
  rcases List.mem_append.mp hmem with hm | hm
  · exact h₁ ev hm
  · exact h₂ ev hm

/-! ## VM-Preserving `IdentityKey::decode` (Block `18`) -/

section
attribute [local irreducible] VmPreserved

set_option maxHeartbeats 1200000 in
/-- Relocatable `IdentityKey::decode` (Block `18`) preserves VM state (`withVmPreserved`). -/
theorem identityKey_decode_vm_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base
      (withLsCodeLoaded lsmpl
        (withVmPreserved (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.identityKeyDecodeRawSpec A))) := by
  have hcall : subroutine_ok (lsProg_18 H) (lsmpl.base 211)
      (withLsCl lsmpl pkTryFromPlacedBudgetSpec) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_18 H) (pkTryFrom_placed_ok H)
  simp only [withLsCl, pkTryFromPlacedBudgetSpec, withVmPreserved, pkTryFromPlacedSpec,
    pkTryFromSpec, sepConj_assoc] at hcall
  simp only [withLsCodeLoaded, withVmPreserved,
    LibsignalBinary.Proofs.RecordCodecs.DepsBudget.identityKeyDecodeRawSpec,
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
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hvm_call : VmPreserved _ sf := ‹_›
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
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    clear hvm1 hvm_call hvm_after_call hvm2
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
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hvm_call : VmPreserved _ sf := ‹_›
    have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
    rw [hdes, pkTryFrom_sp_88_nil s0.sp]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    clear hvm1 hvm_call hvm_after_call hvm2
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
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hvm_call : VmPreserved _ sf := ‹_›
    have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
    rw [hdes, pkTryFrom_sp_88_badType s0.sp t]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    clear hvm1 hvm_call hvm_after_call hvm2
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
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro hcl_call
    wp_apply
    have hvm_call : VmPreserved _ sf := ‹_›
    have hvm_after_call : VmPreserved s0 sf := hvm1.trans hvm_call
    rw [hdes, pkTryFrom_sp_88_badLen s0.sp n]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved sf _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    clear hvm1 hvm_call hvm_after_call hvm2
    try rw [mask_split_64] at hvm_final ⊢
    dsimp only [identityKeyResultAt, speAt] at hvm_final ⊢
    try simp only [sepConj_assoc, *]
    wp_done

end

theorem identityKeyDecode_vm_placed_ok [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) {ext : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i ext]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_18).base
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.identityKeyDecodeRawSpec A))) := by
  have h18 : subroutine_ok ((blkPC_18).rebase (blkPl_18).base ext) (blkPl_18).base
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (LibsignalBinary.Proofs.RecordCodecs.DepsBudget.identityKeyDecodeRawSpec A))) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (identityKey_decode_vm_placed_ok A ext)
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_18).rebase (blkPl_18).base ext) i 18 ext
    hcaller (instIsLsBlockProg_18 ext) (blkPl_18).base _
    h18 _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

/-! ## `.rodata` Literals, Pure Semantics, and Frame Helpers -/

abbrev r1a_CodeOk [LibsignalPlacement] : Memory → Prop := LibsignalCodeRoLoaded lsmpl

def r1a_idKeySym : String := "libsignal_cli:.rodata..Lanon.50"
def r1a_unreadSym : String := "libsignal_cli:.rodata..Lanon.65"
def r1a_herrSym : String := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

theorem r1a_utf8_idkey :
    utf8 "identity-key" =
      [0x69#8, 0x64#8, 0x65#8, 0x6e#8, 0x74#8, 0x69#8, 0x74#8, 0x79#8,
       0x2d#8, 0x6b#8, 0x65#8, 0x79#8] := by
  rw [r0_utf8_eq_flatMap_rp]; rfl

theorem r1a_utf8_idkey_len : (utf8 "identity-key").length = 12 := by
  rw [r1a_utf8_idkey]; rfl

theorem r1a_utf8_unreadable :
    utf8 "file could not be read" =
      [0x66#8, 0x69#8, 0x6c#8, 0x65#8, 0x20#8, 0x63#8, 0x6f#8, 0x75#8,
       0x6c#8, 0x64#8, 0x20#8, 0x6e#8, 0x6f#8, 0x74#8, 0x20#8, 0x62#8,
       0x65#8, 0x20#8, 0x72#8, 0x65#8, 0x61#8, 0x64#8] := by
  rw [r0_utf8_eq_flatMap_rp]; rfl

theorem r1a_utf8_unreadable_len : (utf8 "file could not be read").length = 22 := by
  rw [r1a_utf8_unreadable]; rfl

theorem r1a_rodata_idkey_intro [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hcrl : r1a_CodeOk m) (hm : m ⊨ P) :
    m ⊨ (lsρ r1a_idKeySym ↦ᵣ utf8 "identity-key") ∗ P := by
  have hchk : lsroCheck r1a_idKeySym (utf8 "identity-key") = true := by
    rw [r1a_utf8_idkey, r1a_idKeySym]; decide +kernel
  exact lsro_intro_chk hcrl.2 hchk hm

theorem r1a_rodata_unreadable_intro [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hcrl : r1a_CodeOk m) (hm : m ⊨ P) :
    m ⊨ (lsρ r1a_unreadSym ↦ᵣ utf8 "file could not be read") ∗ P := by
  have hchk : lsroCheck r1a_unreadSym (utf8 "file could not be read") = true := by
    rw [r1a_utf8_unreadable, r1a_unreadSym]; decide +kernel
  exact lsro_intro_chk hcrl.2 hchk hm

theorem r1a_panic_handle_error [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    (runProgPlaced H).externAt? (lsρ r1a_herrSym) = some Rust.panicked :=
  ls_panicAt_of_cliPanic (prog := runProgPlaced H) (i := 579) hh.panics (sym := r1a_herrSym)

theorem r1a_memRegion_zero (p : BitVec 64) (n : Nat) : memRegion p n = memRegion (p + 0#64) n := by
  rw [BitVec.add_zero]

theorem r1a_spAligned_of_fsp {s0 s : State} (hsp : s.sp = runFsp s0) (h0 : s0.spAligned = true) :
    s.spAligned = true := by
  unfold State.spAligned; rw [hsp, runFsp]
  exact ProofLib.spAligned_sub s0.sp runFrame h0 (by decide)

theorem r1a_low64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
theorem r1a_high64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits
theorem r1a_pointsTo64_congr {a x y : BitVec 64} (h : x = y) : (a ↦₆₄ x) = (a ↦₆₄ y) := h ▸ rfl

theorem r1a_idKey_path_bounds [LibsignalPlacement] {S : RunSem} {g : RunCall}
    {peerV : AddrV} {dir : Bytes} {s0 : State}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0) (hc : g.c = .init peerV dir) :
    cliWrOk (dir ++ [0x2f#8] ++ utf8 "identity-key") ∧ dir.length < 2 ^ 32 ∧
      (utf8 "identity-key").length < 2 ^ 32 ∧
      (dir ++ [0x2f#8] ++ utf8 "identity-key").length < 2 ^ 32 := by
  have hwr := he.init_bundlePaths_ok hc "identity-key" (by decide)
  have hlen := hwr.2
  have hidlen := r1a_utf8_idkey_len
  refine ⟨hwr, ?_, by omega, hlen⟩
  simp only [bundlePath, List.length_append, List.length_singleton, hidlen] at hlen
  omega

theorem r1a_reject_of_read_err [LibsignalPlacement] {S : RunSem} {g : RunCall}
    {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost} {s0 s : State}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0)
    (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .init peerV dir)
    (herr : cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .error ()) :
    g.a = some none := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init peerV dir) :=
    hcall ▸ he.parse
  have herr' : cliIo.rd (runFiles g.i) (bundlePath dir "identity-key") = .error () := herr
  have hbf : bundleFile (runFiles g.i) dir "identity-key" = none := by
    unfold bundleFile; rw [herr']; rfl
  have hrb : readBundleV (runFiles g.i) dir peerV.device = none := by simp [readBundleV, hbf]
  rw [he.rel.2.2.2.2.2]; unfold runAns; simp [hparse, hget, hme, hrb]

theorem r1a_reject_of_decode_err [LibsignalPlacement] {S : RunSem} {g : RunCall}
    {peerV : AddrV} {dir ikB : Bytes} {meV : AddrV} {meG : AddrGhost} {s0 s : State}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0)
    (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .init peerV dir)
    (hik : cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB)
    (hdec : exceptOpt (decodeIdentityKey ikB) = none) :
    g.a = some none := by
  rcases hd.ownSem with ⟨ownB, hget, hme⟩
  have hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init peerV dir) :=
    hcall ▸ he.parse
  have hik' : cliIo.rd (runFiles g.i) (bundlePath dir "identity-key") = .ok ikB := hik
  have hbf : bundleFile (runFiles g.i) dir "identity-key" = some ikB := by
    unfold bundleFile; rw [hik']; rfl
  have hrb : readBundleV (runFiles g.i) dir peerV.device = none := by
    simp [readBundleV, hbf, hdec]
  rw [he.rel.2.2.2.2.2]; unfold runAns; simp [hparse, hget, hme, hrb]

theorem r1a_ikOk_sem {F : FsFiles} {dir ikB : Bytes} {idKey : IdentityKey}
    (hik : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB)
    (hdec : decodeIdentityKey ikB = .ok idKey) :
    bundleFile F dir "identity-key" = some ikB ∧ exceptOpt (decodeIdentityKey ikB) = some idKey := by
  have hik' : cliIo.rd F (bundlePath dir "identity-key") = .ok ikB := hik
  exact ⟨by unfold bundleFile; rw [hik']; rfl, by rw [hdec]; rfl⟩

theorem r1a_hist_ans_step {i : Inputs} {g : RunCall} {s0 s1 s2 : State}
    (h : RunHistOk i s0 s1 ∧ g.a = some none)
    (htr : s2.trace = s1.trace) (hfs : s2.fs.files = s1.fs.files) :
    RunHistOk i s0 s2 ∧ g.a = some none :=
  ⟨⟨hfs.trans h.1.1, by simpa [htr] using h.1.2⟩, h.2⟩

theorem r1a_pointsTo32_entails_memRegion (a : BitVec 64) (w : BitVec 32) :
    (a ↦₃₂ w) ⊢ memRegion a 4 := by
  rw [ProofLib.pointsTo32_eq_pointsToBytes]
  exact pointsToBytes_to_memRegion a (unpack32 w)

theorem r1a_pointsTo8_entails_memRegion (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ⊢ memRegion a 1 := by
  rw [memRegion_1_eq_pointsTo8]; exact Entails.sepExists_intro b

theorem r1a_memRegion_exists_bytes (n : Nat) :
    ∀ (p : BitVec 64), n ≤ 2 ^ 63 → memRegion p n ⊢ ∃∗ bs : Bytes, ⌜bs.length = n⌝ ∗ (p ↦ₛ bs) := by
  induction n with
  | zero =>
    intro p _; rw [ProofLib.memRegion_zero]
    exact Entails.sepExists_right [] (Entails.pure_right rfl (Entails.of_eq (pointsToBytes_nil p).symm))
  | succ n ih =>
    intro p hn
    rw [show n + 1 = 1 + n by omega, ProofLib.memRegion_split p 1 n (by omega), memRegion_1_eq_pointsTo8]
    refine Entails.trans (sepConj_mono_right (ih (p + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b0
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
    have hc : (p ↦₈ b0) ∗ ⌜rest.length = n⌝ ∗ ((p + 1#64) ↦ₛ rest) =
        ⌜rest.length = n⌝ ∗ (p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ rest) := by sep_ac_rfl
    rw [hc]; apply Entails.pure_left; intro hlen
    exact Entails.sepExists_right (b0 :: rest)
      (Entails.pure_right (by simp [hlen]; omega) (Entails.of_eq (by rw [pointsToBytes_cons])))

theorem r1a_exists_word64 (bs : Bytes) (hlen : bs.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦₆₄ w) = (a ↦ₛ bs) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at hlen
  have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen); subst hnil
  exact ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0,
    fun a => (ProofLib.pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7).symm⟩

theorem r1a_exists_words32 (bs : Bytes) (hlen : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64, Words32Eq bs w0 w1 w2 w3 := by
  let c0 := bs.take 8; let c1 := (bs.drop 8).take 8
  let c2 := (bs.drop 16).take 8; let c3 := bs.drop 24
  obtain ⟨w0, hw0⟩ := r1a_exists_word64 c0 (by simp [c0, hlen])
  obtain ⟨w1, hw1⟩ := r1a_exists_word64 c1 (by simp [c1, hlen])
  obtain ⟨w2, hw2⟩ := r1a_exists_word64 c2 (by simp [c2, hlen])
  obtain ⟨w3, hw3⟩ := r1a_exists_word64 c3 (by simp [c3, hlen])
  have hbs : bs = c0 ++ (c1 ++ (c2 ++ c3)) := by
    have h1 := (List.take_append_drop 8 bs).symm
    have h2 := (List.take_append_drop 8 (bs.drop 8)).symm
    have h3 := (List.take_append_drop 8 (bs.drop 16)).symm
    simp only [List.drop_drop] at h2 h3; dsimp only [c0, c1, c2, c3]; rw [← h3, ← h2, ← h1]
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  have hc0 : c0.length = 8 := by simp [c0, hlen]
  have hc1 : c1.length = 8 := by simp [c1, hlen]
  have hc2 : c2.length = 8 := by simp [c2, hlen]
  rw [hbs, pointsToBytes_append a c0, hw0 a, hc0,
    pointsToBytes_append (a + BitVec.ofNat 64 8) c1, hw1 (a + 8#64), hc1,
    pointsToBytes_append (a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) c2, hw2 (a + 16#64), hc2]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, hw3 (a + 24#64)]

theorem r1a_addrUpperAt_open (a : BitVec 64) (meG : AddrGhost) :
    addrUpperAt a meG ⊢
      ∃∗ w1 : BitVec 64, ⌜w1.setWidth 8 = meG.device⌝ ∗
        (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ w1) := by
  unfold addrUpperAt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (r1a_memRegion_exists_bytes 7 (a + 9#64) (by decide)))) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
  have hc : (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₈ meG.device) ∗
      ⌜bs.length = 7⌝ ∗ ((a + 9#64) ↦ₛ bs) =
    ⌜bs.length = 7⌝ ∗ (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
      ((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦ₛ bs) := by sep_ac_rfl
  rw [hc]; apply Entails.pure_left; intro hlen
  rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at hlen
  have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen); subst hnil
  let w1 : BitVec 64 := b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ meG.device
  have hw1 : w1.setWidth 8 = meG.device := by dsimp [w1]; bv_bits
  have hcell : ((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7]) =
      ((a + 8#64) ↦₆₄ w1) := by
    have hcons := pointsToBytes_cons (a + 8#64) meG.device [b1, b2, b3, b4, b5, b6, b7]
    have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
    rw [← ha9, ← hcons, ProofLib.pointsToBytes8_eq_pointsTo64]
  refine Entails.sepExists_right w1 (Entails.pure_right hw1 ?_)
  have assocEq : (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₈ meG.device) ∗
      ((a + 9#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7]) =
    (a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗
      (((a + 8#64) ↦₈ meG.device) ∗ ((a + 9#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7])) := by sep_ac_rfl
  rw [assocEq, hcell]; exact Entails.refl _

theorem r1a_addrUpperAt_close (a : BitVec 64) (meG : AddrGhost) (w1 : BitVec 64)
    (hw1 : w1.setWidth 8 = meG.device) :
    ((a ↦₆₄ BitVec.ofNat 64 meG.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ w1)) ⊢ addrUpperAt a meG := by
  unfold addrUpperAt
  have hunp : (unpack64 w1).length = 8 := by simp [unpack64]
  rcases hlist : unpack64 w1 with _ | ⟨b0, tail⟩
  · rw [hlist] at hunp; simp at hunp
  have hb0 : b0 = meG.device := by
    simp only [unpack64] at hlist; injection hlist with hb0_eq _; rw [← hw1, ← hb0_eq]; bv_bits
  subst hb0
  have htl : tail.length = 7 := by rw [hlist] at hunp; simpa using hunp
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  rw [ProofLib.pointsTo64_eq_pointsToBytes (a + 8#64) w1, hlist, pointsToBytes_cons (a + 8#64), ha9]
  exact sepConj_mono_right (sepConj_mono_right (htl ▸ pointsToBytes_to_memRegion (a + 9#64) tail))

def r1a_peerGhostOf (peerV : AddrV) (w : CallW) : AddrGhost :=
  { name := { cap := w.w0, ptr := w.w1, bytes := peerV.name }, device := peerV.device }

theorem r1a_pack_peer (A : RustAlloc) (a : BitVec 64) (peerV : AddrV) (w : CallW) :
    ((a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗
        ownedBytes A w.w0 w.w1 w.w2 peerV.name ∗ ⌜w.w3.setWidth 8 = peerV.device⌝) ⊢
      protocolAddressAt A (r1a_peerGhostOf peerV w) a := by
  rw [protocolAddressAt_eq_parts, ownedBytes_pure A w.w0 w.w1 w.w2 peerV.name]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜w.w2 = BitVec.ofNat 64 peerV.name.length ∧ peerV.name.length ≤ w.w0.toNat ∧
        w.w0.toNat < 2 ^ 63 ∧ w.w1 ≠ 0⌝ ∗
      ⌜w.w3.setWidth 8 = peerV.device⌝ ∗
      ((a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ (((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3)) ∗
        ownedBytes A w.w0 w.w1 w.w2 peerV.name) by sep_ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hw2, _⟩; apply Entails.pure_left; intro hw3
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hup := r1a_addrUpperAt_close (a + 16#64) (r1a_peerGhostOf peerV w) w.w3 hw3
  have hown : addrNameHeap A (r1a_peerGhostOf peerV w) =
      ownedBytes A w.w0 w.w1 (BitVec.ofNat 64 peerV.name.length) peerV.name := by
    unfold addrNameHeap ownedBytes r1a_peerGhostOf; simp only [true_and]
  rw [hw2, ← ha24, hown]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hup))

theorem r1a_call7_to_memRegion56 (a : BitVec 64) (w : CallW) :
    ((a ↦₆₄ w.w0) ∗ ((a + 8#64) ↦₆₄ w.w1) ∗ ((a + 16#64) ↦₆₄ w.w2) ∗ ((a + 24#64) ↦₆₄ w.w3) ∗
      ((a + 32#64) ↦₆₄ w.w4) ∗ ((a + 40#64) ↦₆₄ w.w5) ∗ ((a + 48#64) ↦₆₄ w.w6)) ⊢ memRegion a 56 := by
  have hs : ∀ k, 8 + k ≤ 56 → ∀ p, memRegion p 8 ∗ memRegion (p + 8#64) k = memRegion p (8 + k) :=
    fun k hk p => (ProofLib.memRegion_split p 8 k (by omega)).symm
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))) ?_
  have e40 : memRegion (a + 40#64) 8 ∗ memRegion (a + 48#64) 8 = memRegion (a + 40#64) 16 := by
    simpa [BitVec.add_assoc] using hs 8 (by decide) (a + 40#64)
  have e32 : memRegion (a + 32#64) 8 ∗ memRegion (a + 40#64) 16 = memRegion (a + 32#64) 24 := by
    simpa [BitVec.add_assoc] using hs 16 (by decide) (a + 32#64)
  have e24 : memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 24 = memRegion (a + 24#64) 32 := by
    simpa [BitVec.add_assoc] using hs 24 (by decide) (a + 24#64)
  have e16 : memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 32 = memRegion (a + 16#64) 40 := by
    simpa [BitVec.add_assoc] using hs 32 (by decide) (a + 16#64)
  have e08 : memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 40 = memRegion (a + 8#64) 48 := by
    simpa [BitVec.add_assoc] using hs 40 (by decide) (a + 8#64)
  rw [e40, e32, e24, e16, e08, hs 48 (by decide) a]; exact Entails.refl _

theorem r1a_vec22_withString_intro (A : RustAlloc) (a buf w4 w5 : BitVec 64) (hbuf : buf ≠ 0) :
    ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗
      ((a + 24#64) ↦₆₄ 22#64) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
      A.live buf 22 1 ∗ memRegion buf 22) ⊢
      speOwnedAt A a (.withString 1 (by decide)) := by
  have htail : ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢ memRegion (a + 0x20#64) 16 := by
    have hsplit := (ProofLib.memRegion_split (a + 0x20#64) 8 8 (by decide)).symm
    have ha40 : a + 0x20#64 + 8#64 = a + 40#64 := by bv_omega
    rw [ha40] at hsplit; rw [← hsplit]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
  have hg : ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗
      ((a + 24#64) ↦₆₄ 22#64) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
      A.live buf 22 1 ∗ memRegion buf 22) =
    (((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗ memRegion buf 22 ∗
      ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗
        ((a + 24#64) ↦₆₄ 22#64) ∗ A.live buf 22 1) := by sep_ac_rfl
  rw [hg]
  refine Entails.trans (sepConj_mono htail (sepConj_mono_left (r1a_memRegion_exists_bytes 22 buf (by decide)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
  have hperm : memRegion (a + 0x20#64) 16 ∗ (⌜bs.length = 22⌝ ∗ (buf ↦ₛ bs)) ∗
      ((a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗
        ((a + 24#64) ↦₆₄ 22#64) ∗ A.live buf 22 1) =
    ⌜bs.length = 22⌝ ∗ (a ↦₆₄ speWord 1) ∗
      (((a + 8#64) ↦₆₄ 22#64) ∗ ((a + 16#64) ↦₆₄ buf) ∗ ((a + 24#64) ↦₆₄ 22#64) ∗
        A.live buf 22 1 ∗ (buf ↦ₛ bs)) ∗ memRegion (a + 0x20#64) 16 := by sep_ac_rfl
  rw [hperm]; apply Entails.pure_left; intro hlen; unfold speOwnedAt
  refine sepConj_mono_right (sepConj_mono_left
    (Entails.sepExists_right bs (Entails.sepExists_right 22#64 (Entails.sepExists_right buf ?_))))
  unfold vecU8At vecHeader
  simp only [show ¬(22#64 : BitVec 64) = 0 from by decide, ↓reduceIte, hlen,
    show (22#64 : BitVec 64).toNat = 22 from rfl, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, hbuf⟩ (Entails.refl _)))
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : (a + 8#64) + 16#64 = a + 24#64 := by bv_omega
  rw [ha16, ha24]; sep_ac_rfl

theorem r1a_decode_err_unified (A : RustAlloc) (a : BitVec 64) (ikB : Bytes)
    (hnotOk : ∀ ik, decodeIdentityKey ikB ≠ .ok ik) :
    ∃ i : Nat, PlainSpeTag i ∧ (speWord i + 2#64 == 0#64) = false ∧
      (identityKeyResultAt A a (decodeIdentityKey ikB) ⊢
        (a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40) := by
  rcases publicKey_deserialize_cases ikB with ⟨pk, _, hok⟩ | ⟨_, herr⟩ | ⟨t, _, herr⟩ | ⟨n, _, herr⟩
  · exact False.elim (hnotOk ⟨pk⟩ hok)
  · refine ⟨7, by decide, by decide, ?_⟩; rw [herr]; exact Entails.refl _
  · refine ⟨8, by decide, by decide, ?_⟩; rw [herr]; dsimp only [identityKeyResultAt, speAt]
    have hm : memRegion (a + 8#64) 1 ∗ memRegion (a + 9#64) 39 = memRegion (a + 8#64) 40 := by
      simpa [BitVec.add_assoc] using (ProofLib.memRegion_split (a + 8#64) 1 39 (by decide)).symm
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left (r1a_pointsTo8_entails_memRegion _ _)))
      (Entails.of_eq (by rw [hm]))
  · refine ⟨9, by decide, by decide, ?_⟩; rw [herr]; dsimp only [identityKeyResultAt, speAt]
    have hm : memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 = memRegion (a + 8#64) 40 := by
      simpa [BitVec.add_assoc] using (ProofLib.memRegion_split (a + 8#64) 8 32 (by decide)).symm
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
      (Entails.of_eq (by rw [hm]))

def r1a_localsBound : List (Nat × Nat × SepProp) → Nat
  | [] => runLocalBytes
  | (o, _, _) :: _ => o

def r1a_localsEnd (off : Nat) : List (Nat × Nat × SepProp) → Nat
  | [] => off
  | (o, n, _) :: cs => r1a_localsEnd (o + n) cs

def r1a_localsCtx (fsp : BitVec 64) :
    Nat → List (Nat × Nat × SepProp) → Nat → Nat → List (Nat × Nat × SepProp) → SepProp
  | off, [], o, n, cs₂ =>
      memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ runLocalsFrom fsp (o + n) cs₂
  | off, (o₁, n₁, P₁) :: cs₁, o, n, cs₂ =>
      memRegion (fsp + BitVec.ofNat 64 off) (o₁ - off) ∗ P₁ ∗ r1a_localsCtx fsp (o₁ + n₁) cs₁ o n cs₂

theorem r1a_locals_focus (fsp : BitVec 64) (cs₁ : List (Nat × Nat × SepProp))
    (o n : Nat) (P : SepProp) (cs₂ : List (Nat × Nat × SepProp)) :
    runLocals fsp (cs₁ ++ (o, n, P) :: cs₂) = P ∗ r1a_localsCtx fsp 0 cs₁ o n cs₂ := by
  suffices ∀ off, runLocalsFrom fsp off (cs₁ ++ (o, n, P) :: cs₂) =
      P ∗ r1a_localsCtx fsp off cs₁ o n cs₂ from this 0
  intro off; induction cs₁ generalizing off with
  | nil => simp only [List.nil_append, runLocalsFrom, r1a_localsCtx]; sep_ac_rfl
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, runLocalsFrom, r1a_localsCtx, ih (o₁ + n₁)]; sep_ac_rfl

theorem r1a_localsFrom_carve (fsp : BitVec 64) (off o n : Nat) (cs : List (Nat × Nat × SepProp))
    (hlo : off ≤ o) (hhi : o + n ≤ r1a_localsBound cs) (hbnd : r1a_localsBound cs ≤ runLocalBytes) :
    runLocalsFrom fsp off cs = runLocalsFrom fsp off ((o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs) := by
  have hlb : runLocalBytes = 0x29f0 := rfl
  have hs1 : memRegion (fsp + BitVec.ofNat 64 off) (r1a_localsBound cs - off) =
      memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗
        memRegion (fsp + BitVec.ofNat 64 o) (r1a_localsBound cs - o) := by
    refine ProofLib.memRegion_split' (n := o - off) (k := r1a_localsBound cs - o) (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hs2 : memRegion (fsp + BitVec.ofNat 64 o) (r1a_localsBound cs - o) =
      memRegion (fsp + BitVec.ofNat 64 o) n ∗
        memRegion (fsp + BitVec.ofNat 64 (o + n)) (r1a_localsBound cs - (o + n)) := by
    refine ProofLib.memRegion_split' (n := n) (k := r1a_localsBound cs - (o + n)) (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  cases cs with
  | nil => simp only [r1a_localsBound] at hhi hbnd hs1 hs2; simp only [runLocalsFrom, hs1, hs2]
  | cons c cs' =>
    rcases c with ⟨o', n', P'⟩
    simp only [r1a_localsBound] at hhi hbnd hs1 hs2; simp only [runLocalsFrom, hs1, hs2]; sep_ac_rfl

theorem r1a_locals_carve_region (fsp : BitVec 64) (cs₁ : List (Nat × Nat × SepProp))
    (o n : Nat) (cs₂ : List (Nat × Nat × SepProp))
    (hlo : r1a_localsEnd 0 cs₁ ≤ o := by
      simp +zeta +zetaDelta only [r1a_localsEnd, init1Cells, List.cons_append, List.append_assoc,
        List.nil_append]; omega)
    (hhi : o + n ≤ r1a_localsBound cs₂ := by
      simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc,
        List.nil_append, runLocalBytes]; omega)
    (hbnd : r1a_localsBound cs₂ ≤ runLocalBytes := by
      simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc,
        List.nil_append, runLocalBytes]; omega) :
    runLocals fsp (cs₁ ++ cs₂) =
      runLocals fsp (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) := by
  suffices ∀ off, r1a_localsEnd off cs₁ ≤ o → runLocalsFrom fsp off (cs₁ ++ cs₂) =
      runLocalsFrom fsp off (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) from
    this 0 hlo
  clear hlo; intro off hlo'; induction cs₁ generalizing off with
  | nil => exact r1a_localsFrom_carve fsp off o n cs₂ hlo' hhi hbnd
  | cons c cs₁ ih => rcases c with ⟨o₁, n₁, P₁⟩; simp only [List.cons_append, runLocalsFrom]; rw [ih (o₁ + n₁) hlo']

theorem r1a_locals_drop_mid (fsp : BitVec 64) (cs₁ : List (Nat × Nat × SepProp))
    (o n : Nat) (P : SepProp) (cs₂ : List (Nat × Nat × SepProp))
    (hP : P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n)
    (hlo : r1a_localsEnd 0 cs₁ ≤ o := by
      simp +zeta +zetaDelta only [r1a_localsEnd, init1Cells, List.cons_append, List.append_assoc,
        List.nil_append]; omega)
    (hhi : o + n ≤ r1a_localsBound cs₂ := by
      simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc,
        List.nil_append, runLocalBytes]; omega)
    (hbnd : r1a_localsBound cs₂ ≤ runLocalBytes := by
      simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc,
        List.nil_append, runLocalBytes]; omega) :
    runLocals fsp (cs₁ ++ (o, n, P) :: cs₂) ⊢ runLocals fsp (cs₁ ++ cs₂) := by
  rw [r1a_locals_focus fsp cs₁ o n P cs₂, r1a_locals_carve_region fsp cs₁ o n cs₂ hlo hhi hbnd,
    r1a_locals_focus fsp cs₁ o n (memRegion (fsp + BitVec.ofNat 64 o) n) cs₂]
  exact sepConj_mono_left hP

theorem r1a_locals_drop_head (fsp : BitVec 64) (o n : Nat) (P : SepProp)
    (cs : List (Nat × Nat × SepProp))
    (hP : P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n)
    (hhi : o + n ≤ r1a_localsBound cs := by
      simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc,
        List.nil_append, runLocalBytes]; omega)
    (hbnd : r1a_localsBound cs ≤ runLocalBytes := by
      simp +zeta +zetaDelta only [r1a_localsBound, init1Cells, List.cons_append, List.append_assoc,
        List.nil_append, runLocalBytes]; omega) :
    runLocals fsp ((o, n, P) :: cs) ⊢ runLocals fsp cs :=
  r1a_locals_drop_mid fsp [] o n P cs hP (Nat.zero_le o) hhi hbnd

theorem r1a_ownedBytes_zero {A : RustAlloc} {cap ptr len : BitVec 64} {bs : Bytes} (hz : cap = 0) :
    ownedBytes A cap ptr len bs ⊢ emp := by
  unfold ownedBytes; simp only [hz, ↓reduceIte]
  exact entails_pure_elim_left fun _ => Entails.refl _

theorem r1a_addrNameHeap_zero {A : RustAlloc} {g : AddrGhost} (hz : g.name.cap = 0) :
    addrNameHeap A g ⊢ emp := by
  unfold addrNameHeap; simp only [hz, ↓reduceIte]
  exact entails_pure_elim_left fun _ => Entails.refl _

theorem r1a_addrNameHeap_eq_owned {A : RustAlloc} (g : AddrGhost) :
    addrNameHeap A g = ownedBytes A g.name.cap g.name.ptr (BitVec.ofNat 64 g.name.bytes.length) g.name.bytes := by
  unfold addrNameHeap ownedBytes; simp only [true_and]

theorem r1a_stackAt_split (sp : BitVec 64) {need sub : Nat} (hle : need ≤ sub) (h64 : sub ≤ 2 ^ 64) :
    stackAt sp sub = memRegion (sp - BitVec.ofNat 64 sub) (sub - need) ∗ stackAt sp need := by
  have h1 := ProofLib.stackAt_split_bottom sp need (sub - need) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

theorem r1a_sepWPp_exists_pre {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

theorem r1a_sepWPp_pure_pre {p : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : p → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜p⌝ ∗ P) Q Qp oom := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

abbrev r1a_sepWPp_pure_left := @r1a_sepWPp_pure_pre

theorem r1a_sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P ⊢ P') (hw : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hw R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem r1a_bind_sepWPp_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : let st := s; SepWPp prog ret st P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := h

theorem r1a_false_entails {Q : SepProp} : (⌜False⌝ : SepProp) ⊢ Q := by
  rw [← sepConj_emp (⌜False⌝ : SepProp)]; exact Entails.pure_left False.elim

theorem r1a_memRegion32_eq_words (a : BitVec 64) :
    memRegion a 32 = (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) := by
  apply sepProp_eq_of_entails
  · rw [ProofLib.memRegion_split a 8 24 (by decide),
      ProofLib.memRegion_split (a + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
      Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
    exact Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))
  · refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
      Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 => ?_
    have s1 := (ProofLib.memRegion_split a 8 24 (by decide)).symm
    have s2 := (ProofLib.memRegion_split (a + 8#64) 8 16 (by decide)).symm
    have s3 := (ProofLib.memRegion_split (a + 16#64) 8 8 (by decide)).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3; rw [← s1, ← s2, ← s3]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))

theorem r1a_memRegion48_words (a : BitVec 64) :
    memRegion a 48 ⊢ ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split a 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight,
    sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

theorem r1a_words5_to_memRegion40 (a w1 w2 w3 w4 w5 : BitVec 64) :
    ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢ memRegion (a + 8#64) 40 := by
  have hs : ∀ k, 8 + k ≤ 40 → ∀ p, memRegion p 8 ∗ memRegion (p + 8#64) k = memRegion p (8 + k) :=
    fun k hk p => (ProofLib.memRegion_split p 8 k (by omega)).symm
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))) ?_
  have e32 : memRegion (a + 32#64) 8 ∗ memRegion (a + 40#64) 8 = memRegion (a + 32#64) 16 := by
    simpa [BitVec.add_assoc] using hs 8 (by decide) (a + 32#64)
  have e24 : memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 16 = memRegion (a + 24#64) 24 := by
    simpa [BitVec.add_assoc] using hs 16 (by decide) (a + 24#64)
  have e16 : memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 = memRegion (a + 16#64) 32 := by
    simpa [BitVec.add_assoc] using hs 24 (by decide) (a + 16#64)
  have e08 : memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 = memRegion (a + 8#64) 40 := by
    simpa [BitVec.add_assoc] using hs 32 (by decide) (a + 8#64)
  rw [e32, e24, e16, e08]; exact Entails.refl _

theorem r1a_words6_to_memRegion48 (a d0 d1 d2 d3 d4 d5 : BitVec 64) :
    (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) ∗
      ((a + 32#64) ↦₆₄ d4) ∗ ((a + 40#64) ↦₆₄ d5) ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split a 8 40 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (r1a_words5_to_memRegion40 a d1 d2 d3 d4 d5)

theorem r1a_buf22_reassoc (buf d0 d1 : BitVec 64) :
    ((buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6) ⊢
      ∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) := by
  have h16 := (ProofLib.memRegion_split buf 8 8 (by decide)).symm
  have h22 := (ProofLib.memRegion_split buf 16 6 (by decide)).symm
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion buf d0)
    (sepConj_mono_left (pointsTo64_entails_memRegion (buf + 8#64) d1))) ?_
  rw [← sepConj_assoc, h16, h22, ProofLib.memRegion_split buf 14 8 (by decide),
    ProofLib.memRegion_eight (buf + 14#64), sepExists_sepConj_right]
  exact Entails.refl _

theorem r1a_buf22_merge (buf d2 : BitVec 64) :
    (memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ⊢ memRegion buf 22 := by
  rw [show (22 : Nat) = 14 + 8 from rfl, ProofLib.memRegion_split buf 14 8 (by decide)]
  exact sepConj_mono_right (pointsTo64_entails_memRegion (buf + 14#64) d2)

def r1a_ownedSlack (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem r1a_ownedBytes_expose (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) :
    ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs = (ptr ↦ₛ bs) ∗ r1a_ownedSlack A cap ptr bs := by
  unfold ownedBytes r1a_ownedSlack; simp only [true_and]; by_cases hz : cap = 0
  · simp only [hz, BitVec.toNat_ofNat, Nat.zero_mod, ↓reduceIte, sepConj_emp]
    apply sepProp_eq_of_entails
    · rw [← sepConj_emp ⌜_⌝]; apply Entails.pure_left; rintro ⟨hle, hp⟩
      have hbs := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle); subst hbs
      rw [pointsToBytes_nil, emp_sepConj]; exact Entails.pure_right ⟨Nat.zero_le _, hp⟩ (Entails.refl _)
    · rw [sepConj_comm]; apply Entails.pure_left; rintro ⟨hle, hp⟩
      have hbs := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle); subst hbs
      rw [pointsToBytes_nil, ← sepConj_emp (⌜_⌝ : SepProp)]
      exact Entails.pure_right ⟨Nat.zero_le _, hp⟩ (Entails.refl _)
  · simp only [hz, ↓reduceIte]; sep_ac_rfl

theorem r1a_readFile_post_facts [LibsignalPlacement] {S : RunSem} {g : RunCall}
    {peerV : AddrV} {dir : Bytes} {meV : AddrV} {meG : AddrGhost}
    {s0 s_disp s sm : State} {r : Except Unit Bytes}
    (he : AtRunEntryPlaced r1a_CodeOk S g s0)
    (hd : AtDispatchPlaced r1a_CodeOk g (.some meV meG) s0 s_disp)
    (hcall : g.c = .init peerV dir)
    (hs_tr : s0.trace <+: s.trace) (hs_fs : s.fs.files = runFiles g.i)
    (hs_out : ProcessOutcome.traceStreamBytes .stdout s.trace = [])
    (hfiles_eq : sm.trace = s.trace → sm.fs.files = s.fs.files)
    (hpost : r = cliIo.rd s.fs.files (dir ++ [0x2f#8] ++ utf8 "identity-key") ∧ sm.trace = s.trace) :
    s0.trace <+: sm.trace ∧ (r = .error () → RunHistOk g.i s0 sm ∧ g.a = some none) ∧
      (∀ ikB, r = .ok ikB →
        cliIo.rd (runFiles g.i) (dir ++ [0x2f#8] ++ utf8 "identity-key") = .ok ikB ∧
          sm.fs.files = runFiles g.i ∧ ProcessOutcome.traceStreamBytes .stdout sm.trace = []) := by
  rcases hpost with ⟨hr, htr_eq⟩
  exact ⟨htr_eq ▸ hs_tr,
    fun he0 => ⟨⟨(hfiles_eq htr_eq).trans hs_fs, htr_eq ▸ hs_out⟩,
      r1a_reject_of_read_err he hd hcall (hs_fs ▸ hr.symm.trans he0)⟩,
    fun ikB hik => ⟨hs_fs ▸ hr.symm.trans hik, (hfiles_eq htr_eq).trans hs_fs, htr_eq ▸ hs_out⟩⟩

theorem r1a_call_lscro [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {g : RunCall}
    {target lr : BitVec 64} {spec : Spec α} {x : α}
    {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hFs : TraceFsSound (runProgPlaced H))
    (hok : subroutine_ok (runProgPlaced H) target (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = target) (hrun : s.status = .Running) (hinv : r1a_CodeOk s.mem)
    (hsp : s.spAligned = true) (hpanic : PanicK g s0 Qp)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜runPanicProp g s0 sf⌝ ∗ anyHeap)
    (hexit : ∀ code sf, spec.onExit x code s sf ⊢ ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf ⊢ runOom s0 sf)
    (hk : ∀ sm : State, sm.pc = s.readReg64 .lr → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → r1a_CodeOk sm.mem →
      s.trace <+: sm.trace → (sm.trace = s.trace → sm.fs.files = s.fs.files) →
      SepWPp (runProgPlaced H) lr sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) lr s (spec.pre x s ∗ F) Q Qp (runOom s0) := by
  intro R hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [show (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F ∗ R) =
      ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ ((spec.pre x s ∗ F) ∗ R) by sep_ac_rfl,
      satisfies_pure_sepConj]
    exact ⟨hinv, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hok.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre hsp hL
  obtain ⟨evs, htr_evs, hfiles_evs⟩ := hFs s sm hsteps
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · have hinv_m : r1a_CodeOk sm.mem := hinv.of_keepsFrozen hsteps.keepsFrozen
    have hm_post : sm.mem ⊨ (spec.post x s sm ∗ F) ∗ R := by
      simpa only [withLsCodeRoLoaded, sepConj_assoc] using hpost
    have hfiles_eq : sm.trace = s.trace → sm.fs.files = s.fs.files := fun heq => by
      have hevs : evs = [] := List.append_cancel_left (htr_evs.symm.trans (by simp [heq]))
      subst hevs; exact hfiles_evs NoFsEv.nil
    obtain ⟨sf, hsteps2, hout2⟩ := hk sm hpcm hrunm hspm hcsm hinv_m ⟨evs, htr_evs.symm⟩ hfiles_eq R hm_post (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout2⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic x s sm ∗ F) ∗ R := by
      simpa only [withLsCodeRoLoaded, sepConj_assoc] using hpost
    have hp_sat : sm.mem ⊨ (⌜runPanicProp g s0 sm⌝ ∗ anyHeap) ∗ (F ∗ R) :=
      Satisfies.mono (sepConj_mono_left (hpan sm)) (by simpa only [sepConj_assoc] using hm_pan)
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp_sat
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, spec.onPanic x s sm ∗ F, hm_pan,
      hpanic sm (spec.onPanic x s sm ∗ F) hp_sat.1⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj (Satisfies.mono (sepConj_mono_left (hexit code sm))
      (by simpa only [withLsCodeRoLoaded, sepConj_assoc] using hpost)))
  · dsimp only [withLsCodeRoLoaded] at hpost
    have hm_oom1 : sm.mem ⊨ runOom s0 sm ∗ (F ∗ R) :=
      Satisfies.mono (sepConj_mono_left (hoom sm)) hpost
    dsimp only [runOom] at hm_oom1
    exact False.elim (not_satisfies_false_sepConj hm_oom1)

theorem r1a_call_run [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {g : RunCall}
    {target : BitVec 64} {spec : Spec α} {x : α} {retOff : Nat}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hFs : TraceFsSound (runProgPlaced H))
    (hok : subroutine_ok (runProgPlaced H) target (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = target) (hrun : s.status = .Running) (hinv : r1a_CodeOk s.mem)
    (hsp_eq : s.sp = runFsp s0) (hfp_eq : s.readReg64 .fp = s0.sp - 0x60#64)
    (hv_eq : calleeSavedVRegs s = calleeSavedVRegs s0) (hsp0_al : s0.spAligned = true)
    (hret : s.readReg64 .lr = runPcPlaced retOff) (hpanic : PanicK g s0 Qp)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜runPanicProp g s0 sf⌝ ∗ anyHeap)
    (hexit : ∀ code sf, spec.onExit x code s sf ⊢ ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf ⊢ runOom s0 sf)
    (hk : ∀ sm : State, InRunPlaced r1a_CodeOk s0 sm retOff → CalleeSavedPreserved s sm →
      s.trace <+: sm.trace → (sm.trace = s.trace → sm.fs.files = s.fs.files) →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sm (spec.post x s sm ∗ F) Q Qp (runOom s0)) :
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s P Q Qp (runOom s0) :=
  r1a_sepWPp_weaken_pre hpre
    (r1a_call_lscro hFs hok hpc hrun hinv (r1a_spAligned_of_fsp hsp_eq hsp0_al) hpanic hpan hexit hoom
      fun sm hpcm hrunm hspm hcsm hinvm htr hf =>
        hk sm ⟨hpcm.trans hret, hrunm, hspm.trans hsp_eq,
          hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp_eq, hinvm,
          hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hv_eq, hsp0_al⟩ hcsm htr hf)

/-- Post-dispatch rejection continuation closed under trailing `FreeOnlyEvs` suffixes. -/
def FreeRejK [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (H : LibsignalHooks) (g : RunCall) (s0 : State)
    (resStack : Nat) (Q Qp : State → SepProp → Prop) : Prop :=
  ∀ (s2 : State) (evs : List AllocEvent),
    FreeOnlyEvs evs →
    AtRejectPlaced r1a_CodeOk g StoresGhost.opened .postDispatch s0 s2 →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
      (rejectMem (A.atState lim (M.stepEvents evs st) s2) g StoresGhost.opened .postDispatch s0 resStack)
      Q Qp (runOom s0)

theorem FreeRejK.step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {s0 : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} {evs₁ : List AllocEvent}
    (hf₁ : FreeOnlyEvs evs₁)
    (hrej : FreeRejK A lim st H g s0 resStack Q Qp) :
    FreeRejK A lim (M.stepEvents evs₁ st) H g s0 resStack Q Qp := by
  intro s2 evs₂ hf₂ hat
  have hcomb := hrej s2 (evs₁ ++ evs₂) (r1a_freeOnly_append hf₁ hf₂) hat
  rwa [M.stepEvents_append] at hcomb

theorem FreeRejK.dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {g : RunCall} {s0 : State} {resStack : Nat}
    {Q Qp : State → SepProp → Prop} (sz al : Nat)
    (hrej : FreeRejK A lim st H g s0 resStack Q Qp) :
    FreeRejK A lim (M.stepEvents (rustDeallocEvents sz al) st) H g s0 resStack Q Qp :=
  hrej.step (FreeOnlyEvs.singleton al sz)

theorem r1a_peel_pure_pre {P Q R F : SepProp} (h : Q ⊢ R ∗ F) : P ∗ Q ⊢ (P ∗ R) ∗ F := by
  rw [sepConj_assoc]; exact sepConj_mono_right h
theorem r1a_group2c (a0 a1 c r : SepProp) : a0 ∗ a1 ∗ c ∗ r = ((a0 ∗ a1) ∗ c) ∗ r := by sep_ac_rfl
theorem r1a_group6c (a0 a1 a2 a3 a4 a5 c r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ c ∗ r = ((a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5) ∗ c) ∗ r := by sep_ac_rfl
theorem r1a_group6_4 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 m c r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ b0 ∗ b1 ∗ b2 ∗ b3 ∗ m ∗ c ∗ r =
      ((a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5) ∗ ((b0 ∗ b1 ∗ b2 ∗ b3) ∗ (m ∗ c))) ∗ r := by sep_ac_rfl
theorem r1a_group_ok710 (a0 a1 a2 a3 a4 a5 b0 b1 b2 m0 m1 m2 c r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ b0 ∗ b1 ∗ b2 ∗ m0 ∗ m1 ∗ m2 ∗ c ∗ r =
      (((a0 ∗ (a1 ∗ a2 ∗ a3 ∗ a4) ∗ a5) ∗ (b0 ∗ b1 ∗ b2 ∗ (m0 ∗ m1 ∗ m2 ∗ c)))) ∗ r := by sep_ac_rfl
theorem r1a_group4_7 (a0 a1 a2 a3 c b0 b1 b2 b3 b4 b5 b6 r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ c ∗ b0 ∗ b1 ∗ b2 ∗ b3 ∗ b4 ∗ b5 ∗ b6 ∗ r =
      ((a0 ∗ a1 ∗ a2 ∗ a3) ∗ c) ∗ ((b0 ∗ b1 ∗ b2 ∗ b3 ∗ b4 ∗ b5 ∗ b6) ∗ r) := by sep_ac_rfl
theorem r1a_group_mid2 (m0 m1 a c r : SepProp) : m0 ∗ m1 ∗ a ∗ c ∗ r = m0 ∗ m1 ∗ (a ∗ c) ∗ r := by sep_ac_rfl
theorem r1a_group_mid6 (m0 m1 a0 a1 a2 a3 a4 a5 c r : SepProp) :
    m0 ∗ m1 ∗ a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ c ∗ r =
      m0 ∗ m1 ∗ ((a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5) ∗ c) ∗ r := by sep_ac_rfl
theorem r1a_group_8b0 (m0 m1 l s p w c o0 o1 o2 o3 o4 o5 o6 o7 o8 fh ah : SepProp) :
    m0 ∗ m1 ∗ l ∗ s ∗ p ∗ w ∗ c ∗ o0 ∗ o1 ∗ o2 ∗ o3 ∗ o4 ∗ o5 ∗ o6 ∗ o7 ∗ o8 ∗ fh ∗ ah =
      (m0 ∗ m1) ∗ l ∗ s ∗ p ∗ ((w ∗ c) ∗ o0 ∗ o1 ∗ o2 ∗ o3 ∗ o4 ∗ o5 ∗ o6 ∗ o7 ∗ o8 ∗ fh) ∗ ah := by sep_ac_rfl
theorem r1a_group_5c (a0 a1 a2 a3 a4 r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ r = (a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4) ∗ r := by sep_ac_rfl
theorem r1a_group_11_2 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b0 b1 r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ a7 ∗ a8 ∗ a9 ∗ a10 ∗ b0 ∗ b1 ∗ r =
      (a0 ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ a7 ∗ a8 ∗ a9 ∗ a10) ∗ (b0 ∗ b1) ∗ r := by sep_ac_rfl
theorem r1a_group_6bc (a0 a1 a2 c p i r : SepProp) :
    a0 ∗ a1 ∗ a2 ∗ c ∗ p ∗ i ∗ r = (((a0 ∗ a1 ∗ a2) ∗ c) ∗ p ∗ i) ∗ r := by sep_ac_rfl


end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudgetAux
