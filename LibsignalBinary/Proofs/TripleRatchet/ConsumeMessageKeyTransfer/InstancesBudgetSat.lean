/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `HookSat`-Parameterized Budget Contracts for `consume_message_key` and `hmac_sha256`

Specializes the `memset`-consuming contracts of `ConsumeMessageKeyTransfer.InstancesBudget`
(Block `24` `RatchetState::consume_message_key` and Block `73` `crypto::hmac_sha256`) from
`H lsMemsetSym = some hookMemset` to `HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState sha256IV)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_114 blkPC_24 blkPC_73 blkPC_114 blkPl_24 blkPl_73 blkPl_114
  extract_withLsCodeLoaded libsignalSessionLib lsBlackBoxU8Sym lsNoAllocShimSym lsProg_114
  lsRustReallocSym lsmpl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  AgreesOutside.write64_self CalleeSaved CallingConventionPreserved_of_calleeSaved Frame
  Frame.update_two_blocks HmacSt Layout.readBytes_writeBytes_eq NfsMemInv NfsRegInv NfsSavedStack
  RW RunsTo RunsTo.lsProg_svc RunsTo.pairStep_114_0x28 TraceEq agreesOutside_nfsPrologueMem
  agreesOutside_toFrame disjointRegions_of_ro_rw keyBlock keyBlock_length lsCompress256Sym
  lsMemcpySym lsSha256IVAddr nfsPlacedFakeB nfsPlacedFakeB_add_iv nfsPrologueMem
  nfsSavedStack_prologue_432 nfsSp nfs_chunk1_placed nfs_chunk2_placed nfs_chunk3_placed
  nfs_chunk4_placed nfs_second_half_placed nfs_sp_add_464_align nfs_sp_add_544_align nfs_sp_align
  nfs_sp_eq_add nfs_ule_65_false readBytes_writeBytes_16_other readBytes_writeBytes_16_self
  rodata_placed_sha256IV slice16 slice16_length write64_oct_zero_eq_writeBytes_64
  write64_quad_288_eq_writeBytes_slice16 writeBytes_key_over_zero64
)
open CryptoVerification.LibsignalTripleRatchet (
  extract_withLsCodeRoLoaded newFromSliceSpec newFromSliceStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (
  isBlock_nfsResult ls_subroutine_ok_transfer ls_subroutine_ok_transfer_of_plain
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (
  stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat (
  hmacCompressOnlyExcHooks hmacCompressOnlyExcHooks_compress runsTo_block_lift_vm_compress_only
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookSatExactMemcpy placed_memcpy_step_of_exact
)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks CmkEnv cmkPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget (cmkPlacedRoSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat (
  consume_message_key_placed_ro_run_of_hooks_sat consume_message_key_placed_ro_run_sat
  hmac_sha256_placed_ok_sat hmac_sha256_placed_ro_ok_sat
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (cmkRawSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

section Placed

variable [LibsignalPlacement]

attribute [local irreducible]
  CryptoVerification.LibsignalSession.cmkDummyImg
  CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptPlacedImg

private theorem subroutine_ok_cro_of_cl_ro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        { spec with pre := fun g s => spec.pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ })) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have ⟨⟨hcl, hro⟩, hp⟩ := extract_withLsCodeRoLoaded hpre
  refine h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcl, ?_⟩
  rw [sepConj_assoc, sepConj_left_comm (spec.pre x s0), satisfies_pure_sepConj]
  exact ⟨hro, hp⟩

/-! ### 1. `RatchetState::consume_message_key` (Block `24`) -/

/-- Budget-threaded relocatable `consume_message_key` contract on Block `24` under
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem cmk_placed_ro_ok_sat {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base
      (cmkPlacedRoSpec F A lim) :=
  consume_message_key_placed_ro_run_of_hooks_sat F A lim H h_bb h_realloc h_mc h_ms h_c256 hA hmm

theorem cmk_placed_ro_ok_of_noop_sat {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base
      (cmkPlacedRoSpec F A lim) :=
  consume_message_key_placed_ro_run_sat F A lim H h_bb h_shim h_realloc h_mc h_ms h_c256 hA hmm

theorem cmk_placed_ro_ok_at_block_sat {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 24) (cmkPlacedRoSpec F A lim) := by
  have htr : subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeLoaded lsmpl (cmkPlacedRoSpec F A lim)) :=
    ls_subroutine_ok_transfer_of_plain
      (cmk_placed_ro_ok_sat F A lim hA hmm h_bb h_realloc h_mc h_ms h_c256) hi
  refine subroutine_ok_outcome_intro fun ⟨x, st_init⟩ R s0 hpc hrun hpre hsp => ?_
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by
    have hp := hpre
    dsimp only [cmkPlacedRoSpec, cmkPlacedSpec] at hp
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    have hp2 := hp.2
    unfold CryptoVerification.LibsignalSession.cmkPlacedSpec at hp2
    exact (extract_withLsCodeLoaded hp2).1
  refine htr.mono_outcome (x, st_init) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

theorem cmk_placed_cro_ok_at_block_sat {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkPlacedSpec F A lim)) := by
  have hbase :=
    cmk_placed_ro_ok_at_block_sat (callerProg := callerProg) F A lim hA hmm h_bb h_realloc
      h_mc h_ms h_c256 hi
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  have ⟨⟨_, hro⟩, hp⟩ := extract_withLsCodeRoLoaded hpre
  refine hbase.mono_outcome g R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [cmkPlacedRoSpec]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hro, hp⟩

private theorem cmkPlacedSpec_pre_eq_raw (F : ShaCompress)
    (A' : CryptoVerification.RustHeap.RustAlloc)
    (x : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost) (s : State) :
    (CryptoVerification.LibsignalSession.cmkPlacedSpec F A').pre x s =
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced F A').pre x s ∗
        ⌜LibsignalCodeLoaded lsmpl s.mem⌝ := by
  dsimp only [CryptoVerification.LibsignalSession.cmkPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced,
    withLsCodeLoaded]
  rw [CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]

private theorem cmkPlacedSpec_post_eq_raw (F : ShaCompress)
    (A' : CryptoVerification.RustHeap.RustAlloc)
    (x : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost) (s0 sf : State) :
    (CryptoVerification.LibsignalSession.cmkPlacedSpec F A').post x s0 sf =
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced
        F A').post x s0 sf := by
  dsimp only [CryptoVerification.LibsignalSession.cmkPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced,
    withLsCodeLoaded]
  rw [CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]

theorem cmk_raw_placed_cro_ok_at_block_sat {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkRawSpecPlaced F A lim CmkEnv)) := by
  have hbase :=
    cmk_placed_ro_ok_at_block_sat (callerProg := callerProg) F A lim hA hmm h_bb h_realloc
      h_mc h_ms h_c256 hi
  refine subroutine_ok_outcome_intro fun ⟨x, st_init⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨⟨hcl, hro⟩, hp⟩ := extract_withLsCodeRoLoaded hpre
  refine hbase.mono_outcome (x, st_init) R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [cmkRawSpecPlaced] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    dsimp only [cmkPlacedRoSpec, cmkPlacedSpec]
    rw [cmkPlacedSpec_pre_eq_raw, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hp.1, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hro, hp.2⟩
  · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [cmkPlacedRoSpec, cmkPlacedSpec, cmkRawSpecPlaced, withLsCodeRoLoaded] at hq ⊢
      simp only [cmkPlacedSpec_post_eq_raw] at hq
      exact hq
    · exact Or.inr (Or.inl ⟨hpan, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/-! ### 2. `crypto::hmac_sha256` (Block `73`) -/

/-- Relocatable `VmPreserved` `crypto::hmac_sha256` contract on Block `73` under
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem hmac_placed_ok_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        (withVmPreserved (CryptoVerification.LibsignalSession.CryptoHmacSha256.hmacPlacedSpec F))) :=
  hmac_sha256_placed_ok_sat F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with
          pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  hmac_sha256_placed_ro_ok_sat F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeLoaded lsmpl
        { hmacSpec F with
          pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  ls_subroutine_ok_transfer (hmac_placed_ro_ok_sat F h_mc h_ms h_c256) hi

theorem hmac_placed_cro_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl
        (withVmPreserved (CryptoVerification.LibsignalSession.hmacSpec F))) :=
  subroutine_ok_cro_of_cl_ro (hmac_placed_ro_ok_at_block_sat F h_mc h_ms h_c256 hi)

/-! ### 3. `<Hmac<Sha256> as KeyInit>::new_from_slice` (Block `114`, `key.length ≤ 64`) -/

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds

omit [LibsignalPlacement] in
private theorem stripS_read64_local (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read64 a = s.mem.read64 a := by
  cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

omit [LibsignalPlacement] in
private theorem stripExecOutside_hmacSt_local {F : ShaState → List (BitVec 8) → ShaState}
    {p : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} {key msg : List (BitVec 8)} :
    HmacSt (ProofLib.stripExecOutside p m) a F key msg ↔ HmacSt m a F key msg := by
  unfold HmacSt
  simp only [stripExecOutside_readBytes, Memory.read64, ProofLib.strip_read8]

private theorem runsTo_114_to_bp_local {X : LibsignalHooks}
    {s : State} {P : State → Prop} (h : RunsTo (lsProg_114 X) s P) :
    RunsTo (libsignalSessionLib.blockProgram lsmpl 114 X) s P := by
  rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)]

private theorem steps_bp_to_114_local {X : LibsignalHooks} {s s' : State}
    (h : Steps (libsignalSessionLib.blockProgram lsmpl 114 X) s s') :
    Steps (lsProg_114 X) s s' := by
  rwa [IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option linter.unnecessarySimpa false in
set_option maxHeartbeats 3200000 in
private theorem nfs_seg0_placed_vm_sat_local
    {H : String → Option (State → State)}
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base)
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key_s0 : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      VmPreserved s₀ s' ∧
      s'.pc = (blkPl_114).base + 476#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key
  generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  refine RunsTo.pairStep_114_0x28 (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  have hreadable_memcpy :
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).Readable
        (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key_s0)
  have hdisj_memcpy :
      (s₀.readReg64 .x2).toNat = 0 ∨
        DisjointRegions (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat
          (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · exact Or.inl h0
    · refine Or.inr ?_
      clear * - hdisj_key_stack hlen; simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢; bv_omega
  refine placed_memcpy_step_of_exact h_memcpy
    (hrun := by simp only [arm64_norm, hstat])
    (hsp := by simp only [State.spAligned, arm64_norm, hal_nfs])
    (hpc := by simp only [arm64_norm, lsMemcpySym])
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key)
    (hrw := hrw_memcpy)
    (hreadable := hreadable_memcpy)
    (hdisj := hdisj_memcpy)
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key)
    rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    simpa using readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h
    exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64)
      [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv nfsPlacedFakeB s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack
    rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := by rw [nfsPlacedFakeB_add_iv]; exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      rw [nfsPlacedFakeB_add_iv]
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := by rw [nfsPlacedFakeB_add_iv]; exact hdisj_iv_stack
    disj_out_stack := hdisj_out_stack
    saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0
    frame := hf_k0
  }
  have hM_final : NfsMemInv nfsPlacedFakeB s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes (nfsSp s₀ + 144#64) 32 =
      (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  refine ⟨?_, by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_, ?_⟩
  · refine ⟨⟨by cases s₀; rfl, by cases s₀; rfl, by cases s₀; rfl⟩,
      by cases s₀; rfl, fun a => ?_, fun _ _ _ => by cases s₀; rfl⟩
    dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact congrFun hM_final.frame.2.1 a
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

private theorem nfs_post_seg0_runsTo_local {F : ShaCompress}
    {X : LibsignalHooks} (h_compress : X lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {s₀ s1 : State}
    (hkey_len : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc1 : s1.pc = (blkPl_114).base + 476#64)
    (hstat1 : s1.status = .Running)
    (hR1 : NfsRegInv nfsPlacedFakeB s₀ s1)
    (hM1 : NfsMemInv nfsPlacedFakeB s₀ s1.mem)
    (hx8_1 : s1.readReg64 .x8 = 0x36#64)
    (hx0_1 : s1.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1_1 : s1.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (hq2_1 : s1.readVReg128 2#5 = s1.mem.read64 (nfsSp s₀ + 152#64) ++ s1.mem.read64 (nfsSp s₀ + 144#64))
    (hq0_1 : s1.readVReg128 0#5 = s1.mem.read64 (nfsSp s₀ + 168#64) ++ s1.mem.read64 (nfsSp s₀ + 160#64))
    (hk0_1 : s1.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0_1 : s1.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16_1 : s1.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (lsProg_114 X) s1 (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  refine (nfs_chunk1_placed hkey_len hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
  rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
  refine (nfs_chunk2_placed hkey_len hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
    (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
  rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
  refine (nfs_chunk3_placed hkey_len hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
    hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
  rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
  refine (nfs_chunk4_placed hkey_len hal hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
    hs0_4 hs16_4 hs32_4 hs48_4).trans fun s5 h5 => ?_
  rcases h5 with ⟨hpc5, hstat5, hR5, hM5, hx0_5, hx1_5, hx2_5, hist5, hblk5, hivsw5⟩
  exact nfs_second_half_placed h_compress hkey_len hal hpc5 hstat5 hR5 hM5 hx0_5 hx1_5 hx2_5 hist5 hblk5 hivsw5

private theorem new_from_slice_placed_ro_vm_ok_plain_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      { withVmPreserved (newFromSliceSpec F) with
        pre := fun g s =>
          (withVmPreserved (newFromSliceSpec F)).pre g s ∗
            ⌜LibsignalRoLoaded lsmpl s.mem⌝ } := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withVmPreserved, newFromSliceSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, ⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hread_key : s0.mem.Readable keyA key.length := by
    intro a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hb_key.permNoLazy_rw hsep_key ha)
    exact ⟨by rw [hp]; rfl, hlf⟩
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hx2_len : (s0.readReg64 .x2).toNat = key.length := hx2_nat
  have hal : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  intro hL114
  obtain ⟨s1, hsteps1, htr1, hvregs1,
      ⟨hvm1, hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩,
      hL1⟩ :=
    nfs_seg0_placed_vm_sat_local h_mc hpc hrun (by rw [hx2_len]; exact hkey_len) hiv_eq
      hread_iv (disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
      (by rw [hx0]; exact hrw_out) hrw_stk
      (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
      (by rw [hx1, hx2_len]; exact hread_key)
      (by rw [hx1, hx2_len]; exact hdisj_key)
      hal hL114
  rw [hx1, hx2_len, hkey_eq] at hk0_1 hs0_1 hs16_1
  let Q114 := libsignalSessionLib.blockProgram lsmpl 114 (hmacCompressOnlyExcHooks F H)
  let kp114 := ProofLib.progKeep Q114
  have hc256Q := hmacCompressOnlyExcHooks_compress F H
  have hL1_bp : (libsignalSessionLib.blockProgram lsmpl 114 H).CodeLoaded s1.mem := by
    rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_114 H)]
  have hnsp0 : nfsSp (ProofLib.stripS kp114 s0) = nfsSp s0 := by cases s0; rfl
  have hm0_114 : (ProofLib.stripS kp114 s0).mem = ProofLib.stripExecOutside kp114 s0.mem := by cases s0; rfl
  have hm1_114 : (ProofLib.stripS kp114 s1).mem = ProofLib.stripExecOutside kp114 s1.mem := by cases s1; rfl
  have hr0_x0 : (ProofLib.stripS kp114 s0).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
  have hR1_strip : NfsRegInv nfsPlacedFakeB (ProofLib.stripS kp114 s0) (ProofLib.stripS kp114 s1) :=
    { sp_eq := by rw [hnsp0]; cases s1; exact hR1.sp_eq
      sp_align := by rw [hnsp0]; exact hR1.sp_align
      x29_eq := by rw [hnsp0]; cases s1; exact hR1.x29_eq
      x19_eq := by rw [hr0_x0]; cases s1; exact hR1.x19_eq
      x20_eq := by cases s1; exact hR1.x20_eq
      x22_eq := by cases s1; exact hR1.x22_eq
      x25_eq := by cases s0; cases s1; exact hR1.x25_eq
      x26_eq := by cases s0; cases s1; exact hR1.x26_eq
      x27_eq := by cases s0; cases s1; exact hR1.x27_eq }
  have hsaved1_strip : NfsSavedStack (ProofLib.stripS kp114 s0) (ProofLib.stripS kp114 s1).mem :=
    { m432 := by rw [hnsp0, stripS_read64_local]; exact hM1.saved.m432
      m464 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m464
      m472 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m472
      m480 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m480
      m496 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m496
      m504 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m504
      m512 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m512
      m520 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m520
      m528 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m528
      m536 := by rw [hnsp0, stripS_read64_local]; cases s0; exact hM1.saved.m536 }
  have hframe1_strip : Frame (ProofLib.stripS kp114 s0).mem (ProofLib.stripS kp114 s1).mem
      [((ProofLib.stripS kp114 s0).readReg64 .x0, 0x98), (nfsSp (ProofLib.stripS kp114 s0), 544)] := by
    rw [hm0_114, hm1_114, hr0_x0, hnsp0]
    exact ⟨fun a hout => by simpa only [ProofLib.strip_read8] using hM1.frame.1 a hout,
      funext fun a => by simp [ProofLib.strip_perm, hvm1.perm_eq a],
      fun a hout => by simpa only [ProofLib.strip_isLazyFree] using hM1.frame.2.2.1 a hout,
      fun a hlf => by
        simpa only [ProofLib.strip_isLazyFree] using
          hM1.frame.2.2.2.1 a (by simpa only [ProofLib.strip_isLazyFree] using hlf),
      fun a han => by
        simpa only [ProofLib.strip_isAnon] using
          hM1.frame.2.2.2.2 a (by simpa only [ProofLib.strip_isAnon] using han)⟩
  have hM1_strip : NfsMemInv nfsPlacedFakeB (ProofLib.stripS kp114 s0) (ProofLib.stripS kp114 s1).mem :=
    { rw_stack := by rw [hm1_114, hnsp0]; exact stripExecOutside_rw kp114 s1.mem _ _ hM1.rw_stack
      rw_out := by rw [hm1_114, hr0_x0]; exact stripExecOutside_rw kp114 s1.mem _ _ hM1.rw_out
      readable_iv := by rw [hm1_114]; exact stripExecOutside_readable kp114 s1.mem _ _ hM1.readable_iv
      iv_bytes := by rw [hm1_114, stripExecOutside_readBytes]; exact hM1.iv_bytes
      disj_iv_stack := by rw [hnsp0]; exact hM1.disj_iv_stack
      disj_out_stack := by rw [hr0_x0, hnsp0]; exact hM1.disj_out_stack
      saved := hsaved1_strip
      frame := hframe1_strip }
  have hrunsP := runsTo_114_to_bp_local (nfs_post_seg0_runsTo_local h_c256 hkey_len hal hpc1 hstat1 hR1 hM1
    hx8_1 hx0_1 hx1_1 hx2_1 hq2_1 hq0_1 hk0_1 hs0_1 hs16_1)
  have hrunsQ := runsTo_114_to_bp_local (nfs_post_seg0_runsTo_local hc256Q hkey_len
    (by cases s0; exact hal) (by cases s1; exact hpc1) (by cases s1; exact hstat1)
    hR1_strip hM1_strip
    (by cases s1; exact hx8_1)
    (by rw [hnsp0]; cases s1; exact hx0_1)
    (by rw [hnsp0]; cases s1; exact hx1_1)
    (by cases s1; exact hx2_1)
    (by rw [hnsp0, stripS_read64_local, stripS_read64_local]; cases s1; exact hq2_1)
    (by rw [hnsp0, stripS_read64_local, stripS_read64_local]; cases s1; exact hq0_1)
    (by rw [hnsp0, hm1_114, stripExecOutside_readBytes]; exact hk0_1)
    (by rw [hnsp0, hm1_114, stripExecOutside_readBytes]; exact hs0_1)
    (by rw [hnsp0, hm1_114, stripExecOutside_readBytes]; exact hs16_1))
  obtain ⟨sf, hsteps_tail_bp, hvm_tail, htr_tail, hvregs_tail, hsf_or⟩ :=
    runsTo_block_lift_vm_compress_only h_c256 blkLib_eq_114 rfl rfl hL1_bp
      hrunsP hrunsQ (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
  have hsteps_tail : Steps (lsProg_114 H) s1 sf := steps_bp_to_114_local hsteps_tail_bp
  have hvm_all : VmPreserved s0 sf := hvm1.trans hvm_tail
  have hsf_post : sf.pc = s0.readReg64 .lr ∧ sf.status = .Running ∧ CalleeSaved s0 sf ∧
      sf.mem.read64 (s0.readReg64 .x0) = 0#64 ∧ HmacSt sf.mem (s0.readReg64 .x0 + 8#64) F key [] ∧
      Frame s0.mem sf.mem [(s0.readReg64 .x0, 0x98), (s0.sp - 544#64, 544)] := by
    rcases hsf_or with hsf_strip | hsf_real
    · rcases hsf_strip with ⟨hpc_f, hstat_f, hcs_f, htag_f, hhmac_f, hframe_f⟩
      have hmf_114 : (ProofLib.stripS kp114 sf).mem = ProofLib.stripExecOutside kp114 sf.mem := by cases sf; rfl
      have hr0_lr : (ProofLib.stripS kp114 s0).readReg64 .lr = s0.readReg64 .lr := by cases s0; rfl
      have hsp_s0 : (ProofLib.stripS kp114 s0).sp = s0.sp := by cases s0; rfl
      rw [hm0_114, hmf_114, hr0_x0, hsp_s0] at hframe_f
      rw [hmf_114, hr0_x0] at hhmac_f
      exact ⟨by rw [hr0_lr] at hpc_f; cases sf; exact hpc_f,
        by cases sf; exact hstat_f,
        ⟨by cases s0; cases sf; exact hcs_f.1,
         fun r hr => by have := hcs_f.2 r hr; cases s0; cases sf; exact this⟩,
        by rw [hr0_x0, stripS_read64_local] at htag_f; exact htag_f,
        stripExecOutside_hmacSt_local.mp hhmac_f,
        unstrip_frame hframe_f hvm_all.perm_eq⟩
    · exact hsf_real
  rcases hsf_post with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨sf, hsteps1.trans hsteps_tail, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee (hvregs_tail.trans hvregs1)⟩⟩
  dsimp only [withVmPreserved, newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm_all, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr_tail.trans htr1, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

/-- `VmPreserved` + `HookSatExactMemcpy` contract for `new_from_slice` (Block `114`,
`key.length ≤ 64`, `0` `memset` calls). -/
theorem new_from_slice_placed_ro_vm_ok_sat (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      (withLsCodeLoaded lsmpl
        { withVmPreserved (newFromSliceSpec F) with
          pre := fun g s =>
            (withVmPreserved (newFromSliceSpec F)).pre g s ∗
              ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  subroutine_ok_withLsCodeLoaded_of_plain (new_from_slice_placed_ro_vm_ok_plain_sat F h_mc h_c256)

/-- Cross-block transfer of `new_from_slice_placed_ro_vm_ok_sat` to any `callerProg` (block `i`). -/
theorem new_from_slice_placed_ro_vm_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeLoaded lsmpl
        { withVmPreserved (newFromSliceSpec F) with
          pre := fun g s =>
            (withVmPreserved (newFromSliceSpec F)).pre g s ∗
              ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  ls_subroutine_ok_transfer (new_from_slice_placed_ro_vm_ok_sat F h_mc h_c256) hi

/-- Cross-block `withLsCodeRoLoaded lsmpl (withVmPreserved (newFromSliceSpec F))` form of
`new_from_slice_placed_ro_vm_ok_at_block_sat` (consumed by `ComputeBudget`, `DeriveBudget`, and
`ResponderCore.CryptoCalleesPlacedBudget*`). -/
theorem new_from_slice_placed_cro_budget_ok_at_block_sat {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (newFromSliceSpec F))) :=
  subroutine_ok_cro_of_cl_ro (new_from_slice_placed_ro_vm_ok_at_block_sat F h_mc h_c256 hi)

end Placed

end LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
