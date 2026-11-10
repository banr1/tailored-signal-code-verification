/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
public import LibsignalBinary.Proofs.Placed.GenLsBlockUltra
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp
import ProofLib.SepLogic.WP.Apply
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSliceBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRefBudget

/-!
# Budget-Threaded `[LibsignalPlacement]` Callee Contracts (`PksmCalleesPlaced`)

Allocation-budget (`RustCliAllocBudget M`) and `VmPreserved`-strengthened callee contracts
for `PreKeySignalMessage::try_from` (Block `111`), discharged from `CodecHooksPlaced M A lim H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters hiding
  dropSpeSpec dropSpeSpecX lsRustDeallocSym
open CryptoVerification.LibsignalTripleRatchet.Wire hiding
  TripleRatchetHooksWPlaced TryFromDepsPlaced
open CryptoVerification.RecordCodecsBinary hiding CodecHooksPlaced
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack
  SepWPp SepWPp.pure_pre SepWPp.exists_pre SepWPp.mono_pre
  spAligned_sub608 PreKeyDeallocOk preKeyDeallocOk_of_hookSat
  PreKeyDropSpeOk PreKeyIntoBoxOk PreKeySigTryFromOk PreKeyTryCloneOk
  preKeyDropSpeOk_cro_of_hookSat preKeyIntoBoxOk_of_hooks
  preKeyTryCloneOk_of_hooks preKeySigTryFromOk_cro_of_deps
  deserializeOk33PlacedSpec deserialize_placed_ok
  identityKeyTryFromSliceOkPlacedSpec identityKeyTryFromSlice_placed_ok
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (
  ikErrWords
  ikErrWords_entails_speAt
  subroutine_ok_withLsCodeRoLoaded_of_cl
  subroutine_ok_withLsCodeRoLoaded_of_plain'
  subroutine_ok_withPreKeyInv_of_cro
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (
  hookSat_noAllocShimBudget_of_withVmPreserved
  hookSat_framelessMemcpyBudget_of_withVmPreserved
  portDepsPlaced_of_hooks
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  intoBoxedSliceSpecX tryCloneFromRefSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSliceBudget (
  into_boxed_slice_placed_ok_x
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRefBudget (
  try_clone_from_ref_placed_ok_x
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropSpeSpec dropSpeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget (
  drop_spe_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustDeallocExternSpecWithStack rustDeallocExternWithStack_of_rustDealloc
  decodeErrorFromSpecWithStack decodeErrorPushExternSpecWithStack
  decodeVarintSlowSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  decodeVarintSliceSpecX int32MergeSpecX skipFieldSpecX dropDecodeErrorSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget (
  TripleRatchetHooksWPlaced bytesMergeExactRawSpecX decodeErrorPushBoundedSpecWithStack
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers (
  bytes_merge_exact_placed_ok_x_e4
  pksmDecodeErrorPushBounded_of_codecHooks
  tripleRatchetHooksWPlaced_of_codecHooks_e4
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget (
  TryFromDepsPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget (
  deserializeFull_vm_placed_ok
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget (
  deserializeOk33PlacedSpec
  deserialize_placed_ok
  identityKeyTryFromSliceOkPlacedSpec
  identityKeyTryFromSlice_placed_ok
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (
  PreKeyDeallocOk preKeyDeallocOk_of_hookSat PreKeyDropSpeOk
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget (
  PreKeyIntoBoxOk PreKeySigTryFromOk
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget (
  PreKeyTryCloneOk
  preKeyDropSpeOk_cro_of_hookSat
  preKeyIntoBoxOk_of_hooks
  preKeyTryCloneOk_of_hooks
  preKeySigTryFromOk_cro_of_deps
)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved

/-! ## Section 1: `<IdentityKey as TryFrom<&[u8]>>::try_from` (Block `116`) `VmPreserved` Err Specs -/

export CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (
  subroutine_ok_withLsCodeRoLoaded_of_cl
  subroutine_ok_withLsCodeRoLoaded_of_plain'
  subroutine_ok_withPreKeyInv_of_cro
)

/-- `VmPreserved`-strengthened word-level Err specification of
`<IdentityKey as TryFrom<&[u8]>>::try_from` (Block `116`) under `[LibsignalPlacement]`. -/
def identityKeyTryFromSliceWordsErrPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × SignalProtocolError × BitVec 64) :=
  withVmPreserved
    CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.identityKeyTryFromSliceWordsErrPlacedSpec

/-- `VmPreserved`-strengthened exact `speAt` Err specification of
`<IdentityKey as TryFrom<&[u8]>>::try_from` (Block `116`) under `[LibsignalPlacement]` on a
48-byte sret (`memRegion outPtr 48`). -/
def identityKeyTryFromSliceErrPlacedSpec [LibsignalPlacement] (A : RustAlloc)
    (fn : List (BitVec 8)) :
    Spec (BitVec 64 × List (BitVec 8) × SignalProtocolError × BitVec 64) :=
  withVmPreserved
    (CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.identityKeyTryFromSliceErrPlacedSpec A fn)

private theorem pl_ik_low8_merge (n : BitVec 64) :
    n &&& (-256#64) ||| n &&& 255#64 = n := by
  rw [← BitVec.and_or_distrib_left, show (-256#64 ||| 255#64) = BitVec.allOnes 64 by decide,
    BitVec.and_allOnes]

private theorem pl_memRegion_40_stp (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      memRegion (a + 16#64) 24 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide), ProofLib.memRegion_split (a + 8#64) 8 24 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]

private theorem pl_memRegion_40_ikErr_small (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗ memRegion (sp - 87#64) 7 ∗ memRegion (sp - 80#64) 1 ∗
      memRegion (sp - 79#64) 1 ∗ memRegion (sp - 78#64) 30 := by
  rw [ProofLib.memRegion_split (sp - 88#64) 1 39 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64) 7 32 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64) 1 31 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64) 1 30 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]

private theorem pl_memRegion_40_ikErr_len (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗ memRegion (sp - 87#64) 7 ∗ memRegion (sp - 80#64) 1 ∗
      memRegion (sp - 79#64) 7 ∗ (∃∗ w : BitVec 64, (sp - 72#64) ↦₆₄ w) ∗
      memRegion (sp - 64#64) 16 := by
  rw [ProofLib.memRegion_split (sp - 88#64) 1 39 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64) 7 32 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64) 1 31 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64) 7 24 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64 + 7#64) 8 16 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  rw [ProofLib.memRegion_eight (sp - 72#64)]

private theorem pl_memRegion_31_byte (a : BitVec 64) :
    memRegion a 31 = (∃∗ v : BitVec 8, a ↦₈ v) ∗ memRegion (a + 1#64) 30 := by
  rw [ProofLib.memRegion_split a 1 30 (by decide), ProofLib.memRegion_one]

private theorem pl_cells_12_identityKey_pre (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      memRegion (sp - 48#64) 8 ∗
      memRegion (sp - 40#64) 8 ∗
      (∃∗ w_32 : BitVec 64, (sp - 32#64) ↦₆₄ w_32) ∗
      (∃∗ w_24 : BitVec 64, (sp - 24#64) ↦₆₄ w_24) ∗
      (∃∗ w_16 : BitVec 64, (sp - 16#64) ↦₆₄ w_16) ∗
      memRegion (sp - 8#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    Prost.memRegion_split (sp - 96#64) 8 88 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64) 40 48 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64) 8 40 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  rw [ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64)]

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

set_option maxHeartbeats 3200000 in
/-- Placed `VmPreserved` word-level Err contract of `<IdentityKey as TryFrom<&[u8]>>::try_from`
(Block `116`). -/
theorem identityKeyTryFromSlice_wordsErr_placed [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_116).rebase (blkPl_116).base H)
      (blkPl_116).base
      (withLsCodeLoaded lsmpl identityKeyTryFromSliceWordsErrPlacedSpec) := by
  simp only [withLsCodeLoaded, identityKeyTryFromSliceWordsErrPlacedSpec, withVmPreserved,
    CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.identityKeyTryFromSliceWordsErrPlacedSpec]
  have hpk := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_116).rebase (blkPl_116).base H)
    (entry := lsmpl.base 211)
    (LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.pkTryFrom_placed_ok H)
  simp only [withLsCl,
    LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.pkTryFromPlacedBudgetSpec,
    withVmPreserved, pkTryFromPlacedSpec, pkTryFromSpec] at hpk
  wp_init x s0
  rcases x with ⟨p, bs, e, outPtr⟩
  dsimp only at *
  subst h_2 h_4
  have hstk_eq : stackAt s0.sp 96 = cells (s0.sp - 96#64) 12 := by
    simp only [stackAt]
    exact ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)
  rw [hstk_eq]
  rw (occs := .pos [1]) [pl_cells_12_identityKey_pre s0.sp]
  rw (occs := .pos [1]) [pl_memRegion_40_stp (s0.readReg64 (.gpr 8#5))]
  wp_pull_exists
  apply sepWP_seq_lscl h (mid := lsmpl.base 211)
  apply sepWP_seg_ls_vm (Q := (blkPC_116).rebase (blkPl_116).base (hooksException H))
    blkLib_eq_116 (mid := lsmpl.base 211)
  intro _m_strip1
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 hnsp1 => ?_
  have hvm1 : VmPreserved s0 _ := hnsp1.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_call
  wp_call hpk (s0.readReg64 (.gpr 0#5), bs, s0.sp - 88#64)
  have hvm_call : VmPreserved _ _ := ‹_›
  have hvm_after_call : VmPreserved s0 _ := hvm1.trans hvm_call
  rw [h_1]
  rcases deserialize_error_cases h_1 with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · simp only [pkTryFromResultAt, ikErrWords, speWord, bv_sub_add_lit', BitVec.reduceSub]
    rw [pl_memRegion_31_byte (s0.sp - 79#64)]
    simp only [bv_sub_add_lit', BitVec.reduceSub]
    rw [pl_cells_12_identityKey_pre s0.sp, pl_memRegion_40_ikErr_small s0.sp]
    wp_pull_exists
    apply sepWP_seg_ls_vm (Q := (blkPC_116).rebase (blkPl_116).base (hooksException H))
      blkLib_eq_116 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    clear hvm1 hvm_call hvm_after_call hvm2
    wp_done
  · simp only [pkTryFromResultAt, ikErrWords, speWord, bv_sub_add_lit', BitVec.reduceSub]
    rw [pl_cells_12_identityKey_pre s0.sp, pl_memRegion_40_ikErr_small s0.sp]
    wp_pull_exists
    apply sepWP_seg_ls_vm (Q := (blkPC_116).rebase (blkPl_116).base (hooksException H))
      blkLib_eq_116 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    clear hvm1 hvm_call hvm_after_call hvm2
    wp_done
  · simp only [pkTryFromResultAt, ikErrWords, speWord, bv_sub_add_lit', BitVec.reduceSub]
    rw [pl_cells_12_identityKey_pre s0.sp, pl_memRegion_40_ikErr_len s0.sp]
    wp_pull_exists
    apply sepWP_seg_ls_vm (Q := (blkPC_116).rebase (blkPl_116).base (hooksException H))
      blkLib_eq_116 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    simp only [pl_ik_low8_merge]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm2 ⊢
    have hvm_final : VmPreserved s0 _ := hvm_after_call.trans hvm2
    clear hvm1 hvm_call hvm_after_call hvm2
    wp_done

/-- Placed `VmPreserved` exact-`speAt` Err contract of `<IdentityKey as TryFrom<&[u8]>>::try_from`
(Block `116`). -/
theorem identityKeyTryFromSlice_err_placed [LibsignalPlacement] (A : RustAlloc)
    (fn : List (BitVec 8)) (H : LibsignalHooks) :
    subroutine_ok ((blkPC_116).rebase (blkPl_116).base H)
      (blkPl_116).base
      (withLsCodeLoaded lsmpl (identityKeyTryFromSliceErrPlacedSpec A fn)) := by
  refine subroutine_ok_map (identityKeyTryFromSlice_wordsErr_placed H) ?_
  rintro ⟨p, bs, e, outPtr⟩ R s0 hpre
  have ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have h48 : memRegion outPtr 48 = memRegion outPtr 40 ∗ memRegion (outPtr + 40#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split outPtr 40 8 (by decide)
  simp only [identityKeyTryFromSliceErrPlacedSpec, withVmPreserved,
    CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.identityKeyTryFromSliceErrPlacedSpec,
    h48, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, e, outPtr), memRegion (outPtr + 40#64) 8 ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded]
    rw [sepConj_comm ((identityKeyTryFromSliceWordsErrPlacedSpec).pre _ s0),
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [identityKeyTryFromSliceWordsErrPlacedSpec, withVmPreserved,
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.identityKeyTryFromSliceWordsErrPlacedSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hdes⟩, by ac_nf at hmem ⊢⟩
  · dsimp only [withLsCodeLoaded, identityKeyTryFromSliceWordsErrPlacedSpec, withVmPreserved,
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.identityKeyTryFromSliceWordsErrPlacedSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, htr, hpost⟩
    dsimp only [withLsCodeLoaded, identityKeyTryFromSliceErrPlacedSpec, withVmPreserved,
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.identityKeyTryFromSliceErrPlacedSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, htr, ?_⟩
    have h32 : memRegion (outPtr + 16#64) 24 ∗ memRegion (outPtr + 40#64) 8 =
        memRegion (outPtr + 16#64) 32 := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using
        (ProofLib.memRegion_split (outPtr + 16#64) 24 8 (by decide)).symm
    have hreg : sf.mem ⊨
        ((outPtr ↦₆₄ (ikErrWords e).1) ∗ ((outPtr + 8#64) ↦₆₄ (ikErrWords e).2) ∗
          (memRegion (outPtr + 16#64) 24 ∗ memRegion (outPtr + 40#64) 8)) ∗
          ((p ↦ₛ bs) ∗ lsLogOff ∗ stackAt s0.sp 96 ∗ R) := by
      ac_nf at hpost ⊢
    rw [h32] at hreg
    have hspe := Satisfies.mono (sepConj_mono_left (ikErrWords_entails_speAt hdes A fn outPtr)) hreg
    ac_nf at hspe ⊢

/-! ## Section 2: Budget-Threaded `drop_spe_placed_cro_ok_x` -/

theorem drop_spe_placed_cro_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((Getters.blkPC_5).rebase (Getters.blkPl_5).base H) (lsmpl.base 5)
      (withLsCodeRoLoaded lsmpl (dropSpeSpecX M A lim)) := by
  refine subroutine_ok_map (drop_spe_placed_ok hdealloc) ?_
  rintro ⟨x, st⟩ R s0 hpre
  have ⟨hcro, hpre⟩ := extract_withLsCodeRoLoaded hpre
  have hsz : dropSpeStackX = dropSpeStack + (extHookStack - allocHookStack) := by decide
  have hsplit := ProofLib.stackAt_split_bottom s0.sp dropSpeStack
    (extHookStack - allocHookStack) (by decide)
  dsimp only [dropSpeSpecX] at hpre ⊢
  rw [hsz, hsplit] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  refine ⟨(x, st), memRegion (s0.sp - BitVec.ofNat 64 (dropSpeStack + (extHookStack - allocHookStack)))
    (extHookStack - allocHookStack) ∗ R, ?_, ?_⟩
  · dsimp only [Getters.withLsRoLoaded, dropSpeSpec]
    rw [sepConj_comm (⌜s0.readReg64 .x0 = x.a ∧ _⌝ ∗ _), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcro.2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, by ac_nf at hmem ⊢⟩
  · intro sf hpost
    dsimp only [Getters.withLsRoLoaded, dropSpeSpec] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [hsz, hsplit]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpost.1, by have hm := hpost.2; ac_nf at hm ⊢⟩

/-! ## Section 3: `TripleRatchetHooksWPlaced`, `TryFromDepsPlaced`, and `PksmCalleesPlaced` -/

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

theorem tripleRatchetHooksWPlaced_of_codecHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    TripleRatchetHooksWPlaced A lim H :=
  tripleRatchetHooksWPlaced_of_codecHooks_e4 hH

theorem tryFromDepsPlaced_of_codecHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    TryFromDepsPlaced A lim H := by
  have hd := portDepsPlaced_of_hooks hH
  have hshim_n := hookSat_noAllocShimBudget_of_withVmPreserved hH.shim
  have hmc_f := hookSat_framelessMemcpyBudget_of_withVmPreserved hH.memcpy
  exact
    { intoBoxed := ls_subroutine_ok_cro_ρ85 (j := 56)
        (subroutine_ok_withLsCodeRoLoaded_of_plain'
          (into_boxed_slice_placed_ok_x hH.dealloc hH.realloc))
      tryClone := ls_subroutine_ok_cro_ρ85 (j := 23)
        (subroutine_ok_withLsCodeRoLoaded_of_plain'
          (try_clone_from_ref_placed_ok_x hshim_n hH.alloc hmc_f))
      varintSlice := ls_subroutine_ok_cro_ρ85 (j := 76)
        (subroutine_ok_withLsCodeRoLoaded_of_cl hd.varintSlice)
      int32Merge := ls_subroutine_ok_cro_ρ85 (j := 8)
        (subroutine_ok_withLsCodeRoLoaded_of_cl hd.int32Merge)
      skipField := ls_subroutine_ok_cro_ρ85 (j := 1)
        (subroutine_ok_withLsCodeRoLoaded_of_cl hd.skipField)
      dropDecodeError := ls_subroutine_ok_cro_ρ85 (j := 4)
        (subroutine_ok_withLsCodeRoLoaded_of_plain' hd.dropDecodeError)
      bytesMerge := ls_subroutine_ok_cro_ρ85 (j := 7)
        (bytes_merge_exact_placed_ok_x_e4 hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy)
      dropSpe := ls_subroutine_ok_cro_ρ85 (j := 5) (drop_spe_placed_cro_ok_x hH.dealloc) }

/-- All budget-threaded callee contracts used by `PreKeySignalMessage::try_from` (Block `111`)
under `[LibsignalPlacement]`, discharged from `CodecHooksPlaced M A lim H` via
`pksmCalleesPlaced_of_codecHooks`. -/
structure PksmCalleesPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  dealloc : PreKeyDeallocOk (LibsignalCodeRoLoaded lsmpl) A lim H
  deallocX : subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustDeallocExternSpecWithStack M A lim extHookStack))
  panic_alloc : H lsAllocHandleErrorSym = some Rust.panicked
  panic_raw : H lsHandleErrorSym = some Rust.panicked
  decodeErrorFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (decodeErrorFromSpecWithStack M A lim (2 * extHookStack)))
  decodeErrorPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack)))
  decodeVarintSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack)))
  varintSlice : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (decodeVarintSliceSpecX A lim))
  int32Merge : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (int32MergeSpecX A lim))
  skipField : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (skipFieldSpecX A lim))
  bytesMerge : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (bytesMergeExactRawSpecX A lim))
  dropDecodeError : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 4)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropDecodeErrorSpecX A lim))
  dropSpe : PreKeyDropSpeOk (LibsignalCodeRoLoaded lsmpl) A lim H
  dropSpeX : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 5)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (dropSpeSpecX M A lim))
  intoBoxed : PreKeyIntoBoxOk (LibsignalCodeRoLoaded lsmpl) A lim H
  intoBoxedX : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 56)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (intoBoxedSliceSpecX M A lim))
  tryClone : PreKeyTryCloneOk (LibsignalCodeRoLoaded lsmpl) A lim H
  tryCloneX : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 23)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (tryCloneFromRefSpecX M A lim))
  deserializeOk : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 201)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) deserializeOk33PlacedSpec)
  deserializeFull : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 201)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (withVmPreserved deserializeFullPlacedSpec))
  sigTryFrom : PreKeySigTryFromOk (LibsignalCodeRoLoaded lsmpl) A lim H
  identityKeyOk : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 116)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) identityKeyTryFromSliceOkPlacedSpec)
  identityKeyWordsErr : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 116)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) identityKeyTryFromSliceWordsErrPlacedSpec)
  identityKeyErr : ∀ (f : List (BitVec 8)), subroutine_ok (preKeyPlacedProg H) (lsmpl.base 116)
    (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (identityKeyTryFromSliceErrPlacedSpec A.repAlloc f))

/-- Discharges every callee contract in `PksmCalleesPlaced M A lim H` from
`CodecHooksPlaced M A lim H`. -/
theorem pksmCalleesPlaced_of_codecHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    PksmCalleesPlaced M A lim H := by
  have hd := portDepsPlaced_of_hooks hH
  have hcl_of_cro : ∀ m, LibsignalCodeRoLoaded lsmpl m → LibsignalCodeLoaded lsmpl m :=
    fun _ h => h.1
  have hshim_n := hookSat_noAllocShimBudget_of_withVmPreserved hH.shim
  have hmc_f := hookSat_framelessMemcpyBudget_of_withVmPreserved hH.memcpy
  exact
    { dealloc := preKeyDeallocOk_of_hookSat hH.dealloc
      deallocX := subroutine_ok_withPreKeyInv_of_plain
        (rustDeallocExternWithStack_of_rustDealloc (by decide) (by decide)
          (ls_hook_ok_of_mem hH.dealloc))
      panic_alloc := hH.panic_alloc
      panic_raw := hH.panic_raw
      decodeErrorFrom := ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 261) hcl_of_cro hd.decodeErrorFrom
      decodeErrorPush := pksmDecodeErrorPushBounded_of_codecHooks hH
      decodeVarintSlow := ls_subroutine_ok_pk_of_cl (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 293) hcl_of_cro hd.varintSlow
      varintSlice := ls_subroutine_ok_pk_of_cl (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 76) hcl_of_cro hd.varintSlice
      int32Merge := ls_subroutine_ok_pk_of_cl (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 8) hcl_of_cro hd.int32Merge
      skipField := ls_subroutine_ok_pk_of_cl (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 1) hcl_of_cro hd.skipField
      bytesMerge := subroutine_ok_withPreKeyInv_of_cro
        (ls_subroutine_ok_cro_of_block (callerProg := preKeyPlacedProg H)
          (i := 111) (j := 7)
          (bytes_merge_exact_placed_ok_x_e4 hH.shim hH.alloc hH.realloc hH.dealloc hH.memcpy))
      dropDecodeError := ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 4) hcl_of_cro hd.dropDecodeError
      dropSpe := preKeyDropSpeOk_cro_of_hookSat hH.dealloc
      dropSpeX := subroutine_ok_withPreKeyInv_of_cro
        (ls_subroutine_ok_cro_of_block (callerProg := preKeyPlacedProg H)
          (i := 111) (j := 5) (drop_spe_placed_cro_ok_x hH.dealloc))
      intoBoxed := preKeyIntoBoxOk_of_hooks hcl_of_cro hH.dealloc hH.realloc
      intoBoxedX := ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 56) hcl_of_cro
        (into_boxed_slice_placed_ok_x hH.dealloc hH.realloc)
      tryClone := preKeyTryCloneOk_of_hooks hcl_of_cro hshim_n hH.alloc hmc_f
      tryCloneX := ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 23) hcl_of_cro
        (try_clone_from_ref_placed_ok_x hshim_n hH.alloc hmc_f)
      deserializeOk := ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 201) hcl_of_cro (deserialize_placed_ok H)
      deserializeFull := ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 201) hcl_of_cro (deserializeFull_vm_placed_ok H)
      sigTryFrom := preKeySigTryFromOk_cro_of_deps
        (tripleRatchetHooksWPlaced_of_codecHooks hH) (tryFromDepsPlaced_of_codecHooks hH)
      identityKeyOk := ls_subroutine_ok_pk_of_cl (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 116) hcl_of_cro (identityKeyTryFromSlice_placed_ok H)
      identityKeyWordsErr := ls_subroutine_ok_pk_of_cl (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 116) hcl_of_cro (identityKeyTryFromSlice_wordsErr_placed H)
      identityKeyErr := fun f => ls_subroutine_ok_pk_of_cl (callerProg := preKeyPlacedProg H)
        (i := 111) (j := 116) hcl_of_cro (identityKeyTryFromSlice_err_placed A.repAlloc f H) }

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
