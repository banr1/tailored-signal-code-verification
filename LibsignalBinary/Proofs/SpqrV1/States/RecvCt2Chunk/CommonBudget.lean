/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget
public import LibsignalBinary.Proofs.SpqrV1.GF.IsNonZero
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux
public meta import Lean -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux -- shake: keep
public meta import ProofLib.SepLogic.WP.ControlTactics -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Budget Callee Contracts & Framing Helpers

`VmPreserved` proofs for `spqr::util::is_non_zero` (`0x5e50c` / Block `380`), total-correctness
`libcruxHmacSafeBudgetSpec`, and fixed-offset budget callee contracts for `recv_ct2_chunk`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement blkPC_380 blkPl_380 libsignalSessionCode
  libsignalSessionCode_fnOff_0x46920 libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x58ac4 libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x5de8c libsignalSessionCode_fnOff_0x5e5f0
  libsignalSessionCode_fnOff_0x5eab8 libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x67028
)
open scoped CryptoVerification.CodeLayout
open CryptoVerification.InImageLift (subroutine_ok_inImage_of_subroutine_ok)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes HkdfFn LibcruxHmacCall MlKem NUM_POLYS isNonZero
  libcruxHmacName mlkemDecapsName mlkemDecapsSpec optKeyBytesAt spqrHkdfWith
)
open CryptoVerification.LibsignalTripleRatchet (
  allocZeroedName extHookStack tripleRatchetProgAtExt withStack
)
open CryptoVerification.RustHeap (RustAlloc vecU8)
open CryptoVerification.SpqrV1.Alloc (doReserve7Name)
open CryptoVerification.SpqrV1.Auth (authUpdateName)
open CryptoVerification.SpqrV1.Auth.UpdateFacts (
  allocZeroed_fnOff alloc_fnOff authUpdate_fnOff handleError_fnOff shim_fnOff
)
open CryptoVerification.SpqrV1.ChainProofs (
  hkdfToSliceSpecExt hkdfToSliceSpqrSpec sliceConcatName
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  dealloc_fnOff hkdfToSlice_fnOff sliceConcat_fnOff
)
open CryptoVerification.SpqrV1.Drop (
  DropGlueSortedSetPt16Ghost dropSortedSetPt16Name sub_ok_of_addr_eq
)
open CryptoVerification.SpqrV1.GF.IsNonZero (
  isNonZeroName isNonZeroSpec isNonZero_asm_eq isNonZero_fnOff
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre stackAt_16_merge_byte12 stackAt_16_split_byte12
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt)
open CryptoVerification.SpqrV1.Kdf (hkdfToSliceName)
open CryptoVerification.SpqrV1.Poly (
  boolByte polyDecoderAt polyDecoderIsCompleteOff polyDecoderPadOff
  polyDecoderPadSize polyDecoderPtsNeededOff sortedSetPtListOf vecHeaderBytes
)
open CryptoVerification.SpqrV1.Poly.AddChunk (
  PolyDecoderStrictSorted addChunkName addChunk_fnOff
)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  DecodedMessageGhost decodedMessageName decodedMessageStack decodedMessageTotal
  decodedMessage_eq_ok optVecU8Of
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  SplitBytes assertFailedU64_fnOff doReserve7_fnOff_eq gf16IsNonZero_fnOff
  memcpy_fnOff mlkemDecaps_fnOff panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  polyDecodedMessageName polyDecodedMessageStackX polyDecodedMessage_fnOff
  recvCt2ChunkName recvCt2Chunk_fnOff sliceIndexFail_fnOff sub_ok_at_recvCt2
  unwrapFailed_fnOff
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
  rustCliDeallocBudgetExternSpecWithStack
)
open LibsignalBinary.Heap.SpecBudget (
  LibcruxHmacEnv libcruxHmacBudgetSpec libcruxHmacSha256Events withVmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  sepWP_rebase_vmPreserved trapHooks
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  sliceConcat3Spec sliceConcat3SpecXA
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveSpecX)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget (do_reserve_7_ok_ext_x_4k)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec dropGlueSortedSetPt16SpecBase)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (AddChunkOkX addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  DecodedMessageOkExt decodedMessageSpec
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget (
  PolyDecodedMessageEnv PolyDecodedMessageOkX polyDecodedMessageSpec
  polyDecodedMessageSpecOfEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  AllocContractsXBudget alloc_ok_at_norm_ext_x dealloc_ok_at_norm_ext_x
  memcpy_ok_at2_ext_x session2MemcpyBudgetSpecX session2ShimBudgetSpecX shim_ok_at2_ext_x
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  allocNoOomWithStack_inImage_of_budget
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec
)

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst := h

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] isNonZero_asm_eq
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  recvCt2Chunk_fnOff addChunk_fnOff polyDecodedMessage_fnOff mlkemDecaps_fnOff
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  memcpy_fnOff gf16IsNonZero_fnOff doReserve7_fnOff_eq
  assertFailedU64_fnOff sliceIndexFail_fnOff unwrapFailed_fnOff
  panicBoundsCheck_fnOff panicConstAddOverflow_fnOff
  libsignalSessionCode_fnOff_0x59834
  libsignalSessionCode_fnOff_0x67028
  libsignalSessionCode_fnOff_0x66788
  libsignalSessionCode_fnOff_0x58ac4
  libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x46920
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5e5f0
  (ls_stub% "memcpy") (ls_hook% "memcpy")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
  (ls_stub% "libcrux_hmac::hmac") (ls_hook% "libcrux_hmac::hmac")
  (ls_stub% "core::panicking::assert_failed::<u64, u64>")
  (ls_hook% "core::panicking::assert_failed::<u64, u64>")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")
  (ls_stub% "core::result::unwrap_failed") (ls_hook% "core::result::unwrap_failed")
  (ls_stub% "core::panicking::panic_bounds_check")
  (ls_hook% "core::panicking::panic_bounds_check")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")

/-! ## Reducible Re-Exports from `CommonBudgetAux` -/

abbrev onPanic_false_entails_recvCt2 := @CommonBudgetAux.onPanic_false_entails_recvCt2
abbrev onPanic_pure_entails_recvCt2 := @CommonBudgetAux.onPanic_pure_entails_recvCt2
abbrev onPanic_budget_entails_recvCt2 := @CommonBudgetAux.onPanic_budget_entails_recvCt2
abbrev onPanic_hmac_budget_entails_recvCt2 := @CommonBudgetAux.onPanic_hmac_budget_entails_recvCt2
abbrev allowPanic_isPanic_budget_recvCt2 := @CommonBudgetAux.allowPanic_isPanic_budget_recvCt2

abbrev recvCt2ChunkBudgetPostQOfEnv := @CommonBudgetAux.recvCt2ChunkBudgetPostQOfEnv
abbrev recvCt2ChunkBudgetPostQ := @CommonBudgetAux.recvCt2ChunkBudgetPostQ
abbrev recvCt2ChunkBudgetPostQExtOfEnv := @CommonBudgetAux.recvCt2ChunkBudgetPostQExtOfEnv
abbrev recvCt2ChunkBudgetPostQExt := @CommonBudgetAux.recvCt2ChunkBudgetPostQExt
abbrev recvCt2ChunkBudgetPostQp := @CommonBudgetAux.recvCt2ChunkBudgetPostQp
abbrev sepWPp_frame_recvCt2_budget_ext := @CommonBudgetAux.sepWPp_frame_recvCt2_budget_ext

abbrev SplitBytes.memcpyVm_withStack_ok := @CommonBudgetAux.SplitBytes.memcpyVm_withStack_ok
abbrev SplitBytes.memcpyVm_withStack_inImage_ok :=
  @CommonBudgetAux.SplitBytes.memcpyVm_withStack_inImage_ok
abbrev splitBytes_memcpyVm_withStack_ok := @CommonBudgetAux.SplitBytes.memcpyVm_withStack_ok
abbrev splitBytes_memcpyVm_withStack_inImage_ok :=
  @CommonBudgetAux.SplitBytes.memcpyVm_withStack_inImage_ok

abbrev fitsEnv_seqEnv_left := @CommonBudgetAux.fitsEnv_seqEnv_left
abbrev fitsEnv_seqEnv_right := @CommonBudgetAux.fitsEnv_seqEnv_right
abbrev seqEnv_nonempty := @CommonBudgetAux.seqEnv_nonempty
abbrev authUpdateLenEnv_nonempty := @CommonBudgetAux.authUpdateLenEnv_nonempty
abbrev freeOnlyEvs_nonempty := @CommonBudgetAux.freeOnlyEvs_nonempty
abbrev freeOnlyEvs_rustDealloc1 := @CommonBudgetAux.freeOnlyEvs_rustDealloc1
abbrev freeOnlyEvs_macDealloc := @CommonBudgetAux.freeOnlyEvs_macDealloc

abbrev recvCt2ChunkEnv_of_epoch_ne := @CommonBudgetAux.recvCt2ChunkEnv_of_epoch_ne
abbrev recvCt2ChunkEnv_of_lt_128 := @CommonBudgetAux.recvCt2ChunkEnv_of_lt_128
abbrev recvCt2ChunkEnv_of_bad_kem_len := @CommonBudgetAux.recvCt2ChunkEnv_of_bad_kem_len
abbrev recvCt2ChunkEnv_of_postDecaps := @CommonBudgetAux.recvCt2ChunkEnv_of_postDecaps
abbrev recvCt2PostDecapsEnv_mk := @CommonBudgetAux.recvCt2PostDecapsEnv_mk

abbrev fitsEnv_addChunk_of_recvCt2 := @CommonBudgetAux.fitsEnv_addChunk_of_recvCt2
abbrev fitsEnv_decodedMessage_of_recvCt2 := @CommonBudgetAux.fitsEnv_decodedMessage_of_recvCt2
abbrev fitsEnv_tail_of_recvCt2 := @CommonBudgetAux.fitsEnv_tail_of_recvCt2
abbrev fitsEvents_macCt2Alloc_of_tail := @CommonBudgetAux.fitsEvents_macCt2Alloc_of_tail
abbrev fitsEnv_postDecaps_of_tail := @CommonBudgetAux.fitsEnv_postDecaps_of_tail
abbrev fitsEvents_preAuth_of_postDecaps := @CommonBudgetAux.fitsEvents_preAuth_of_postDecaps
abbrev fitsEnv_authUpdate_of_postDecaps := @CommonBudgetAux.fitsEnv_authUpdate_of_postDecaps
abbrev fitsEnv_reserveCt1_of_postDecaps := @CommonBudgetAux.fitsEnv_reserveCt1_of_postDecaps
abbrev fitsEnv_doReserve_of_reserveCt1 := @CommonBudgetAux.fitsEnv_doReserve_of_reserveCt1
abbrev fitsEvents_hmac_of_postDecaps := @CommonBudgetAux.fitsEvents_hmac_of_postDecaps
abbrev fitsEnv_libcruxHmacEnv_of_fitsEvents := @CommonBudgetAux.fitsEnv_libcruxHmacEnv_of_fitsEvents
abbrev fitsEnv_free1_of_postDecaps := @CommonBudgetAux.fitsEnv_free1_of_postDecaps
abbrev fitsEnv_optSecret32_of_postDecaps := @CommonBudgetAux.fitsEnv_optSecret32_of_postDecaps
abbrev fitsEnv_free2_of_postDecaps := @CommonBudgetAux.fitsEnv_free2_of_postDecaps

/-! ## `spqr::util::is_non_zero` (`0x5e5f0`, Block `380`) with `VmPreserved` -/

local elab "lift_fetches_withSvc" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut hyps : Array Lean.Meta.Hypothesis := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Arm64.Program.fetch 2 then
          let progE := (ty.getArg! 1).getArg! 0
          if !progE.isAppOfArity ``Arm64.Program.withSvc 2 then
            let prf ← Lean.Meta.mkAppM ``withSvc_fetch_eq
              #[Lean.mkConst ``Arm64.noSyscalls, decl.toExpr]
            let newTy ← Lean.Meta.inferType prf
            hyps := hyps.push { userName := `this, type := newTy, value := prf }
    if !hyps.isEmpty then
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← g.assertHypotheses hyps
      Lean.Elab.Tactic.replaceMainGoal [g']

@[local arm64_norm, local wp_norm]
private theorem isNonZero_asm_eq' (v : BitVec 8) :
    BitVec.setWidth 64 (BitVec.truncate 8 ((0#32 - BitVec.zeroExtend 32 v) >>> 31)) =
    BitVec.zeroExtend 64 (isNonZero v) := by
  revert v
  decide +kernel

/-- Relocatable `spqr::util::is_non_zero` (Block `380`, 9 instructions) satisfies
`withVmPreserved isNonZeroSpec` under `[LibsignalPlacement]`. -/
theorem isNonZero_vm_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_380).rebase (blkPl_380).base H) (blkPl_380).base
      (withVmPreserved isNonZeroSpec) := by
  simp only [withVmPreserved, isNonZeroSpec]
  wp_init v s0
  wp_simp_pre [stackAt_16_split_byte12]
  wp_pull_exists
  refine SepWP.mono
    (post := fun sf P_f =>
      VmPreserved s0 sf ∧
      (P_f ⊢ stackAt s0.sp 0x10) ∧
      sf.readReg64 .x0 = BitVec.zeroExtend 64 (isNonZero v) ∧
      sf.trace = s0.trace ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf)
    ?_
    (fun sf P_f _ _ ⟨hvm, hstk, hx0_f, htr_f, hsp_f, hcs_f⟩ =>
      ⟨fun hm => by
        have hm' := Satisfies.mono (sepConj_mono_left hstk) hm
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hvm, ⟨hx0_f, htr_f⟩, hm'⟩, hsp_f, hcs_f⟩)
  by_vm_steps (
    wp_steps
    apply SepWP.fold
      (stackAt_16_merge_byte12 s0.sp
        (BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (0#32 - BitVec.zeroExtend 32 v) >>> 31)))
      (by sep_focus)
    wp_done)

/-- Fixed-base `spqr::util::is_non_zero` (`0x5e50c`, 9 instructions) satisfies
`withVmPreserved isNonZeroSpec` on `tripleRatchetProgAtExt b ext`. -/
theorem isNonZero_vm_ok (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr isNonZeroName)
      (withVmPreserved isNonZeroSpec) := by
  have hfn : libsignalSessionCode.fnOff isNonZeroName = 0x5e5f0 := isNonZero_fnOff
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.GF.IsNonZero.isNonZeroBin b trapHooks hfn 0x5e5f0 36
  dsimp only [tripleRatchetProgAtExt] at ⊢
  clear hfn
  simp only [withVmPreserved, isNonZeroSpec]
  wp_init v s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b trapHooks).fnAddr isNonZeroName := by
    rw [Program.fnAddr_rebase, isNonZero_fnOff]; exact hpc
  clear hpc
  wp_simp_pre [stackAt_16_split_byte12]
  wp_pull_exists
  refine SepWP.mono
    (post := fun sf P_f =>
      VmPreserved s0 sf ∧
      (P_f ⊢ stackAt s0.sp 0x10) ∧
      sf.readReg64 .x0 = BitVec.zeroExtend 64 (isNonZero v) ∧
      sf.trace = s0.trace ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf)
    ?_
    (fun sf P_f _ _ ⟨hvm, hstk, hx0_f, htr_f, hsp_f, hcs_f⟩ =>
      ⟨fun hm => by
        have hm' := Satisfies.mono (sepConj_mono_left hstk) hm
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hvm, ⟨hx0_f, htr_f⟩, hm'⟩, hsp_f, hcs_f⟩)
  apply sepWP_rebase_vmPreserved
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr isNonZeroName = entry
  lift_fetches_withSvc
  examples_hide_fetches
  wp_steps
  apply SepWP.fold
    (stackAt_16_merge_byte12 s0.sp
      (BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (0#32 - BitVec.zeroExtend 32 v) >>> 31)))
    (by sep_focus)
  wp_done

theorem isNonZero_ok_at_recvCt2 (img : Obj.Image) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5e5f0 - 0x59834))
      ((withVmPreserved isNonZeroSpec).inImage img) :=
  sub_ok_at_recvCt2 (callee := isNonZeroName)
    (by rw [recvCt2Chunk_fnOff, isNonZero_fnOff]; rfl)
    (subroutine_ok_inImage_of_subroutine_ok img (isNonZero_vm_ok img.base ext))

/-! ## Allocator, `memcpy`, `shim`, `mlkem_decaps`, and `libcrux_hmac` Call-Site Bridges -/

theorem shim_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (session2ShimBudgetSpecX.inImage img) :=
  shim_ok_at2_ext_x hA

theorem memcpy_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "memcpy"))
      (session2MemcpyBudgetSpecX.inImage img) :=
  memcpy_ok_at2_ext_x hA

theorem memcpy_region_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "memcpy"))
      ((withStack sessionMemcpyRegionBudgetSpec extHookStack).inImage img) :=
  hA.session_memcpy_region_ok_at recvCt2ChunkName
    (num% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "memcpy"))
    extHookStack (by decide) (by decide) (by simp only [arm64_norm])

theorem splitBytes_memcpyVm_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64)
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "memcpy"))
      ((withStack (DefsBudget.SplitBytes.memcpyVmSpec S) extHookStack).inImage img) :=
  CommonBudgetAux.SplitBytes.memcpyVm_withStack_inImage_ok S hn extHookStack
    (memcpy_region_ok_at_recvCt2 hA)

theorem alloc_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_alloc"))
      ((LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStackBase M A lim false extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hA

theorem allocNoOom_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_alloc"))
      ((LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStackBase M A lim false extHookStack).inImage img) :=
  allocNoOomWithStack_inImage_of_budget (alloc_ok_at_recvCt2 hA)

theorem dealloc_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContractsXBudget img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_dealloc"))
      ((LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hA

abbrev AllocZeroedWithStackOkX :=
  @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.AllocZeroedWithStackOkX
abbrev allocZeroedWithStackOkX_of_hook :=
  @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.allocZeroedWithStackOkX_of_hook

theorem allocZeroed_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : AllocZeroedWithStackOkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_alloc_zeroed"))
      ((LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocBudgetSpecWithStackBase M A lim true extHookStack).inImage img) :=
  sub_ok_at_recvCt2 (callee := allocZeroedName)
    (by rw [recvCt2Chunk_fnOff, allocZeroed_fnOff]; rfl) h

theorem allocZeroedNoOom_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : AllocZeroedWithStackOkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "__rustc::__rust_alloc_zeroed"))
      ((LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStackBase M A lim true extHookStack).inImage img) :=
  allocNoOomWithStack_inImage_of_budget (allocZeroed_ok_at_recvCt2 h)

theorem mlkem_decaps_ok_at_recvCt2 {img : Obj.Image} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdecaps : HookSat ext mlkemDecapsName (withVmPreserved (mlkemDecapsSpec K))) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key"))
      ((withVmPreserved (mlkemDecapsSpec K)).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img <|
    hook_ok_at (hname := "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
      recvCt2Chunk_fnOff (by fnoff_eq) (by decide)
      (ls_hook% "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key")
      (by simp [Rust.isPanicSymbol]) hdecaps

private theorem libcrux_hmac_raw_ok_at_recvCt2 {b : BitVec 64} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_hmac::hmac"))
      (libcruxHmacBudgetSpec F M A lim) :=
  hook_ok_at (hname := "libcrux_hmac::hmac")
    recvCt2Chunk_fnOff (by fnoff_eq) (by decide)
    (ls_hook% "libcrux_hmac::hmac")
    (by simp [Rust.isPanicSymbol]) hhmac

theorem libcrux_hmac_ok_at_recvCt2 {img : Obj.Image} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_hmac::hmac"))
      ((libcruxHmacBudgetSpec F M A lim).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (libcrux_hmac_raw_ok_at_recvCt2 hhmac)

/-- Specialized budget `libcrux_hmac::hmac` contract when `key.length < 2 ^ 32`,
`data.length < 2 ^ 32`, and `FitsEvents M lim st libcruxHmacSha256Events` are already known at
the call site (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`, concrete `libcruxHmacSha256Events` step). -/
def libcruxHmacSafeBudgetSpec (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (LibcruxHmacCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
      FitsEvents M lim st libcruxHmacSha256Events⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A.repAlloc x.ret (hmacWith F x.key x.data) ∗
      A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗ stackAt s0.sp extHookStack

theorem subroutine_ok_libcruxHmacSafeBudget_of_budget {prog : Program} {entry : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hhmac : subroutine_ok prog entry (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok prog entry (libcruxHmacSafeBudgetSpec F M A lim) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hsp => ?_
  dsimp only [libcruxHmacSafeBudgetSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_lt, hd_lt, hfit⟩, hmem⟩
  have hfit_env : FitsEnv M lim st (LibcruxHmacEnv x) :=
    fitsEnv_libcruxHmacEnv_of_fitsEvents x hk_lt hd_lt hfit
  have hpre' : s0.mem ⊨ (libcruxHmacBudgetSpec F M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hfit_env⟩, hmem⟩
  refine (hhmac.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [libcruxHmacBudgetSpec, libcruxHmacSafeBudgetSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨_, _, htr, hevs⟩, hmem'⟩
    unfold LibcruxHmacEnv at hevs
    simp only [hk_lt, hd_lt, and_self, ↓reduceIte] at hevs
    rw [hevs] at hmem'
    exact ⟨htr, hmem'⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [libcruxHmacBudgetSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hk_ge | hd_ge, _⟩, _⟩ <;> omega
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

theorem libcrux_hmac_safe_ok_at_recvCt2 {img : Obj.Image} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName +
        bv% (ls_rel% "<spqr::v1::chunked::send_ek::EkSentCt1Received>::recv_ct2_chunk" "libcrux_hmac::hmac"))
      ((libcruxHmacSafeBudgetSpec F M A lim).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_libcruxHmacSafeBudget_of_budget (libcrux_hmac_raw_ok_at_recvCt2 hhmac))

/-! ## Fixed-Offset SPQR Callee Bridges (`Poly`, `Concat`, `Kdf`, `Auth`, `DoReserve`, `Drop`) -/

theorem addChunk_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : AddChunkOkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x67028 - 0x59834))
      ((addChunkSpecX M A lim).inImage img) := by
  unfold AddChunkOkX at h
  exact sub_ok_at_recvCt2 (callee := addChunkName)
    (by rw [recvCt2Chunk_fnOff, addChunk_fnOff]; rfl) h

private theorem optVecU8Of_eq_optKeyBytesAt (A : RustAlloc) (a : BitVec 64) (opt : Option Bytes) :
    optVecU8Of A a opt = optKeyBytesAt A a opt := by
  cases opt <;> rfl

theorem polyDecodedMessageOkX_of_decodedMessage {img : Obj.Image}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdm : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodedMessageName)
      ((decodedMessageSpec M A lim img.base).inImage img)) :
    PolyDecodedMessageOkX img M A lim ext := by
  unfold PolyDecodedMessageOkX
  change subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr decodedMessageName)
    ((polyDecodedMessageSpec M A lim img.base).inImage img)
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre0⟩
  have hpts_sort : x.dec.pts.length = 16 ∧ PolyDecoderStrictSorted x.dec := by
    have h1 : s0.mem ⊨
        ⌜x.dec.pts.length = 16 ∧ x.dec.ptsNeeded < 2 ^ 64⌝ ∗
        ⌜img.base &&& 0xfff#64 = 0#64 ∧
          s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec ∧
          FitsEnv M lim st (PolyDecodedMessageEnv x)⌝ ∗
        (memRegion x.outA vecHeaderBytes ∗
          sortedSetPtListOf A.repAlloc x.decA x.dec.pts ∗
          ((x.decA + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 x.dec.ptsNeeded) ∗
          ((x.decA + polyDecoderIsCompleteOff) ↦₈ boolByte x.dec.isComplete) ∗
          memRegion (x.decA + polyDecoderPadOff) polyDecoderPadSize ∗
          tokenInitAt img.base ∗
          reduceTableAt img.base ∗
          A.pool lim st s0 ∗
          stackAt s0.sp polyDecodedMessageStackX ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hpre0
      dsimp only [polyDecodedMessageSpec, polyDecodedMessageSpecOfEnv, polyDecoderAt, NUM_POLYS]
      sep_ac_rfl
    rw [satisfies_pure_sepConj] at h1
    rcases h1 with ⟨⟨hlen, _⟩, h2⟩
    rw [satisfies_pure_sepConj] at h2
    exact ⟨hlen, h2.1.2.2.2.1⟩
  have hdec_eq := decodedMessage_eq_ok x.dec hpts_sort.1 hpts_sort.2
  let x' : DecodedMessageGhost := { out := x.outA, decA := x.decA, dec := x.dec }
  have hpre' : s0.mem ⊨ ((decodedMessageSpec M A lim img.base).inImage img).pre (x', st) s0 ∗ R := by
    dsimp only [Spec.inImage, decodedMessageSpec, polyDecodedMessageSpec,
      polyDecodedMessageSpecOfEnv, PolyDecodedMessageEnv, decodedMessageStack,
      polyDecodedMessageStackX, x'] at hpre0 ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, hpre0⟩
  refine subroutine_ok.mono_outcome hdm (x', st) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, decodedMessageSpec, x'] at hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hevs, htr⟩, hpost_mem⟩
    rw [optVecU8Of_eq_optKeyBytesAt] at hpost_mem
    dsimp only [Spec.inImage, polyDecodedMessageSpec, polyDecodedMessageSpecOfEnv,
      decodedMessageStack, polyDecodedMessageStackX] at hpost_mem ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨decodedMessageTotal x.dec, ?_⟩
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hdec_eq, htr, hevs⟩, hpost_mem⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

theorem polyDecodedMessageOkX_of_ext {img : Obj.Image}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdm : DecodedMessageOkExt img.base M A lim ext) :
    PolyDecodedMessageOkX img M A lim ext :=
  polyDecodedMessageOkX_of_decodedMessage (subroutine_ok_inImage_of_subroutine_ok img hdm)

theorem polyDecodedMessage_ok_at_recvCt2 {img : Obj.Image}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : PolyDecodedMessageOkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x66788 - 0x59834))
      ((polyDecodedMessageSpec M A lim img.base).inImage img) :=
  sub_ok_at_recvCt2 (callee := polyDecodedMessageName)
    (by rw [recvCt2Chunk_fnOff, polyDecodedMessage_fnOff]; rfl) h

abbrev SliceConcat2OkX := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.SliceConcat2OkX
abbrev HkdfToSliceSpqrOkX := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.HkdfToSliceSpqrOkX
abbrev HkdfToSliceSpqrOkExt := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.HkdfToSliceSpqrOkExt
abbrev AuthUpdateOkX := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.AuthUpdateOkX
abbrev AuthUpdateOkExt := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.AuthUpdateOkExt
abbrev authUpdateSpec := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.authUpdateSpec
abbrev authUpdateSpecExt := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.authUpdateSpecExt

/-- Fixed-offset contract for 3-slice byte concatenation (`allocHookStack`). -/
def SliceConcat3OkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr sliceConcatName)
    ((sliceConcat3Spec M A lim).inImage img)

/-- Fixed-offset contract for 3-slice byte concatenation (`extHookStack`). -/
def SliceConcat3OkXA (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr sliceConcatName)
    ((sliceConcat3SpecXA M A lim).inImage img)

theorem sliceConcat2_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : SliceConcat2OkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5eab8 - 0x59834))
      ((sliceConcat2Spec M A lim).inImage img) :=
  sub_ok_at_recvCt2 (callee := sliceConcatName)
    (by rw [recvCt2Chunk_fnOff, sliceConcat_fnOff]; rfl) h

theorem sliceConcat3_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : SliceConcat3OkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5eab8 - 0x59834))
      ((sliceConcat3Spec M A lim).inImage img) :=
  sub_ok_at_recvCt2 (callee := sliceConcatName)
    (by rw [recvCt2Chunk_fnOff, sliceConcat_fnOff]; rfl) h

theorem sliceConcat3_xa_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : SliceConcat3OkXA img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5eab8 - 0x59834))
      ((sliceConcat3SpecXA M A lim).inImage img) :=
  sub_ok_at_recvCt2 (callee := sliceConcatName)
    (by rw [recvCt2Chunk_fnOff, sliceConcat_fnOff]; rfl) h

theorem hkdfToSlice_ok_at_recvCt2 {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (h : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5de8c - 0x59834))
      ((withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F))).inImage img) :=
  sub_ok_at_recvCt2 (callee := hkdfToSliceName)
    (by rw [recvCt2Chunk_fnOff, hkdfToSlice_fnOff]; rfl) h

theorem hkdfToSlice_ok_ext_at_recvCt2 {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (h : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5de8c - 0x59834))
      ((withVmPreserved (hkdfToSliceSpecExt (spqrHkdfWith F))).inImage img) :=
  sub_ok_at_recvCt2 (callee := hkdfToSliceName)
    (by rw [recvCt2Chunk_fnOff, hkdfToSlice_fnOff]; rfl) h

theorem authUpdate_ok_at_recvCt2 {img : Obj.Image} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : AuthUpdateOkX img F M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + (0x58ac4#64 - 0x59834#64))
      ((authUpdateSpec F M A lim).inImage img) :=
  sub_ok_at_recvCt2 (callee := authUpdateName)
    (by rw [recvCt2Chunk_fnOff, authUpdate_fnOff]; rfl) h

theorem authUpdate_ok_ext_at_recvCt2 {img : Obj.Image} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : AuthUpdateOkExt img F M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + (0x58ac4#64 - 0x59834#64))
      ((authUpdateSpecExt F M A lim).inImage img) :=
  sub_ok_at_recvCt2 (callee := authUpdateName)
    (by rw [recvCt2Chunk_fnOff, authUpdate_fnOff]; rfl) h

/-- Fixed-offset contract for `alloc::raw_vec::RawVecInner::do_reserve_and_handle [local#7]`
(`0x4dbc4`). -/
def DoReserve7OkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
    ((doReserveSpecX M A lim).inImage img)

theorem doReserve7OkX_of_4k {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A lim ext) :
    DoReserve7OkX img M A lim ext :=
  do_reserve_7_ok_ext_x_4k hA

theorem doReserve7_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : DoReserve7OkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + (0x4dca8#64 - 0x59834#64))
      ((doReserveSpecX M A lim).inImage img) :=
  sub_ok_at_recvCt2 (callee := doReserve7Name)
    (by rw [recvCt2Chunk_fnOff, doReserve7_fnOff_eq]; rfl) h

/-- Fixed-offset contract for
`core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>` (`0x4683c`). -/
def DropSortedSetPt16OkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropSortedSetPt16Name)
    ((dropGlueSortedSetPt16SpecBase M A lim).inImage img)

theorem dropSortedSetPt16_ok_at_recvCt2 {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : DropSortedSetPt16OkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + (0x46920#64 - 0x59834#64))
      ((dropGlueSortedSetPt16SpecBase M A lim).inImage img) := by
  have hrel : (tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropSortedSetPt16Name + BitVec.ofNat 64 77588 :=
    Program.fnAddr_rel (k := 77588) (b := img.base) (X := Rust.withPanics ext)
      libsignalSessionCode_fnOff_0x46920 recvCt2Chunk_fnOff (by decide)
  refine sub_ok_of_addr_eq ?_ h
  rw [hrel, BitVec.add_assoc]; simp

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudget
