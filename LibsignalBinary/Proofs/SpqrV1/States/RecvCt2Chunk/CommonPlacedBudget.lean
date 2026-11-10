/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
public meta import Lean -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux -- shake: keep
public meta import ProofLib.SepLogic.WP.ControlTactics -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudget
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Budget Relocatable Envelopes & Helpers

Intermediate allocation-event envelopes (`RecvCt2PostDecapsEnv`, `RecvCt2PostHmacEnv`,
`RecvCt2PostMacCompareEnv`) and relocatable budget framing helpers for Block `350`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement blkPC_264 blkPC_341 blkPC_379 blkPC_419
  blkPl_264 blkPl_341 blkPl_379 blkPl_419 libsignalMutatedBlocks lsProg_350
  ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (MlKem mlkemDecapsSpec spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks LibsignalCodeRoLoaded extHookStack keys_ls_subroutine_ok_of_block_cro
  sessionMemcpyRegionSpec sessionShimSpec
  subroutine_ok_withStack_of_subroutine_ok withLsCodeRoLoaded withStack
)
open CryptoVerification.SpqrV1.Alloc (
  spqrHandleErrorSym spqrMemcpySym spqrPanicConstAddOverflowSym
  spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym spqr_externAt?_of_mem
  spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.ChainProofs (
  bytesAt_false bytesAt_true hkdfToSliceSpqrSpec
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  onPanic_entails_of_trace_eq withLsCallInv
)
open CryptoVerification.SpqrV1.GF.IsNonZero (isNonZeroSpec)
open CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.States.Leaves (
  of_sepWP_lscro sepWPp_call_frozen subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
  subroutine_ok_withLsCodeRoLoaded_of_plain subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  PolyDecodedMessageCall RecvCt2ChunkGhost SplitBytes recvCt2RoPlacedAt
  spqrAssertFailedU64Sym spqrLibcruxHmacSym' spqrMlkemDecapsSym spqrPanicBoundsCheckSym
  spqrRustDeallocSym' spqrSliceIndexFailSym spqrUnwrapFailedSym stackAt_recvCt2ChunkExt_eq_X
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget allocMemcpyVmSpec
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
  rustCliReallocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetExternSpecWithStack rustCliAllocBudgetSpecWithStack
  rustCliAllocNoOomExternSpecWithStack rustCliAllocNoOomSpecWithStack
  rustCliDeallocBudgetExternSpecWithStack rustCliDeallocBudgetSpecWithStack
  subroutine_ok_rustCliAllocBudget_externWithStack subroutine_ok_rustCliAllocBudget_withStack
  subroutine_ok_rustCliAllocNoOom_externWithStack subroutine_ok_rustCliAllocNoOom_withStack
  subroutine_ok_rustCliDeallocBudget_externWithStack subroutine_ok_rustCliDeallocBudget_withStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  sliceConcat3Spec sliceConcat3SpecXA slice_concat_3_placed_ok slice_concat_3_placed_ok_xa
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  framelessMemcpyAcpSpec framelessMemcpyAcp_of_allocMemcpyVm
  hookMemcpy_framelessMemcpyAcp_ok hookMemcpy_region_ro_trace_ok hookNoop_rustAllocShimVm_ok
  session2MemcpyAcpSpecWithStack session2MemcpyAcpWithStack_of_frameless
  session2ShimAcpSpecWithStack session2ShimAcpWithStack_of_rustAllocShimVm
  sessionMemcpyRegionROSpec sliceConcat2SpecXA slice_concat_2_placed_ok slice_concat_2_placed_ok_xa
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  doReserveSpecX do_reserve_7_placed_ok_x
)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux (
  authUpdateSpec authUpdate_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (
  dropGlueSortedSetPt16Spec drop_glue_sorted_set_pt16_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudget (
  hkdf_to_slice_spqr_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (addChunkSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimBudgetSpec session2MemcpyBudgetSpecX session2ShimBudgetSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
  subroutine_ok_sessionShimBudget_of_rustAllocShimVm
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Re-Exports from `DefsPlacedBudget`, `CommonPlaced`, and `CommonBudget` -/

abbrev recvCt2RoPlacedAt' := @recvCt2RoPlacedAt
alias sckaKeyInfoPrefixSym := DefsPlacedBudget.sckaKeyInfoPrefixSym
alias ctLabelSym := DefsPlacedBudget.ctLabelSym
alias zeros32Sym := DefsPlacedBudget.zeros32Sym
alias rodata_sckaKeyInfoPrefix_placed := DefsPlacedBudget.rodata_sckaKeyInfoPrefix_placed
alias rodata_ctLabel_placed := DefsPlacedBudget.rodata_ctLabel_placed
alias rodata_zeros32_placed' := DefsPlacedBudget.rodata_zeros32_placed'
alias subroutine_ok_withLsCodeRoLoaded_rodata3_keep :=
  DefsPlacedBudget.subroutine_ok_withLsCodeRoLoaded_rodata3_keep

alias PolyDecodedMessageEnv := DefsPlacedBudget.PolyDecodedMessageEnv
alias polyDecodedMessageEnv_nonempty := DefsPlacedBudget.polyDecodedMessageEnv_nonempty
alias recvCt2MacCt2AllocEvents := DefsPlacedBudget.recvCt2MacCt2AllocEvents
alias recvCt2PreAuthUpdateEvents := DefsPlacedBudget.recvCt2PreAuthUpdateEvents
alias recvCt2HmacEvents := DefsPlacedBudget.recvCt2HmacEvents
alias RecvCt2ReserveCt1Env := DefsPlacedBudget.RecvCt2ReserveCt1Env
alias recvCt2ReserveCt1Env_nil := DefsPlacedBudget.recvCt2ReserveCt1Env_nil
alias recvCt2ReserveCt1Env_nonempty := DefsPlacedBudget.recvCt2ReserveCt1Env_nonempty
alias recvCt2ReserveCt1Env_of_doReserve := DefsPlacedBudget.recvCt2ReserveCt1Env_of_doReserve
alias OptSecret32AllocEnv := DefsPlacedBudget.OptSecret32AllocEnv
alias optSecret32AllocEnv_nil := DefsPlacedBudget.optSecret32AllocEnv_nil
alias optSecret32AllocEnv_alloc32 := DefsPlacedBudget.optSecret32AllocEnv_alloc32
alias optSecret32AllocEnv_nonempty := DefsPlacedBudget.optSecret32AllocEnv_nonempty
alias RecvCt2PostDecapsEnv := DefsPlacedBudget.RecvCt2PostDecapsEnv
alias recvCt2PostDecapsEnv_nonempty := DefsPlacedBudget.recvCt2PostDecapsEnv_nonempty
alias RecvCt2TailEnv := DefsPlacedBudget.RecvCt2TailEnv
alias recvCt2TailEnv_nonempty := DefsPlacedBudget.recvCt2TailEnv_nonempty
alias RecvCt2ChunkEnv := DefsPlacedBudget.RecvCt2ChunkEnv
alias recvCt2ChunkEnv_nonempty := DefsPlacedBudget.recvCt2ChunkEnv_nonempty
alias recvCt2ChunkEnv_of_stillReceiving := DefsPlacedBudget.recvCt2ChunkEnv_of_stillReceiving
alias recvCt2ChunkBudgetOnPanic := DefsPlacedBudget.recvCt2ChunkBudgetOnPanic

alias polyDecodedMessagePlacedSpecOfEnv := DefsPlacedBudget.polyDecodedMessagePlacedSpecOfEnv
alias polyDecodedMessagePlacedSpec := DefsPlacedBudget.polyDecodedMessagePlacedSpec
alias PolyDecodedMessagePlacedOkXOfEnv := DefsPlacedBudget.PolyDecodedMessagePlacedOkXOfEnv
alias PolyDecodedMessagePlacedOkX := DefsPlacedBudget.PolyDecodedMessagePlacedOkX
alias polyDecodedMessagePlacedOkX_of_decodedMessage :=
  DefsPlacedBudget.polyDecodedMessagePlacedOkX_of_decodedMessage
alias recvCt2ChunkPlacedSpecOfPrePostEnv := DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv
alias recvCt2ChunkPlacedSpecOfEnv := DefsPlacedBudget.recvCt2ChunkPlacedSpecOfEnv
alias recvCt2ChunkPlacedSpec := DefsPlacedBudget.recvCt2ChunkPlacedSpec
alias RecvCt2ChunkPlacedOkXOfPrePostEnv := DefsPlacedBudget.RecvCt2ChunkPlacedOkXOfPrePostEnv
alias RecvCt2ChunkPlacedOkXOfEnv := DefsPlacedBudget.RecvCt2ChunkPlacedOkXOfEnv
alias RecvCt2ChunkPlacedOkX := DefsPlacedBudget.RecvCt2ChunkPlacedOkX
alias recvCt2ChunkPlacedSpecExtOfPrePostEnv :=
  DefsPlacedBudget.recvCt2ChunkPlacedSpecExtOfPrePostEnv
alias recvCt2ChunkPlacedSpecExtOfEnv := DefsPlacedBudget.recvCt2ChunkPlacedSpecExtOfEnv
alias recvCt2ChunkPlacedSpecExt := DefsPlacedBudget.recvCt2ChunkPlacedSpecExt
alias RecvCt2ChunkPlacedOkExtOfPrePostEnv := DefsPlacedBudget.RecvCt2ChunkPlacedOkExtOfPrePostEnv
alias RecvCt2ChunkPlacedOkExtOfEnv := DefsPlacedBudget.RecvCt2ChunkPlacedOkExtOfEnv
alias RecvCt2ChunkPlacedOkExt := DefsPlacedBudget.RecvCt2ChunkPlacedOkExt
alias withLsCodeRoLoaded_recvCt2ChunkPlacedSpecExtOfPrePostEnv_of_X :=
  DefsPlacedBudget.withLsCodeRoLoaded_recvCt2ChunkPlacedSpecExtOfPrePostEnv_of_X
alias recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX :=
  DefsPlacedBudget.recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX
alias recvCt2ChunkPlacedOkExtOfEnv_of_okX :=
  DefsPlacedBudget.recvCt2ChunkPlacedOkExtOfEnv_of_okX
alias recvCt2ChunkPlacedOkExt_of_okX := DefsPlacedBudget.recvCt2ChunkPlacedOkExt_of_okX
alias polyDecodedMessagePlacedOfEnv_on := DefsPlacedBudget.polyDecodedMessagePlacedOfEnv_on
alias polyDecodedMessagePlaced_on := DefsPlacedBudget.polyDecodedMessagePlaced_on
alias recvCt2ChunkPlacedOfPrePostEnv_on := DefsPlacedBudget.recvCt2ChunkPlacedOfPrePostEnv_on
alias recvCt2ChunkPlaced_on := DefsPlacedBudget.recvCt2ChunkPlaced_on
alias recvCt2ChunkPlacedExt_on := DefsPlacedBudget.recvCt2ChunkPlacedExt_on

abbrev onPanic_false_entails_recvCt2 := @CommonBudgetAux.onPanic_false_entails_recvCt2
abbrev onPanic_pure_entails_recvCt2 := @CommonBudgetAux.onPanic_pure_entails_recvCt2
abbrev onPanic_budget_entails_recvCt2 := @CommonBudgetAux.onPanic_budget_entails_recvCt2
abbrev onPanic_hmac_budget_entails_recvCt2 := @CommonBudgetAux.onPanic_hmac_budget_entails_recvCt2
abbrev allowPanic_isPanic_budget_recvCt2 := @CommonBudgetAux.allowPanic_isPanic_budget_recvCt2

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

abbrev libcruxHmacSafeBudgetSpec := @CommonBudget.libcruxHmacSafeBudgetSpec
abbrev subroutine_ok_libcruxHmacSafeBudget_of_budget :=
  @CommonBudget.subroutine_ok_libcruxHmacSafeBudget_of_budget
abbrev isNonZero_vm_placed_ok := @CommonBudget.isNonZero_vm_placed_ok

/-! ## Relocatable Postcondition Abbreviations & Stack-Frame Lift -/

/-- Two-envelope (`PreEnv` / `PostEnv`) normal-return `SepWPp` postcondition predicate for
Block `350` segments (`recvCt2ChunkStackX = 19552`B). -/
abbrev recvCt2PlacedPostQOfPrePostEnv [LibsignalPlacement] (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop)
    (x : RecvCt2ChunkGhost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (recvCt2RoPlacedAt ∗
          (DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim
            PreEnv PostEnv).post (x, st) s0 sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Envelope-parametric normal-return `SepWPp` postcondition predicate for Block `350` segments
(`recvCt2ChunkStackX = 19552`B). -/
abbrev recvCt2PlacedPostQOfEnv [LibsignalPlacement] (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : RecvCt2ChunkGhost F → List AllocEvent → Prop)
    (x : RecvCt2ChunkGhost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  recvCt2PlacedPostQOfPrePostEnv K F M A lim Env Env x st s0 R

/-- Canonical normal-return `SepWPp` postcondition predicate for Block `350` segments
(`recvCt2ChunkStackX = 19552`B). -/
abbrev recvCt2PlacedPostQ [LibsignalPlacement] (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : RecvCt2ChunkGhost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  recvCt2PlacedPostQOfEnv K F M A lim DefsPlacedBudget.RecvCt2ChunkEnv x st s0 R

/-- Two-envelope (`PreEnv` / `PostEnv`) contract-backed normal-return `SepWPp` postcondition
predicate for Block `350` segments (`recvCt2ChunkStackExt = 20272`B). -/
abbrev recvCt2PlacedPostQExtOfPrePostEnv [LibsignalPlacement] (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop)
    (x : RecvCt2ChunkGhost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (recvCt2RoPlacedAt ∗
          (DefsPlacedBudget.recvCt2ChunkPlacedSpecExtOfPrePostEnv K F M A lim
            PreEnv PostEnv).post (x, st) s0 sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Envelope-parametric contract-backed normal-return `SepWPp` postcondition predicate for
Block `350` segments (`recvCt2ChunkStackExt = 20272`B). -/
abbrev recvCt2PlacedPostQExtOfEnv [LibsignalPlacement] (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : RecvCt2ChunkGhost F → List AllocEvent → Prop)
    (x : RecvCt2ChunkGhost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  recvCt2PlacedPostQExtOfPrePostEnv K F M A lim Env Env x st s0 R

/-- Canonical contract-backed normal-return `SepWPp` postcondition predicate for Block `350`
segments (`recvCt2ChunkStackExt = 20272`B). -/
abbrev recvCt2PlacedPostQExt [LibsignalPlacement] (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : RecvCt2ChunkGhost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  recvCt2PlacedPostQExtOfEnv K F M A lim DefsPlacedBudget.RecvCt2ChunkEnv x st s0 R

/-- Panic `SepWPp` postcondition predicate for Block `350` segments (shared across `X` and `Ext`
stack budgets). -/
abbrev recvCt2PlacedPostQp {F : ShaCompress} (K : MlKem)
    (x : RecvCt2ChunkGhost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ DefsPlacedBudget.recvCt2ChunkBudgetOnPanic K x s0 sf ∗ R)

/-- Frame the bottom `720` stack bytes `memRegion (s0.sp - 20272#64) 720` out of a terminal
relocatable `SepWPp` segment proved against `recvCt2PlacedPostQOfPrePostEnv` (`19552`B) to obtain
`recvCt2PlacedPostQExtOfPrePostEnv` (`20272`B). -/
theorem sepWPp_frame_recvCt2_placed_budget_ext [LibsignalPlacement] {prog : Program}
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {x : RecvCt2ChunkGhost F} {st : M.σ} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .x30) s P
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st s0
        (memRegion (s0.sp - 20272#64) 720 ∗ R))
      (recvCt2PlacedPostQp K x s0
        (memRegion (s0.sp - 20272#64) 720 ∗ R))) :
    SepWPp prog (s0.readReg64 .x30) s (P ∗ memRegion (s0.sp - 20272#64) 720)
      (recvCt2PlacedPostQExtOfPrePostEnv K F M A lim PreEnv PostEnv x st s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  intro R_in hmem hcode
  have hmem' : s.mem ⊨ P ∗ (memRegion (s0.sp - 20272#64) 720 ∗ R_in) := by
    simpa only [sepConj_assoc] using hmem
  obtain ⟨sf, hsteps, hout⟩ := h (memRegion (s0.sp - 20272#64) 720 ∗ R_in) hmem' hcode
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hPf_in, ⟨hQ, hsp, hcs⟩⟩ | ⟨hpan, P_f, hPf_in, hQp⟩ | ⟨_, hfalse⟩
  · refine Or.inl ⟨hpc, hrun, P_f ∗ memRegion (s0.sp - 20272#64) 720, ?_, ?_⟩
    · simpa only [sepConj_assoc] using hPf_in
    · refine ⟨fun hPf_R => ?_, hsp, hcs⟩
      have hPf_R' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 20272#64) 720 ∗ R) := by
        simpa only [sepConj_assoc] using hPf_R
      have hpost := hQ hPf_R'
      dsimp only [recvCt2PlacedPostQOfPrePostEnv, DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv,
        DefsBudget.recvCt2ChunkPlacedSpecOfPrePostEnv] at hpost
      dsimp only [recvCt2PlacedPostQExtOfPrePostEnv,
        DefsPlacedBudget.recvCt2ChunkPlacedSpecExtOfPrePostEnv]
      simp only [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      rw [stackAt_recvCt2ChunkExt_eq_X s0.sp]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, P_f ∗ memRegion (s0.sp - 20272#64) 720, ?_, ?_⟩)
    · simpa only [sepConj_assoc] using hPf_in
    · intro hPf_R
      have hPf_R' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 20272#64) 720 ∗ R) := by
        simpa only [sepConj_assoc] using hPf_R
      have hpan_post := hQp hPf_R'
      dsimp only [recvCt2PlacedPostQp, DefsPlacedBudget.recvCt2ChunkBudgetOnPanic,
        DefsBudget.recvCt2ChunkBudgetOnPanic] at hpan_post ⊢
      have harrange :
          (⌜(x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∧ s0.trace <+: sf.trace⌝ ∗
            anyHeap) ∗ (memRegion (s0.sp - 20272#64) 720 ∗ R) =
          (⌜(x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∧ s0.trace <+: sf.trace⌝ ∗
            (anyHeap ∗ memRegion (s0.sp - 20272#64) 720)) ∗ R := by sep_ac_rfl
      rw [harrange] at hpan_post
      exact Satisfies.mono
        (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) hpan_post
  · exact (not_satisfies_false_sepConj hfalse).elim

/-! ## `LibsignalCodeRoLoaded`-Preserving `SepWPp` Sequencing and Budget Call Tactic -/

theorem sepWPp_of_sepWP_lscro {prog : Program} {pl : Arm64.Obj.MultiPlacement}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp}
    {post postPanic : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWPp prog target_pc sm Pm post postPanic)) :
    SepWPp prog target_pc s P post postPanic :=
  of_sepWP_lscro hinv h

/-- Absorb a spatial frame `F_frame` into a panic postcondition ending in `∗ anyHeap`. -/
theorem anyHeap_absorb_right (P F_frame : SepProp) :
    (P ∗ anyHeap) ∗ F_frame ⊢ P ∗ anyHeap := by
  rw [sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap (anyHeap ∗ F_frame))

/-- Mid-function `SepWPp` call rule for `withLsCodeRoLoaded pl spec` with general panic
postcondition `Qpan sf`. -/
theorem call_allowPanic_lscro_recvCt2 {α : Type} {prog : Program}
    {pl : Arm64.Obj.MultiPlacement} {entry ret_pc target_pc : BitVec 64}
    {spec : Spec α} {x : α} {F_frame R : SepProp}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {Qpan : State → SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hinv : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F_frame ∗ R')))
    (hpanic : ∀ sf, spec.onPanic x s sf ∗ F_frame ⊢ Qpan sf)
    (herr : (∀ sf code, spec.onExit x code s sf = ⌜False⌝) ∧
            (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F_frame) Q
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hinv hcall
    (x := x) (F := F_frame) hpc hrun hsp hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm (spec.pre x s), satisfies_pure_sepConj]
    exact ⟨hinv, hpre R' hm⟩
  · intro sf code R' _ hex
    dsimp only [withLsCodeRoLoaded] at hex
    rw [herr.1 sf code, satisfies_pure_sepConj] at hex
    exact hex.1
  · intro sf _ hmem
    dsimp only [withLsCodeRoLoaded] at hmem
    exact Satisfies.mono (sepConj_mono_left (hpanic sf)) hmem
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf
    exact hnext sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf
  · intro sf R' _ hoom_m
    dsimp only [withLsCodeRoLoaded] at hoom_m
    rw [herr.2 sf, satisfies_pure_sepConj] at hoom_m
    exact False.elim hoom_m.1

/-- Specialization of `call_allowPanic_lscro_recvCt2` to panic postconditions of shape
`⌜φ sf⌝ ∗ anyHeap` (such as `recvCt2ChunkBudgetOnPanic`). -/
theorem call_allowPanic_lscro_recvCt2_pure {α : Type} {prog : Program}
    {pl : Arm64.Obj.MultiPlacement} {entry ret_pc target_pc : BitVec 64}
    {spec : Spec α} {x : α} {F_frame R : SepProp}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop} {φ : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hinv : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F_frame ∗ R')))
    (hpanic : ∀ sf, spec.onPanic x s sf ∗ F_frame ⊢ ⌜φ sf⌝ ∗ anyHeap)
    (herr : (∀ sf code, spec.onExit x code s sf = ⌜False⌝) ∧
            (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F_frame) Q
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ (⌜φ sf'⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜φ sf⌝ ∗ anyHeap) ∗ R)) :=
  call_allowPanic_lscro_recvCt2 hcall hinv hpc hrun hsp hlr hpre hpanic herr hnext

open Lean Elab Tactic Meta in
/-- Relocatable counterpart of `wpp_call_inImage_recvCt2_budget`: discharges a mid-function call
to `hcall : subroutine_ok _ _ (withLsCodeRoLoaded lsmpl spec)` with ghost argument `a` and
`hinv : LibsignalCodeRoLoaded lsmpl s.mem`, handling `onPanic = ⌜False⌝` and budget-form
`recvCt2ChunkBudgetOnPanic` uniformly. -/
elab "wpp_call_lscro_recvCt2_budget " hcall:term:max a:term:max hinv:term:max : tactic => do
  let hcallCopyId ← freshIdent `hcall_copy
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    have $hcallCopyId := $hcall
    apply (call_allowPanic_lscro_recvCt2 $hcallCopyId (x := $a) $hinv)
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_lscro_recvCt2_budget: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    try dsimp only [withVmPreserved, withStack]
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcallCopyId)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (
      try dsimp only [withVmPreserved, withStack,
        DefsPlacedBudget.recvCt2ChunkBudgetOnPanic, DefsBudget.recvCt2ChunkBudgetOnPanic]
      wp_unfold_specs; intro _; first
      | exact CommonBudgetAux.onPanic_budget_entails_recvCt2 (by wp_norm_lhs)
      | exact CommonBudgetAux.onPanic_pure_entails_recvCt2 (by wp_norm_lhs)
      | exact onPanic_entails_of_trace_eq (by wp_norm_lhs)
      | exact Entails.pure_left False.elim
      | (repeat rw [sepConj_assoc]; exact Entails.pure_left False.elim)
      | (repeat rw [← sepConj_assoc]; exact Entails.pure_left False.elim))
    wp_focus_close (try dsimp only [withVmPreserved, withStack]; wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    try clear $hcallCopyId
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  )))
  foldStructEtaTarget
  for _ in [:2] do
    let mvarId ← getMainGoal
    let ref ← IO.mkRef #[]
    mvarId.withContext do
      let ty ← instantiateMVars (← mvarId.getType)
      ty.forEach fun sub => do
        if sub.isConst then
          let nm := sub.constName!
          if nm != ``Arm64.Spec.mk && nm != ``Arm64.Spec.inImage &&
              nm != ``withLsCodeRoLoaded &&
              nm != ``CryptoVerification.withLsCodeLoaded then
            let subTy ← inferType sub
            if subTy.getForallBody.isAppOf ``Arm64.Spec then
              let arr ← ref.get
              if !arr.any (fun i => i.getId == nm) then
                ref.set (arr.push (mkIdent nm))
    let ids ← ref.get
    for id in ids do
      let _ ← tryTactic (evalTactic (← `(tactic| dsimp only [$id:ident])))
  let _ ← tryTactic (evalTactic (← `(tactic| dsimp only)))
  for hId in [hspId, hcsId] do
    let _ ← tryTactic (evalTactic (← `(tactic| dsimp only at $hId:ident)))
    let _ ← tryTactic (evalTactic (← `(tactic|
      simp (config := { decide := true }) only [
        ← disjointRegions_iff_disjoint64,
        ← disjointRegions_iff_disjoint128,
        Arm64.CalleeSavedPreserved,
        wp_norm, arm64_norm] at $hId:ident)))
  let mut worklist : List Ident := [hspId, hcsId]
  while !worklist.isEmpty do
    let currId :: rest := worklist | break
    worklist := rest
    let mvarId ← getMainGoal
    let lctx ← mvarId.withContext getLCtx
    if let some decl := lctx.findFromUserName? currId.getId then
      let ty ← mvarId.withContext (instantiateMVars decl.type)
      if ty.isAppOfArity ``And 2 then
        let h1 ← freshIdent `h
        if ← tryTactic (evalTactic (← `(tactic| rcases $currId:ident with ⟨$h1:ident, $currId:ident⟩))) then
          worklist := h1 :: currId :: worklist
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))

/-! ## `SplitBytes` `VmPreserved` Memcpy Bridges for `withLsCodeRoLoaded` -/

theorem splitBytes_memcpyVm_withStack_lscro_ok {pl : Arm64.Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64) (hookStack : Nat)
    (hmc : subroutine_ok prog entry (withStack sessionMemcpyRegionBudgetSpec hookStack)) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded pl (withStack (DefsBudget.SplitBytes.memcpyVmSpec S) hookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (CommonBudgetAux.SplitBytes.memcpyVm_withStack_ok S hn hookStack hmc)

theorem splitBytes_memcpyVmOuter_withStack_lscro_ok {pl : Arm64.Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64}
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64) (hookStack : Nat)
    (hmc : subroutine_ok prog entry (withStack sessionMemcpyRegionBudgetSpec hookStack)) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded pl (withVmPreserved (withStack S.memcpySpec hookStack))) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_plain
  have h := CommonBudgetAux.SplitBytes.memcpyVm_withStack_ok S hn hookStack hmc
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved, withStack, DefsBudget.SplitBytes.memcpyVmSpec] at hq ⊢
  simpa only [sepConj_assoc] using hq

/-! ## Budget Hook Bundle (`RecvCt2PlacedAlloc`) and Cross-Block Callee Bridges -/

abbrev hookNoop_rustAllocShimVm_ok' := @hookNoop_rustAllocShimVm_ok
abbrev hookMemcpy_framelessMemcpyAcp_ok' := @hookMemcpy_framelessMemcpyAcp_ok
abbrev hookMemcpy_region_ro_trace_ok' := @hookMemcpy_region_ro_trace_ok
abbrev framelessMemcpyAcp_of_allocMemcpyVm' := @framelessMemcpyAcp_of_allocMemcpyVm

theorem hookSat_noAllocShim_of_rustAllocShimVm {hooks : String → Option (State → State)}
    {name : String} (h : HookSat hooks name rustAllocShimVmSpec) :
    HookSat hooks name noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocShimVmSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1.2.1, hpost.1.2⟩, hpost.2⟩
  · exact Or.inr hrest

theorem hookSat_framelessMemcpyAcp_of_allocMemcpyVm {hooks : String → Option (State → State)}
    {name : String} (h : HookSat hooks name allocMemcpyVmSpec) :
    HookSat hooks name framelessMemcpyAcpSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  dsimp only [framelessMemcpyAcpSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hpre' : s0.mem ⊨ allocMemcpyVmSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [allocMemcpyVmSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hsat (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocMemcpyVmSpec, framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

theorem withStack_sessionShimVm_of_rustAllocShimVm {prog : Program} {entry : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog entry rustAllocShimVmSpec) :
    subroutine_ok prog entry (withStack (withVmPreserved sessionShimSpec) hookStack) :=
  subroutine_ok_withStack_of_subroutine_ok
    (subroutine_ok_sessionShimBudget_of_rustAllocShimVm h) hookStack

theorem session2ShimBudgetX_of_rustAllocShimVm {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry rustAllocShimVmSpec) :
    subroutine_ok prog entry session2ShimBudgetSpecX := by
  have h' := session2ShimAcpWithStack_of_rustAllocShimVm extHookStack h
  refine subroutine_ok_mono h' (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [session2ShimAcpSpecWithStack, session2ShimBudgetSpecX] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.2⟩, hq.2⟩

theorem subroutine_ok_sessionMemcpyRegionBudget_of_framelessAcp {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry framelessMemcpyAcpSpec) :
    subroutine_ok prog entry sessionMemcpyRegionBudgetSpec := by
  refine subroutine_ok_mono h
    (fun ⟨dst, src, bs⟩ R s0 hp => by
      dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
        framelessMemcpyAcpSpec] at hp ⊢
      simpa only [sepConj_assoc] using hp)
    (fun ⟨dst, src, bs⟩ R s0 sf hq => by
      dsimp only [framelessMemcpyAcpSpec, sessionMemcpyRegionBudgetSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec] at hq ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.2.2, ⟨hq.1.1, hq.1.2.1.2.1⟩, hq.2⟩)

theorem withStack_sessionMemcpyRegionBudget_of_framelessAcp {prog : Program} {entry : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog entry framelessMemcpyAcpSpec) :
    subroutine_ok prog entry (withStack sessionMemcpyRegionBudgetSpec hookStack) :=
  subroutine_ok_withStack_of_subroutine_ok
    (subroutine_ok_sessionMemcpyRegionBudget_of_framelessAcp h) hookStack

theorem session2MemcpyBudgetX_of_framelessAcp {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry framelessMemcpyAcpSpec) :
    subroutine_ok prog entry session2MemcpyBudgetSpecX := by
  have h' := session2MemcpyAcpWithStack_of_frameless extHookStack h
  refine subroutine_ok_mono h' (fun _ _ _ hp => hp) (fun ⟨dst, src, bs⟩ R s0 sf hq => ?_)
  dsimp only [session2MemcpyAcpSpecWithStack, session2MemcpyBudgetSpecX] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, hq.1.2.1.2.1, hq.1.2.2⟩, hq.2⟩

/-- Budget-threaded allocator, `memcpy`, and panic hypotheses on `Rust.withPanics ext` for
Block `350` (`<EkSentCt1Received>::recv_ct2_chunk`). -/
structure RecvCt2PlacedAlloc [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  handleError : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked
  assertFailedU64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked
  sliceIndexFail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked
  unwrapFailed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked
  panicBoundsCheck : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked
  panicConstAddOverflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  allocZeroed :
    HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustCliAllocBudgetSpec M A lim true)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustCliDeallocBudgetSpec M A lim)
  realloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)
  memcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec
  memcpyRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec

theorem RecvCt2PlacedAlloc.panic_handle_error [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem (hi := hi) (hunmut := hunmut)).trans hA.handleError

theorem RecvCt2PlacedAlloc.panic_assert_failed_u64 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrAssertFailedU64Sym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.assertFailedU64

theorem RecvCt2PlacedAlloc.panic_slice_index_fail [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrSliceIndexFailSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.sliceIndexFail

theorem RecvCt2PlacedAlloc.panic_unwrap_failed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrUnwrapFailedSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.unwrapFailed

theorem RecvCt2PlacedAlloc.panic_bounds_check [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrPanicBoundsCheckSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.panicBoundsCheck

theorem RecvCt2PlacedAlloc.panic_add_overflow [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    (lsProg_350 (Rust.withPanics ext)).externAt? (lsρ spqrPanicConstAddOverflowSym) =
      some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.panicConstAddOverflow

theorem RecvCt2PlacedAlloc.shim_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)] (hookStack : Nat)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustNoAllocShimSym)
      (withStack (withVmPreserved sessionShimSpec) hookStack) :=
  withStack_sessionShimVm_of_rustAllocShimVm hookStack
    (spqr_hook_ok_of_mem hA.shim (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.shim_withStack_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustNoAllocShimSym)
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (hA.shim_at_block extHookStack)

theorem RecvCt2PlacedAlloc.shim_acp_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustNoAllocShimSym)
      (withLsCodeRoLoaded lsmpl (session2ShimAcpSpecWithStack extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2ShimAcpWithStack_of_rustAllocShimVm extHookStack
      (spqr_hook_ok_of_mem hA.shim))

theorem RecvCt2PlacedAlloc.shim_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustNoAllocShimSym)
      (withLsCodeRoLoaded lsmpl session2ShimBudgetSpecX) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2ShimBudgetX_of_rustAllocShimVm (spqr_hook_ok_of_mem hA.shim))

theorem RecvCt2PlacedAlloc.memcpy_region_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)] (hookStack : Nat)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrMemcpySym)
      (withStack sessionMemcpyRegionBudgetSpec hookStack) :=
  withStack_sessionMemcpyRegionBudget_of_framelessAcp hookStack
    (spqr_hook_ok_of_mem hA.memcpy (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.memcpy_region_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    (hookStack : Nat := extHookStack) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrMemcpySym)
      (withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec hookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (hA.memcpy_region_at_block hookStack)

theorem RecvCt2PlacedAlloc.memcpy_splitBytes_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {n : Nat} {P : BitVec 64 → SepProp} (S : SplitBytes n P) (hn : n < 2 ^ 64)
    (hookStack : Nat) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrMemcpySym)
      (withLsCodeRoLoaded lsmpl (withStack (DefsBudget.SplitBytes.memcpyVmSpec S) hookStack)) :=
  splitBytes_memcpyVm_withStack_lscro_ok S hn hookStack
    (hA.memcpy_region_at_block hookStack)

theorem RecvCt2PlacedAlloc.memcpy_acp_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrMemcpySym)
      (withLsCodeRoLoaded lsmpl (session2MemcpyAcpSpecWithStack extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2MemcpyAcpWithStack_of_frameless extHookStack
      (spqr_hook_ok_of_mem hA.memcpy))

theorem RecvCt2PlacedAlloc.memcpy_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrMemcpySym)
      (withLsCodeRoLoaded lsmpl session2MemcpyBudgetSpecX) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (session2MemcpyBudgetX_of_framelessAcp (spqr_hook_ok_of_mem hA.memcpy))

theorem RecvCt2PlacedAlloc.alloc_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpecWithStack M A lim false extHookStack) :=
  subroutine_ok_rustCliAllocBudget_withStack (by decide) (by decide)
    (spqr_hook_ok_of_mem hA.alloc (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.alloc_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustAllocSym)
      (withLsCodeRoLoaded lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain hA.alloc_at_block

theorem RecvCt2PlacedAlloc.alloc_extern_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustAllocSym)
      (withLsCodeRoLoaded lsmpl
        (rustCliAllocBudgetExternSpecWithStack M A lim false extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (subroutine_ok_rustCliAllocBudget_externWithStack (by decide) (by decide)
      (spqr_hook_ok_of_mem hA.alloc))

theorem RecvCt2PlacedAlloc.allocNoOom_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustAllocSym)
      (rustCliAllocNoOomSpecWithStack M A lim false extHookStack) :=
  subroutine_ok_rustCliAllocNoOom_withStack (by decide) (by decide)
    (subroutine_ok_allocNoOom_of_budget
      (spqr_hook_ok_of_mem hA.alloc (hi := hi) (hunmut := hunmut)))

theorem RecvCt2PlacedAlloc.allocNoOom_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustAllocSym)
      (withLsCodeRoLoaded lsmpl (rustCliAllocNoOomSpecWithStack M A lim false extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain hA.allocNoOom_at_block

theorem RecvCt2PlacedAlloc.allocNoOom_extern_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustAllocSym)
      (withLsCodeRoLoaded lsmpl
        (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (spqr_hook_ok_of_mem hA.alloc)))

theorem RecvCt2PlacedAlloc.allocZeroed_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustAllocZeroedSym)
      (rustCliAllocBudgetSpecWithStack M A lim true extHookStack) :=
  subroutine_ok_rustCliAllocBudget_withStack (by decide) (by decide)
    (spqr_hook_ok_of_mem hA.allocZeroed (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.allocZeroed_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustAllocZeroedSym)
      (withLsCodeRoLoaded lsmpl (rustCliAllocBudgetSpecWithStack M A lim true extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain hA.allocZeroed_at_block

theorem RecvCt2PlacedAlloc.allocZeroedNoOom_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustAllocZeroedSym)
      (rustCliAllocNoOomSpecWithStack M A lim true extHookStack) :=
  subroutine_ok_rustCliAllocNoOom_withStack (by decide) (by decide)
    (subroutine_ok_allocNoOom_of_budget
      (spqr_hook_ok_of_mem hA.allocZeroed (hi := hi) (hunmut := hunmut)))

theorem RecvCt2PlacedAlloc.allocZeroedNoOom_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustAllocZeroedSym)
      (withLsCodeRoLoaded lsmpl (rustCliAllocNoOomSpecWithStack M A lim true extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain hA.allocZeroedNoOom_at_block

theorem RecvCt2PlacedAlloc.dealloc_budget_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustDeallocSym')
      (rustCliDeallocBudgetSpecWithStack M A lim extHookStack) :=
  subroutine_ok_rustCliDeallocBudget_withStack (by decide) (by decide)
    (spqr_hook_ok_of_mem hA.dealloc (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.dealloc_budget_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustDeallocSym')
      (withLsCodeRoLoaded lsmpl (rustCliDeallocBudgetSpecWithStack M A lim extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain hA.dealloc_budget_at_block

theorem RecvCt2PlacedAlloc.dealloc_at_block [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ spqrRustDeallocSym')
      (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack) :=
  subroutine_ok_rustCliDeallocBudget_externWithStack (by decide) (by decide)
    (spqr_hook_ok_of_mem hA.dealloc (hi := hi) (hunmut := hunmut))

theorem RecvCt2PlacedAlloc.dealloc_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrRustDeallocSym')
      (withLsCodeRoLoaded lsmpl
        (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain hA.dealloc_at_block

theorem mlkem_decaps_placed_lscro [LibsignalPlacement] {K : MlKem}
    {ext : String → Option (State → State)}
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K))) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrMlkemDecapsSym)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (mlkemDecapsSpec K))) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (spqr_hook_ok_of_mem hdecaps)

theorem libcrux_hmac_placed_lscro [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrLibcruxHmacSym')
      (withLsCodeRoLoaded lsmpl (libcruxHmacBudgetSpec F M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (spqr_hook_ok_of_mem hhmac)

theorem libcrux_hmac_safe_placed_lscro [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsρ spqrLibcruxHmacSym')
      (withLsCodeRoLoaded lsmpl (CommonBudget.libcruxHmacSafeBudgetSpec F M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (CommonBudget.subroutine_ok_libcruxHmacSafeBudget_of_budget (spqr_hook_ok_of_mem hhmac))

theorem addChunk_placed_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hadd : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (CryptoVerification.withLsCodeLoaded lsmpl (addChunkSpecX M A lim))) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 419)
      (withLsCodeRoLoaded lsmpl (addChunkSpecX M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 419) hadd)

theorem polyDecodedMessageOfEnv_placed_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : PolyDecodedMessageCall → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdec : DefsPlacedBudget.PolyDecodedMessagePlacedOkXOfEnv M A lim Env ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl (DefsPlacedBudget.polyDecodedMessagePlacedSpecOfEnv M A lim Env)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 350) (j := 418) hdec

theorem polyDecodedMessage_placed_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec : DefsPlacedBudget.PolyDecodedMessagePlacedOkX M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl (DefsPlacedBudget.polyDecodedMessagePlacedSpec M A lim)) :=
  polyDecodedMessageOfEnv_placed_lscro hdec

theorem RecvCt2PlacedAlloc.sliceConcat2_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 386)
      (withLsCodeRoLoaded lsmpl (sliceConcat2Spec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_2_placed_ok hA.shim hA.alloc hA.memcpy hA.memcpyRO)))

theorem RecvCt2PlacedAlloc.sliceConcat2_xa_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 386)
      (withLsCodeRoLoaded lsmpl (sliceConcat2SpecXA M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_2_placed_ok_xa hA.shim hA.alloc hA.memcpy hA.memcpyRO)))

theorem RecvCt2PlacedAlloc.sliceConcat3_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 386)
      (withLsCodeRoLoaded lsmpl (sliceConcat3Spec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_3_placed_ok hA.shim hA.alloc hA.memcpy hA.memcpyRO)))

theorem RecvCt2PlacedAlloc.sliceConcat3_xa_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 386)
      (withLsCodeRoLoaded lsmpl (sliceConcat3SpecXA M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 386)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (slice_concat_3_placed_ok_xa hA.shim hA.alloc hA.memcpy hA.memcpyRO)))

theorem hkdfToSlice_placed_lscro [LibsignalPlacement] {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F))))) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))) :=
  keys_ls_subroutine_ok_of_block_cro (i := 350) (j := 379) hhkdf

/-- Pure `Crypto` bundle carrying `F : ShaCompress` so `hkdf_to_slice_spqr_placed_ok`
instantiates without requiring AES or X25519 parameters. -/
abbrev cryptoOfShaCompress (F : ShaCompress) : Crypto where
  F := F
  E := fun _ b => b
  D := fun _ b => b
  X := fun _ k => k
  pubKey := fun k => k

theorem hkdfToSlice_placed_ok_of_hooks [LibsignalPlacement] (F : ShaCompress)
    {ext : String → Option (State → State)} [HkdfPlacedHooks F (Rust.withPanics ext)] :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))) :=
  hkdf_to_slice_spqr_placed_ok (cryptoOfShaCompress F)

theorem RecvCt2PlacedAlloc.authUpdate_lscro [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext)
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F))))) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec F M A lim)) := by
  have hconcat_341 : subroutine_ok ((blkPC_341).rebase (blkPl_341).base (Rust.withPanics ext))
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (ls_subroutine_ok_of_block (i := 341) (j := 386)
          (subroutine_ok_withLsCodeLoaded_of_plain
            (slice_concat_2_placed_ok hA.shim hA.alloc hA.memcpy hA.memcpyRO))))
  have hhkdf_341 : subroutine_ok ((blkPC_341).rebase (blkPl_341).base (Rust.withPanics ext))
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (keys_ls_subroutine_ok_of_block_cro (i := 341) (j := 379) hhkdf)
  have hupd_341 :=
    authUpdate_placed_ok hconcat_341 hhkdf_341
      (hA.shim_at_block extHookStack)
      hA.alloc_at_block
      hA.allocZeroed_at_block
      hA.dealloc_budget_at_block
  exact keys_ls_subroutine_ok_of_block_cro (i := 350) (j := 341)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hupd_341)

theorem RecvCt2PlacedAlloc.doReserve7_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 320)
      (withLsCodeRoLoaded lsmpl (doReserveSpecX M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 320)
      (do_reserve_7_placed_ok_x hA.handleError
        (hookSat_noAllocShim_of_rustAllocShimVm hA.shim) hA.alloc hA.realloc))

theorem isNonZero_placed_lscro [LibsignalPlacement] (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 380)
      (withLsCodeRoLoaded lsmpl (withVmPreserved isNonZeroSpec)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 380)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (CommonBudget.isNonZero_vm_placed_ok (Rust.withPanics ext))))

theorem RecvCt2PlacedAlloc.dropSortedSetPt16_lscro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : RecvCt2PlacedAlloc M A lim ext) :
    subroutine_ok (lsProg_350 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeRoLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (i := 350) (j := 264)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_sorted_set_pt16_placed_ok
          (spqr_hook_ok_of_mem hA.dealloc))))

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
