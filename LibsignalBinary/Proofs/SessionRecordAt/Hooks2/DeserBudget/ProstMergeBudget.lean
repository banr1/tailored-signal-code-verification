/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public meta import ProofLib -- shake: keep
public meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstVarintVm
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExt
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsW
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.VarintBridge

/-!
# Budget-Threaded `do_reserve_and_handle`, `bytesVtableDrop`, and `bytes::merge`

Proves relocatable `[LibsignalPlacement]` total-correctness (`onPanic := ⌜False⌝`,
`onOom := ⌜False⌝`) contracts under `AllocContractsBudgetPlaced`:
1. `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle` (Block `13`);
2. `bytes::bytes::{static_drop, promotable_even_drop, promotable_odd_drop}` `.rodata` vtable
   dispatch (Blocks `224, 237, 236`);
3. `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]` (Block `7`), crediting
   temporary `Bytes` buffer deallocation while requiring `FitsEvents` only on `bytesMergeAllocEvents`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg LibsignalCodeLoaded LibsignalRoLoaded
  libsignalRoLoaded_of_keepsFrozen withLsCodeLoaded withLsCl extract_withLsCodeLoaded
  lsmpl lsρ
  lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_subroutine_ok_of_block subroutine_ok_withLsCodeLoaded_of_plain
  blkPC_7 blkPl_7 blkPC_13 blkPl_13 blkPC_45 blkPl_45
  blkPC_224 blkPl_224 blkPC_236 blkPl_236 blkPC_237 blkPl_237 blkPC_250 blkPl_250
)
open CryptoVerification.RustHeap (
  RustAlloc vecU8At vecHeader LayoutOk
)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarintAux mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall DoReserveCall reserveCap
  extHookStack withLsCodeRoLoaded extract_withLsCodeRoLoaded
  ls_subroutine_ok_cl_of_callee ls_subroutine_ok_of_callee
  bytesStaticDropSpec bytesFromVecPlacedSpec bytesFromVecStack
  bytesPlacedAt bytesHeader bytesBoxU8Buf bytesPlacedVtable bytesPlacedDropFnAddr
  bytesPtr bytesData lsBytesRustDeallocSym getLsbD_zero_iff
  varintSlow
)
open CryptoVerification.LibsignalTripleRatchet.VarintBridge (varintSlow_some_iff)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeGhost DecodeVarintSliceGhost
  sliceCursorAt sliceCursorAfter VarintSlicePre varintSlow_none_iff
  bmTotalStack bmSliceStack bmExtraStack stackAt_sliceGen_split stackAt_split_sub
  stackAt_bytesMergeGen_entry fold_stackAt_bytesMergeGen savedRegsStack
  bm_HighCalleeSaved spAligned_sub_224
  bm_vecU8Buf bm_vecU8At_eq_header_sep_buf fold_vecU8At_clear vecU8At_nil_eq
  bytesBoxU8Buf_nonempty fold_bytesBoxU8Buf_nonempty fold_vecU8Buf_nonempty fold_vecU8At_copied
  unfold_bytesPlacedAt_sp112 unfold_vecHeader_sp136 fold_vecU8At_sp136
  memRegion_104_unfold memRegion_104_fold
  bytesMutDataWord bytesMutDataWord_zero bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5
  bitvec_ult_zero bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32
  bitvec_getLsbD_63_of_lt32 bitvec_sub_self_64 bitvec_if_zero_ult_self
  vecU8Buf_nil_one sliceCursorAfter_split_copy sliceCursorAfter_advance_fold
  bm_decodeVarint_suffix mergeBytes_lengthDelimited_ok
  mergeBytes_lengthDelimited_underflow mergeBytes_of_decodeVarint_none
  mergeBytes_ne_lengthDelimited mergeBytes_nil
  decodeVarint_cons_of_signExtend_63_false fold_sliceCursorAfter_cons
  fold_sliceCursorAfter_drop fold_sliceCursorAfter_from_consumed
  memRegion_48_sret24 fold_memRegion_48_sret_ok
  bm_pointsToBytes_split_last toNat_le_0x7f_of_getLsbD_7_false
  SepWP.drop_left SepWP.with_vtableSlot_placed SepWPp.bm_call_frame_lscl
  SepWPp.unfold_memRegion_168 SepWPp.unfold_cells_64
  subroutine_ok_withLsCl_of_withLsCodeLoaded subroutine_ok_withLsCl_of_plain
)
open CryptoVerification.LibsignalTripleRatchet.Prost.X (
  decodeErrorHookStackW bytesMergeStackW
)
open Proofs.libsignal.Stage1X (
  finishGrowStackX lscall_of_withLsCl
)
open Proofs.libsignal.Hooks2 (
  doReserveStackX subroutine_ok_withLsCodeLoaded_map' subroutine_ok_withLsCl_map'
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel RustCliAllocBudget BudgetLimits
  FitsStep FitsEvent FitsEvents fitsEvents_nil fitsEvents_append
  rustAllocEvents rustDeallocEvents rustReallocEvents
  RustLayoutOk VmPreserved
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack rustCliDeallocNoOomExternSpecWithStack
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
  stepEvents_rustAlloc_small stepEvents_rustAlloc_large
  stepEvents_rustDealloc_small stepEvents_rustDealloc_large
  stepEvents_rustRealloc_small_small stepEvents_rustRealloc_small_large
  stepEvents_rustRealloc_large_large stepEvents_rustRealloc_large_small
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  AllocContractsBudgetPlaced withVmPreserved rustLayoutOk_of_layoutOk
  trapHooks sepWP_rebase_vmPreserved sepWP_seq_vmPreserved sepWP_seq_lscl_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget (
  sepWP_ret_vmPreserved
  shimVmExternSpecX memcpyVmExternSpecX
  alloc_extern_of_budgetPlaced dealloc_extern_of_budgetPlaced
  shim_extern_of_budgetPlaced memcpy_extern_of_budgetPlaced
  finishGrowEvents finishGrowEvents_zero finishGrowEvents_ne
  finishGrowBudgetSpecX finish_grow_budget_placed_ok
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstVarintVm (
  bytesStaticDrop_vmPreserved_placed_ok_cl bytesFromVec_vmPreserved_placed_ok_cl
  decodeVarintSlowSomeWithStackSpec decode_varint_slow_some_withStack_placed_ok_cl
  decodeVarintSliceSomeSpecGen decode_varint_slice_some_placed_ok_cl
)

private theorem decodeVarintAux_length_lt_pm (i : Nat) (acc : BitVec 64)
    (bs rest0 : List (BitVec 8)) (len : BitVec 64)
    (h : decodeVarintAux i acc bs = some (len, rest0)) :
    rest0.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h
    dsimp only at h
    split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp
    · split at h
      · contradiction
      · have hlt := ih _ _ h
        simp; omega

private theorem mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩
    rw [hvar] at h
    dsimp only at h
    split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : rest0.length < bs.length := decodeVarintAux_length_lt_pm 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

/-! ## 0. Event Trace Definitions & Symbolic `HasFineReallocCredit` Lemmas -/

/-- Events emitted by `do_reserve_and_handle` (`Block 13`, `align = 1, stride = 1`) from `cap` to
`reserveCap cap len additional`. -/
def doReserveEvents (cap len additional : Nat) : List AllocEvent :=
  let newCap := reserveCap cap len additional
  if cap = 0 then rustAllocEvents newCap 1
  else rustReallocEvents cap newCap 1

/-- Events emitted by `bytesVtableDrop` (`Blocks 224, 236, 237`, `align = 1`). -/
def bytesDropEvents (len : Nat) : List AllocEvent :=
  if len = 0 then [] else rustDeallocEvents len 1

/-- Allocating events emitted during `prost::encoding::bytes::merge` (Block `7`):
temporary `BytesMut` buffer allocation (`vlen` B, if `vlen ≠ 0`) followed by
`do_reserve_and_handle` on the destination `Vec<u8>` (if `valCap < vlen`).
Used in `FitsEvents` preconditions (since trailing `.free` has unconstrained `stepReserve`
and never OOMs). -/
def bytesMergeAllocEvents (valCap vlen : Nat) : List AllocEvent :=
  (if vlen = 0 then [] else rustAllocEvents vlen 1) ++
  (if valCap < vlen then doReserveEvents valCap 0 vlen else [])

/-- Full event trace of `prost::encoding::bytes::merge` (Block `7`), including the epilogue
`bytesVtableDrop` of the temporary `vlen`-byte buffer (which credits `largeCost M vlen` back
from `liveLarge` when `smallMaxReq M < vlen`). -/
def bytesMergeEvents (valCap vlen : Nat) : List AllocEvent :=
  bytesMergeAllocEvents valCap vlen ++ bytesDropEvents vlen

/-- Deterministic output capacity of `prost::encoding::bytes::merge` on `mergeBytes wt bs = some (v, rest)`. -/
def bytesMergeOutCap (valCap : BitVec 64) (vlen : Nat) : BitVec 64 :=
  if valCap.toNat < vlen then BitVec.ofNat 64 (reserveCap valCap.toNat 0 vlen) else valCap

@[simp]
theorem doReserveEvents_zero (len additional : Nat) :
    doReserveEvents 0 len additional = rustAllocEvents (reserveCap 0 len additional) 1 := rfl

theorem doReserveEvents_ne {cap : Nat} (hcap : cap ≠ 0) (len additional : Nat) :
    doReserveEvents cap len additional = rustReallocEvents cap (reserveCap cap len additional) 1 := by
  simp [doReserveEvents, hcap]

@[simp]
theorem bytesDropEvents_zero : bytesDropEvents 0 = [] := rfl

theorem bytesDropEvents_ne {len : Nat} (hlen : len ≠ 0) :
    bytesDropEvents len = rustDeallocEvents len 1 := by
  simp [bytesDropEvents, hlen]

@[simp]
theorem bytesMergeAllocEvents_zero (valCap : Nat) :
    bytesMergeAllocEvents valCap 0 = [] := by
  simp [bytesMergeAllocEvents]

@[simp]
theorem bytesMergeEvents_zero (valCap : Nat) :
    bytesMergeEvents valCap 0 = [] := by
  simp [bytesMergeEvents]

@[simp]
theorem reserveCap_zero_zero (vlen : Nat) :
    reserveCap 0 0 vlen = max vlen 8 := by
  dsimp [reserveCap]
  omega

theorem bytesMergeOutCap_zero_zero :
    bytesMergeOutCap 0#64 0 = 0#64 := rfl

theorem bytesMergeOutCap_zero_pos {vlen : Nat} (hpos : 0 < vlen) :
    bytesMergeOutCap 0#64 vlen = BitVec.ofNat 64 (max vlen 8) := by
  simp [bytesMergeOutCap, hpos, reserveCap_zero_zero]

theorem fitsEvents_singleton {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {ev : AllocEvent} :
    FitsEvents M lim st [ev] ↔ FitsEvent M lim st ev := by
  simp [FitsEvents]

theorem fitsEvents_rustAlloc_one {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {req : Nat} (hpos : 0 < req) :
    FitsEvents M lim st (rustAllocEvents req 1) ↔ FitsEvent M lim st (.alloc req) := by
  have hle : 1 ≤ req := hpos
  simp [rustAllocEvents, hle, FitsEvents]

theorem fitsEvents_rustRealloc_one {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {old new : Nat} (hpos : 0 < new) :
    FitsEvents M lim st (rustReallocEvents old new 1) ↔
      FitsEvent M lim st (.realloc 1 old new) := by
  have hle : 1 ≤ new := hpos
  simp [rustReallocEvents, hle, FitsEvents]

theorem stepEvents_bytesDrop_small (M : AllocCostModel) [HasFineReallocCredit M]
    {len : Nat} (st : M.σ) (hle : len ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (bytesDropEvents len) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  by_cases h0 : len = 0
  · subst h0; simp [bytesDropEvents, AllocCostModel.stepEvents]
  · rw [bytesDropEvents_ne h0]
    exact stepEvents_rustDealloc_small M st (by decide) hle

theorem stepEvents_bytesDrop_large (M : AllocCostModel) [HasFineReallocCredit M]
    {len : Nat} (st : M.σ) (hgt : HasFineReallocCredit.smallMaxReq M < len) :
    let st' := M.stepEvents (bytesDropEvents len) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - HasFineReallocCredit.largeCost M len ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have h0 : len ≠ 0 := by omega
  rw [bytesDropEvents_ne h0]
  exact stepEvents_rustDealloc_large M st (by decide) hgt

theorem stepEvents_bytesMergeFresh_zero (M : AllocCostModel) (st : M.σ) :
    M.stepEvents (bytesMergeEvents 0 0) st = st := by
  simp [bytesMergeEvents, AllocCostModel.stepEvents]

theorem stepEvents_bytesMergeFresh_small (M : AllocCostModel) [HasFineReallocCredit M]
    {vlen : Nat} (st : M.σ)
    (hpos : 0 < vlen) (hle : max vlen 8 ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (bytesMergeEvents 0 vlen) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        HasFineReallocCredit.smallAllocCost M vlen +
        HasFineReallocCredit.smallAllocCost M (max vlen 8) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have hv_ne : vlen ≠ 0 := by omega
  have hv_le : vlen ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hmax_pos : 0 < max vlen 8 := by omega
  have hev : bytesMergeEvents 0 vlen =
      (rustAllocEvents vlen 1 ++ rustAllocEvents (max vlen 8) 1) ++ bytesDropEvents vlen := by
    simp [bytesMergeEvents, bytesMergeAllocEvents, hv_ne, hpos, doReserveEvents, reserveCap_zero_zero]
  dsimp only
  rw [hev, AllocCostModel.stepEvents_append, AllocCostModel.stepEvents_append]
  have h1 := stepEvents_rustAlloc_small M st (al := 1) (by decide) hpos hv_le
  set st1 := M.stepEvents (rustAllocEvents vlen 1) st
  have h2 := stepEvents_rustAlloc_small M st1 (al := 1) (by decide) hmax_pos hle
  set st2 := M.stepEvents (rustAllocEvents (max vlen 8) 1) st1
  have h3 := stepEvents_bytesDrop_small M st2 hv_le
  set st3 := M.stepEvents (bytesDropEvents vlen) st2
  exact ⟨by omega, by omega, by omega⟩

theorem stepEvents_bytesMergeFresh_large (M : AllocCostModel) [HasFineReallocCredit M]
    {vlen : Nat} (st : M.σ)
    (h8 : 8 ≤ HasFineReallocCredit.smallMaxReq M)
    (hgt : HasFineReallocCredit.smallMaxReq M < vlen) :
    let st' := M.stepEvents (bytesMergeEvents 0 vlen) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + 2 * HasFineReallocCredit.largeMetaCost M ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M vlen ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + 2 * HasFineReallocCredit.largeCost M vlen) := by
  have hv_pos : 0 < vlen := by omega
  have hv_ne : vlen ≠ 0 := by omega
  have hmax_eq : max vlen 8 = vlen := by omega
  have hev : bytesMergeEvents 0 vlen =
      (rustAllocEvents vlen 1 ++ rustAllocEvents vlen 1) ++ bytesDropEvents vlen := by
    simp [bytesMergeEvents, bytesMergeAllocEvents, hv_ne, hv_pos, doReserveEvents,
      reserveCap_zero_zero, hmax_eq]
  dsimp only
  rw [hev, AllocCostModel.stepEvents_append, AllocCostModel.stepEvents_append]
  have h1 := stepEvents_rustAlloc_large M st (al := 1) (by decide) hgt
  set st1 := M.stepEvents (rustAllocEvents vlen 1) st
  have h2 := stepEvents_rustAlloc_large M st1 (al := 1) (by decide) hgt
  set st2 := M.stepEvents (rustAllocEvents vlen 1) st1
  have h3 := stepEvents_bytesDrop_large M st2 hgt
  set st3 := M.stepEvents (bytesDropEvents vlen) st2
  refine ⟨by omega, by omega, ?_⟩
  have hp1 := h1.2.2
  have hl1 := h1.2.1
  have hp2 := h2.2.2
  have hp3 := h3.2.2
  omega

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff FitsEvents
attribute [local simp, local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `SepWPp` `LibsignalRoLoaded` + `VmPreserved` Sequencing & Bitwise Helpers -/

/-- Sequence a `SepWP` segment up to `mid` inside a `SepWPp` proof on `P.rebase b Hk` while
threading `VmPreserved s sm`, `LibsignalCodeLoaded pl sm.mem`, and `LibsignalRoLoaded pl sm.mem`. -/
theorem sepWPp_seq_lsclro_vm {P : Program} {b mid ret : BitVec 64} {Hk : LibsignalHooks}
    {s : State} {Pre : SepProp} {pl : Obj.MultiPlacement}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → LibsignalCodeLoaded pl sm.mem → LibsignalRoLoaded pl sm.mem →
          SepWPp (P.rebase b Hk) ret sm Pm Q Qp oom))) :
    SepWPp (P.rebase b Hk) ret s Pre Q Qp oom := by
  have h1 := sepWP_rebase_vmPreserved (Hk := Hk) hwp
  intro R hm hL
  rcases SepWP.to_reaches_pc h1 hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hvm, hcont⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hst2, hout⟩ :=
      (hcont hvm (hcl.of_keepsFrozen hst1.keepsFrozen)
        (libsignalRoLoaded_of_keepsFrozen hro hst1.keepsFrozen)) R hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem noPanic_of_false {F R : SepProp} {sf : State}
    (hm : sf.mem ⊨ ((⌜False⌝ : SepProp) ∗ F) ∗ R) :
    False := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1

private theorem truncate32_and_255_of_setWidth8_eq_two {w : BitVec 64}
    (hw : w.setWidth 8 = 2#8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 w) &&& 255#64) = 2#32 := by
  bv_bits

private theorem signExtend32_zeroExtend64_getLsbD_31 (b : BitVec 8) :
    (((b.signExtend 32).zeroExtend 64).getLsbD 31) = b.getLsbD 7 := by
  bv_bits

/-! ## 2. `do_reserve_and_handle` (Block `13`, `doReserveStackX`) -/

private theorem adds_cs_eq_false_x {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_eq_x {cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : reserveCap cap.toNat len additional + 1 ≤ 2 ^ 63) :
    (if (8#64).ult (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else 8#64) =
      BitVec.ofNat 64 (reserveCap cap.toNat len additional) := by
  have hmax : max (max (len + additional) (2 * cap.toNat)) 8 + 1 ≤ 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc
      omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [reserveCap]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : (8#64).ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change 8 < max (len + additional) (2 * cap.toNat) at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change ¬ 8 < max (len + additional) (2 * cap.toNat) at hc2
    change 8 = max (max (len + additional) (2 * cap.toNat)) 8
    omega

private theorem memRegion_24_cells_x (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_doReserveX (sp : BitVec 64) :
    stackAt sp doReserveStackX =
      stackAt (sp - 64#64) finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := stackAt_split_cells sp 16432 8 (by decide)
  change stackAt sp doReserveStackX =
    stackAt (sp - 64#64) finishGrowStackX ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private abbrev FG1Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def finishGrow1ZeroBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG1Ghost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents new.toNat 1)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents new.toNat 1) st
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' new.toNat 1 ∗ memRegion p' new.toNat ∗
      A.pool lim st' sf ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private def finishGrow1NeBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG1Ghost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 1#64 ∧ s.readReg64 .x5 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, cap, _ptr, new, bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    let st' := M.stepEvents (rustReallocEvents cap.toNat new.toNat 1) st
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' new.toNat 1 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat - bs.length) ∗
      A.pool lim st' sf ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_1_zero_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowBudgetSpecX M A lim))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow1ZeroBudgetSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg
    fun ⟨(out, cap, ptr, new, bs, o0, o1, o2, fsp), st⟩ R s0 hpre => ?_
  simp only [finishGrow1ZeroBudgetSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  have hlay : LayoutOk new.toNat 1 := ⟨hpos, ⟨0, rfl⟩, hbound⟩
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  refine ⟨(⟨out, 0#64, ptr, new, 1#64, 1#64, []⟩, st), R, ?_, fun sf hq => ?_⟩
  · dsimp only [finishGrowBudgetSpecX, FinishGrowCall.oldBuf]
    simp only [ite_true, BitVec.toNat_zero, h1_toNat, Nat.mul_one, finishGrowEvents_zero,
      memRegion_24_cells_x, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos,
      by decide, by decide, hlay, hfit⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · dsimp only [finishGrowBudgetSpecX, finishGrow1ZeroBudgetSpecX] at hq ⊢
    simp only [BitVec.toNat_zero, h1_toNat, Nat.mul_one, finishGrowEvents_zero,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', BitVec.ofNat 64 new.toNat, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hp', _hal, htr⟩, hmemf⟩
    exact ⟨⟨hp', htr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemf⟩

private theorem finish_grow_1_ne_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowBudgetSpecX M A lim))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow1NeBudgetSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg
    fun ⟨(out, cap, ptr, new, bs, o0, o1, o2, fsp), st⟩ R s0 hpre => ?_
  simp only [finishGrow1NeBudgetSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp
  have hcap_ne_nat : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  have hlay : LayoutOk new.toNat 1 := ⟨hpos, ⟨0, rfl⟩, hbound⟩
  have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
  refine ⟨(⟨out, cap, ptr, new, 1#64, 1#64, bs⟩, st), R, ?_, fun sf hq => ?_⟩
  · dsimp only [finishGrowBudgetSpecX, FinishGrowCall.oldBuf]
    simp only [hcap, ite_false, h1_toNat, Nat.mul_one, finishGrowEvents_ne hcap_ne_nat,
      LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm,
      memRegion_24_cells_x, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos,
      by decide, by decide, hlay, hfit⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · dsimp only [finishGrowBudgetSpecX, finishGrow1NeBudgetSpecX] at hq ⊢
    simp only [h1_toNat, Nat.mul_one, finishGrowEvents_ne hcap_ne_nat,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', BitVec.ofNat 64 new.toNat, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hp', _hal, htr⟩, hmemf⟩
    exact ⟨⟨hp', htr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemf⟩

/-- Raw budget-threaded total-correctness spec for `do_reserve_and_handle` (Block `13`, `doReserveStackX`). -/
def doReserveRawBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      x.bs.length ≤ x.cap.toNat ∧ x.cap.toNat < 2 ^ 63 ∧ x.ptr ≠ 0#64 ∧
      reserveCap x.cap.toNat x.bs.length x.additional + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (doReserveEvents x.cap.toNat x.bs.length x.additional)⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp doReserveStackX
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    let st' := M.stepEvents (doReserveEvents x.cap.toNat x.bs.length x.additional) st
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64⌝ ∗ (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' newCap 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (newCap - x.bs.length)) ∗
    A.pool lim st' sf ∗ stackAt s0.sp doReserveStackX

set_option maxHeartbeats 1600000 in
/-- Block `13` (`<RawVecInner<_>>::reserve::do_reserve_and_handle`) meets `doReserveRawBudgetSpecX`
with `onPanic := ⌜False⌝` and `onOom := ⌜False⌝`. -/
theorem do_reserve_raw_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveRawBudgetSpecX M A lim)) := by
  unfold withLsCodeLoaded doReserveRawBudgetSpecX
  simp only [stackAt_doReserveX, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init xpair s0
  obtain ⟨⟨v, cap, ptr, bs, additional⟩, st⟩ := xpair
  dsimp only at *
  have hfg := finish_grow_budget_placed_ok hA
  have hfg0_cl : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (lsmpl.base 45)
      (withLsCl lsmpl (finishGrow1ZeroBudgetSpecX M A lim)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_1_zero_budget_placed_ok hfg)
  have hfg1_cl : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (lsmpl.base 45)
      (withLsCl lsmpl (finishGrow1NeBudgetSpecX M A lim)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_1_ne_budget_placed_ok hfg)
  clear hfg
  have hx1_eq : (s0.readReg64 (Reg.gpr 1#5)).toNat = bs.length := ‹_›
  have hx2_eq : (s0.readReg64 (Reg.gpr 2#5)).toNat = additional := ‹_›
  have hx3_eq : s0.readReg64 (Reg.gpr 3#5) = 1#64 := ‹_›
  have hx4_eq : s0.readReg64 (Reg.gpr 4#5) = 1#64 := ‹_›
  have hbs_le_cap : bs.length ≤ cap.toNat := ‹_›
  have hcap_lt63 : cap.toNat < 2 ^ 63 := ‹_›
  have hbound0 : reserveCap cap.toNat bs.length additional ≤ 9223372036854775807 := ‹_›
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by omega
  have hcs := adds_cs_eq_false_x (x2 := s0.readReg64 (Reg.gpr 2#5))
    (x1 := s0.readReg64 (Reg.gpr 1#5)) (by rw [hx2_eq, hx1_eq]; dsimp [reserveCap] at hbound; omega)
  have hnew_eq := reserve_new_cap_eq_x (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp only [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hfit0 : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
      have hf : FitsEvents M lim st (doReserveEvents (0#64 : BitVec 64).toNat ([] : List (BitVec 8)).length additional) := ‹_›
      simpa only [BitVec.toNat_zero, List.length_nil, doReserveEvents_zero, hnew_toNat] using hf
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 (Reg.gpr 2#5) + s0.readReg64 (Reg.gpr 1#5)) = true then
                s0.readReg64 (Reg.gpr 2#5) + s0.readReg64 (Reg.gpr 1#5)
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 (Reg.gpr 2#5) + s0.readReg64 (Reg.gpr 1#5)) = true then
            s0.readReg64 (Reg.gpr 2#5) + s0.readReg64 (Reg.gpr 1#5)
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [ite_true, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_zero, Nat.sub_zero, doReserveEvents_zero]
    wp_steps_lscl_vm_s (lsmpl.base 45) as hvm1 hcl1
    apply SepWP.transport_budgetPool hvm1
    have hfg0_call := lscall_of_withLsCl hfg0_cl hcl1
    dsimp only [finishGrow1ZeroBudgetSpecX] at hfg0_call
    wp_call hfg0_call ((s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3,
      s0.sp - 64#64), st)
    wp_steps_to_tgt_vm_s as hvm_end
    apply SepWP.transport_budgetPool hvm_end
    rw [hnew_toNat]
    wp_done
  · have hcap_ne_nat : cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    have hfit1 : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
      have hf : FitsEvents M lim st (doReserveEvents cap.toNat bs.length additional) := ‹_›
      simpa only [doReserveEvents_ne hcap_ne_nat, hnew_toNat] using hf
    simp only [hcap0, ite_false, sepConj_assoc, doReserveEvents_ne hcap_ne_nat]
    have hsub_eq : reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length := by
      rw [hnew_toNat]
    rw [hsub_eq]
    wp_steps_lscl_vm_s (lsmpl.base 45) as hvm1 hcl1
    apply SepWP.transport_budgetPool hvm1
    have hfg1_call := lscall_of_withLsCl hfg1_cl hcl1
    dsimp only [finishGrow1NeBudgetSpecX] at hfg1_call
    wp_call hfg1_call ((s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3,
      s0.sp - 64#64), st)
    wp_steps_to_tgt_vm_s as hvm_end
    apply SepWP.transport_budgetPool hvm_end
    rw [hnew_toNat]
    wp_done

/-- Budget-threaded total-correctness (`onOom := ⌜False⌝`, `onPanic := ⌜False⌝`) spec for
`RawVecInner::reserve::do_reserve_and_handle` (Block `13`, `doReserveStackX`) in `vecU8At` form. -/
def doReserveBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      s.readReg64 .x3 = 1#64 ∧ s.readReg64 .x4 = 1#64 ∧
      newCap + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (doReserveEvents x.cap.toNat x.bs.length x.additional)⌝ ∗
    vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
    A.pool lim st s ∗ stackAt s.sp doReserveStackX
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    let st' := M.stepEvents (doReserveEvents x.cap.toNat x.bs.length x.additional) st
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64, vecU8At A.repAlloc x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
    A.pool lim st' sf ∗ stackAt s0.sp doReserveStackX

/-- Block `13` meets `doReserveBudgetSpecX` (`vecU8At` wrapper over `do_reserve_raw_budget_placed_ok`). -/
theorem do_reserve_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveBudgetSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' (do_reserve_raw_budget_placed_ok hA)
    fun ⟨x, st⟩ R s0 hpre => ?_
  dsimp only [doReserveBudgetSpecX, vecU8At, vecHeader] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩, hmem⟩
  have hmem' : s0.mem ⊨ ⌜x.bs.length ≤ x.cap.toNat ∧ x.cap.toNat < 2 ^ 63 ∧ x.ptr ≠ 0⌝ ∗
      ((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
        ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (if x.cap = 0 then emp
         else A.repAlloc.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
           memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
        A.pool lim st s0 ∗ stackAt s0.sp doReserveStackX ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  rw [satisfies_pure_sepConj] at hmem'
  rcases hmem' with ⟨⟨hbs_le, hcap63, hptr_ne⟩, hmem_rest⟩
  have hptr64 : x.ptr ≠ 0#64 := hptr_ne
  refine ⟨(x, st), ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R, ?_, fun sf hq => ?_⟩
  · dsimp only [doReserveRawBudgetSpecX]
    have hif_eq : (if x.cap = 0 then emp
        else A.repAlloc.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
          memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) =
        (if x.cap = 0#64 then emp
        else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
          memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) := rfl
    rw [hif_eq] at hmem_rest
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hbs_le, hcap63, hptr64, hbound, hfit⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem_rest⟩
  · dsimp only [doReserveRawBudgetSpecX, doReserveBudgetSpecX] at hq ⊢
    set newCap := reserveCap x.cap.toNat x.bs.length x.additional
    have hnew_lt63 : (BitVec.ofNat 64 newCap).toNat < 2 ^ 63 := by
      dsimp [newCap, reserveCap] at hbound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hbs_le_new : x.bs.length ≤ (BitVec.ofNat 64 newCap).toNat := by
      dsimp [newCap, reserveCap] at hbound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    refine ⟨p', ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hp', hmemf⟩
    have hp'_ne0 : p' ≠ 0 := hp'
    have hcap_ne0 : BitVec.ofNat 64 newCap ≠ 0 := by
      intro h0
      have ht : (BitVec.ofNat 64 newCap).toNat = 0 := by rw [h0]; rfl
      dsimp [newCap, reserveCap] at hbound ht
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      omega
    dsimp only [vecU8At, vecHeader]
    simp only [hcap_ne0, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    have hgoal_eq :
        (((x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          (⌜x.bs.length ≤ (BitVec.ofNat 64 newCap).toNat ∧
            (BitVec.ofNat 64 newCap).toNat < 2 ^ 63 ∧ p' ≠ 0⌝ ∗
            (A.live p' (BitVec.ofNat 64 newCap).toNat 1 ∗ (p' ↦ₛ x.bs) ∗
              memRegion (p' + BitVec.ofNat 64 x.bs.length)
                ((BitVec.ofNat 64 newCap).toNat - x.bs.length))) ∗
          A.pool lim (M.stepEvents (doReserveEvents x.cap.toNat x.bs.length x.additional) st) sf ∗
          stackAt s0.sp doReserveStackX) ∗ R) =
        (⌜x.bs.length ≤ (BitVec.ofNat 64 newCap).toNat ∧
          (BitVec.ofNat 64 newCap).toNat < 2 ^ 63 ∧ p' ≠ 0⌝ ∗
          (((x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
            A.live p' (BitVec.ofNat 64 newCap).toNat 1 ∗ (p' ↦ₛ x.bs) ∗
            memRegion (p' + BitVec.ofNat 64 x.bs.length)
              ((BitVec.ofNat 64 newCap).toNat - x.bs.length) ∗
            A.pool lim (M.stepEvents (doReserveEvents x.cap.toNat x.bs.length x.additional) st) sf ∗
            stackAt s0.sp doReserveStackX) ∗
            (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R))) := by
      sep_ac_rfl
    have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
      dsimp [newCap, reserveCap] at hbound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [sepConj_assoc] at hgoal_eq ⊢
    rw [hgoal_eq, satisfies_pure_sepConj]
    refine ⟨⟨hbs_le_new, hnew_lt63, hp'_ne0⟩, ?_⟩
    rw [hnew_toNat]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemf

/-- Caller-block-polymorphic `withLsCl` form of `do_reserve_budget_placed_ok`. -/
theorem do_reserve_budget_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 13)
      (withLsCl lsmpl (doReserveBudgetSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 13) (do_reserve_budget_placed_ok hA)


/-! ## 3. `bytesVtableDrop` (Blocks `224, 237, 236`, `extHookStack + 48`) -/

private theorem stackAt_add_48_x {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

private theorem stackAt_add_48_comm_x {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt sp hookStack := by
  unfold stackAt
  have h0 : hookStack + 48 = 48 + hookStack := Nat.add_comm hookStack 48
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 (48 + hookStack)) 48 hookStack (by omega)
  have h1 : sp - BitVec.ofNat 64 (48 + hookStack) =
      sp - BitVec.ofNat 64 hookStack - 48#64 := by
    rw [BitVec.ofNat_add]; bv_lin
  have h2 : sp - BitVec.ofNat 64 (48 + hookStack) + 48#64 =
      sp - BitVec.ofNat 64 hookStack := by
    rw [BitVec.ofNat_add]; bv_lin
  rw [h0, hsplit, h2, h1]

private theorem pointsTo64_entails_exists_x (a v : BitVec 64) {R Q : SepProp}
    (h : R ⊢ Q) : ((a ↦₆₄ v) ∗ R) ⊢ ∃∗ x, (a ↦₆₄ x) ∗ Q :=
  Entails.trans (sepConj_mono_right h) (Entails.sepExists_intro (P := fun x => (a ↦₆₄ x) ∗ Q) v)

private theorem pointsTo64_entails_exists_single_x (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ x, (a ↦₆₄ x) :=
  Entails.sepExists_intro (P := fun x => a ↦₆₄ x) v

private theorem pointsTo64_6_entails_cells_x (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5)) ⊢ cells base 6 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists_x _ v0
    (pointsTo64_entails_exists_x _ v1
      (pointsTo64_entails_exists_x _ v2
        (pointsTo64_entails_exists_x _ v3
          (pointsTo64_entails_exists_x _ v4
            (pointsTo64_entails_exists_single_x _ v5)))))

@[local simp, local arm64_norm]
private theorem getLsbD_or_one_x (ptr : BitVec 64) : (ptr ||| 1#64).getLsbD 0 = true := by
  bv_bits

private theorem or_one_and_not_one_x {ptr : BitVec 64} (h : (ptr &&& 1#64) = 0#64) :
    (ptr ||| 1#64) &&& (-2#64) = ptr := by
  bv_bits

private theorem odd_drop_add_x {off len : Nat} (hoff : off ≤ len) :
    BitVec.ofNat 64 off + BitVec.ofNat 64 (len - off) = BitVec.ofNat 64 len := by
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le hoff]

private theorem ult_ofNat_false_x {off len : Nat} (hoff : off ≤ len) (hlen : len < 2 ^ 63) :
    (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 off) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : off < 2 ^ 64)]
  omega

private abbrev DeallocTailGhost :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def deallocTailBudgetSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DeallocTailGhost × M.σ) where
  pre := fun ((p, bs, align, v0, v1, v2, v3, v4, v5), st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      (s.readReg64 .x2).toNat = align ∧ RustLayoutOk bs.length align ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) extHookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun ((_p, bs, align, _v0, _v1, _v2, _v3, _v4, _v5), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents bs.length align) st) sf ∗
      stackAt s0.sp (extHookStack + 48)

private theorem dealloc_tail_budget_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (deallocTailBudgetSpecX M A lim)) := by
  have hstack : extHookStack + 48 ≤ 2 ^ 64 := by decide
  refine subroutine_ok_withLsCl_map' (dealloc_extern_of_budgetPlaced hA (callerProg := callerProg))
    fun ⟨(p, bs, align, v0, v1, v2, v3, v4, v5), st⟩ R s0 hpre => ?_
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells_x (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  refine ⟨(p, bs.length, align, st), stackAt (s0.sp - BitVec.ofNat 64 extHookStack) 48 ∗ R, ?_,
    fun sf hpost => ?_⟩
  · dsimp only [deallocTailBudgetSpecX] at hpre
    dsimp only [rustCliDeallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
            (s0.readReg64 .x2).toNat = align ∧ RustLayoutOk bs.length align ∧
            LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          A.pool lim st s0 ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) extHookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_48_x hstack, stackAt_add_48_comm_x hstack] at h1
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h1
  · dsimp only [deallocTailBudgetSpecX]
    dsimp only [rustCliDeallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hpost
    rw [stackAt_add_48_comm_x hstack]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

private def promotableEvenDropBudgetSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × Nat) × M.σ) where
  pre := fun ((ptr, bs, off), st) s =>
    ⌜0 < bs.length ∧ off ≤ bs.length ∧ (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧ s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      bytesBoxU8Buf A.repAlloc ptr bs ∗ A.pool lim st s ∗ stackAt s.sp (extHookStack + 48)
  post := fun ((_ptr, bs, _off), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (bytesDropEvents bs.length) st) sf ∗
      stackAt s0.sp (extHookStack + 48)

private theorem promotableEvenDrop_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (withLsCodeLoaded lsmpl (promotableEvenDropBudgetSpec M A lim)) := by
  have hstack : extHookStack + 48 ≤ 2 ^ 64 := by decide
  unfold withLsCodeLoaded promotableEvenDropBudgetSpec bytesBoxU8Buf
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_x hstack]
  cells_unfold
  wp_init xpair s0
  obtain ⟨⟨ptr, bs, off⟩, st⟩ := xpair
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := ‹_›
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := ‹_›
  have hlr30 : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr0
  have hpos : 0 < bs.length := ‹_›
  have hoff : off ≤ bs.length := ‹_›
  have heven : (ptr &&& 1#64) = 0#64 := ‹_›
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlen_ne : bs.length ≠ 0 := by omega
  simp only [hbs_ne, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm,
    bytesDropEvents_ne hlen_ne]
  have hlen63 : bs.length < 2 ^ 63 := ‹_›
  have hrlay : RustLayoutOk bs.length 1 :=
    rustLayoutOk_of_layoutOk (by decide) ⟨hpos, ⟨0, rfl⟩, by omega⟩
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_one_x heven
  apply sepWP_seq_lscl_vm hcl0 (mid := lsρ lsRustDeallocSym)
  by_vm_steps_withSvc (
    wp_steps
    wp_if hcs
    { rw [bitvec_add_sub_self_left, odd_drop_add_x hoff, ult_ofNat_false_x hoff hlen63] at hcs
      cases hcs }
    wp_steps
    refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1
  apply SepWP.transport_budgetPool hvm1
  have hadd_even : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
      BitVec.ofNat 64 bs.length := by
    rw [bitvec_add_sub_self_left, odd_drop_add_x hoff]
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdealloc := dealloc_tail_budget_ok hA
    (callerProg := (blkPC_237).rebase (blkPl_237).base H)
  have hcall := lscall_of_withLsCl hdealloc hcl1
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_call hcall ((ptr, bs, 1, v_stk, v_stk_1,
    s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
    s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5)), st)
  wp_done

private def promotableOddDropBudgetSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × Nat) × M.σ) where
  pre := fun ((ptr, bs, off), st) s =>
    ⌜0 < bs.length ∧ off ≤ bs.length ∧ (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      bytesBoxU8Buf A.repAlloc ptr bs ∗ A.pool lim st s ∗ stackAt s.sp (extHookStack + 48)
  post := fun ((_ptr, bs, _off), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (bytesDropEvents bs.length) st) sf ∗
      stackAt s0.sp (extHookStack + 48)

private theorem promotableOddDrop_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (withLsCodeLoaded lsmpl (promotableOddDropBudgetSpec M A lim)) := by
  have hstack : extHookStack + 48 ≤ 2 ^ 64 := by decide
  unfold withLsCodeLoaded promotableOddDropBudgetSpec bytesBoxU8Buf
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_x hstack]
  cells_unfold
  wp_init xpair s0
  obtain ⟨⟨ptr, bs, off⟩, st⟩ := xpair
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := ‹_›
  have hlr0 : LsRetAddr624 (s0.readReg64 .lr) := ‹_›
  have hlr30 : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr0
  have hpos : 0 < bs.length := ‹_›
  have hoff : off ≤ bs.length := ‹_›
  have hodd : (ptr &&& 1#64) ≠ 0#64 := ‹_›
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlen_ne : bs.length ≠ 0 := by omega
  simp only [hbs_ne, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm,
    bytesDropEvents_ne hlen_ne]
  have hlen63 : bs.length < 2 ^ 63 := ‹_›
  have hrlay : RustLayoutOk bs.length 1 :=
    rustLayoutOk_of_layoutOk (by decide) ⟨hpos, ⟨0, rfl⟩, by omega⟩
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr hodd
  apply sepWP_seq_lscl_vm hcl0 (mid := lsρ lsRustDeallocSym)
  by_vm_steps_withSvc (
    wp_steps
    wp_if hcs
    { rw [bitvec_add_sub_self_left, odd_drop_add_x hoff, ult_ofNat_false_x hoff hlen63] at hcs
      cases hcs }
    wp_steps
    refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1
  apply SepWP.transport_budgetPool hvm1
  have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
      BitVec.ofNat 64 bs.length := by
    rw [bitvec_add_sub_self_left, odd_drop_add_x hoff]
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdealloc := dealloc_tail_budget_ok hA
    (callerProg := (blkPC_236).rebase (blkPl_236).base H)
  have hcall := lscall_of_withLsCl hdealloc hcl1
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_call hcall ((ptr, bs, 1, v_stk, v_stk_1,
    s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
    s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5)), st)
  wp_done

/-- Budget-threaded total-correctness (`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`) contract for
unified `bytes::Bytes` `.rodata` vtable `drop` dispatch (`Blocks 224, 237, 236`). -/
def bytesVtableDropBudgetSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ptr : BitVec 64) (bs : List (BitVec 8))
    (off : Nat) : Spec M.σ where
  pre := fun st s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      bytesBoxU8Buf A.repAlloc ptr bs ∗ A.pool lim st s ∗ stackAt s.sp (extHookStack + 48)
  post := fun st s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      A.pool lim (M.stepEvents (bytesDropEvents bs.length) st) sf ∗
      stackAt s0.sp (extHookStack + 48)

/-- Caller-block-polymorphic `withLsCl` proof of `bytesVtableDropBudgetSpec` across
`bytes::bytes::{static_drop, promotable_even_drop, promotable_odd_drop}`. -/
theorem bytesVtableDrop_budget_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCl lsmpl (bytesVtableDropBudgetSpec M A lim ptr bs off)) := by
  by_cases hbs : bs = []
  · subst hbs
    have haddr : bytesPlacedDropFnAddr ptr ([] : List (BitVec 8)).length = lsmpl.base 224 := rfl
    rw [haddr]
    refine subroutine_ok_withLsCl_map'
      (bytesStaticDrop_vmPreserved_placed_ok_cl (callerProg := callerProg))
      fun st R s0 hpre => ?_
    dsimp only [bytesVtableDropBudgetSpec, bytesBoxU8Buf] at hpre
    simp only [↓reduceIte, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, _, hmem⟩
    refine ⟨(), A.pool lim st s0 ∗ (stackAt s0.sp (extHookStack + 48) ∗ R), ?_, fun sf hpost => ?_⟩
    · dsimp only [withVmPreserved, bytesStaticDropSpec]
      rw [emp_sepConj]
      exact hmem
    · dsimp only [withVmPreserved, bytesStaticDropSpec] at hpost
      dsimp only [bytesVtableDropBudgetSpec]
      simp only [List.length_nil, bytesDropEvents_zero, AllocCostModel.stepEvents]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hvm, htr, hmemf⟩
      rw [← A.pool_transport lim st s0 sf hvm] at hmemf
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htr, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemf⟩
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_ne : bs.length ≠ 0 := by omega
    have hptr_eq : bytesPtr ptr bs.length = ptr := by
      unfold bytesPtr; simp only [hlen_ne, ↓reduceIte]
    by_cases heven : (ptr &&& 1#64) = 0#64
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = lsmpl.base 237 := by
        unfold bytesPlacedDropFnAddr; simp only [hlen_ne, heven, ↓reduceIte]
      have hdata_eq : bytesData ptr bs.length = (ptr ||| 1#64) := by
        unfold bytesData; simp only [hlen_ne, heven, ↓reduceIte]
      rw [haddr]
      refine subroutine_ok_withLsCl_map'
        (ls_subroutine_ok_cl_of_callee (j := 237) (promotableEvenDrop_budget_placed_ok hA))
        fun st R s0 hpre => ⟨((ptr, bs, off), st), R, ?_, fun _ hpost => hpost⟩
      dsimp only [bytesVtableDropBudgetSpec, promotableEvenDropBudgetSpec] at hpre ⊢
      rw [hdata_eq, hptr_eq] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hoff, hx0, hx1, hx2, hlr⟩, hrest⟩
      exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2, hlr⟩, hrest⟩
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = lsmpl.base 236 := by
        unfold bytesPlacedDropFnAddr; simp only [hlen_ne, heven, ↓reduceIte]
      have hdata_eq : bytesData ptr bs.length = ptr := by
        unfold bytesData; simp only [hlen_ne, heven, ↓reduceIte]
      rw [haddr]
      refine subroutine_ok_withLsCl_map'
        (ls_subroutine_ok_cl_of_callee (j := 236) (promotableOddDrop_budget_placed_ok hA))
        fun st R s0 hpre => ⟨((ptr, bs, off), st), R, ?_, fun _ hpost => hpost⟩
      dsimp only [bytesVtableDropBudgetSpec, promotableOddDropBudgetSpec] at hpre ⊢
      rw [hdata_eq, hptr_eq] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hoff, hx0, hx1, hx2, hlr⟩, hrest⟩
      exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2, hlr⟩, hrest⟩

/-! ## 4. `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>` on `some` (Block `7`, `bytesMergeStackW`) -/

/-- Budget-threaded total-correctness (`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`) contract for
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]` (Block `7`, `bytesMergeStackW`)
on `mergeBytes x.wt x.bs = some (v, rest)` for general destination capacity `x.valCap`
(`2 * x.valCap.toNat + 1 ≤ 2 ^ 63`). Requires `FitsEvents` only on the allocating prefix
`bytesMergeAllocEvents x.valCap.toNat v.length` while stepping `M` through the full trace
`bytesMergeEvents x.valCap.toNat v.length` (including the epilogue `bytesVtableDrop` credit). -/
def bytesMergeSomeBudgetSpecW (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BytesMergeGhost × List (BitVec 8) × List (BitVec 8) × M.σ) where
  pre := fun (x, v, rest, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧ 2 * x.valCap.toNat + 1 ≤ 2 ^ 63 ∧
      mergeBytes x.wt x.bs = some (v, rest) ∧
      FitsEvents M lim st (bytesMergeAllocEvents x.valCap.toNat v.length)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMergeStackW
  post := fun (x, v, rest, st) s0 sf =>
    let cap' := bytesMergeOutCap x.valCap v.length
    let st' := M.stepEvents (bytesMergeEvents x.valCap.toNat v.length) st
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ ptr' : BitVec 64, vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
      A.pool lim st' sf ∗ stackAt s0.sp bytesMergeStackW

private abbrev NoPanicPost (R : SepProp) : State → SepProp → Prop :=
  fun sf Pf => (sf.mem ⊨ Pf ∗ R) → False

private def MergeBudgetPost (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (v rest : List (BitVec 8)) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf Pf =>
    ((sf.mem ⊨ Pf ∗ R) →
      (sf.mem ⊨ (bytesMergeSomeBudgetSpecW M A lim).post (x, v, rest, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private theorem noPanicPost_of_false {F R : SepProp} {sf : State} :
    NoPanicPost R sf (⌜False⌝ ∗ F) :=
  fun hm => noPanic_of_false hm

private theorem noExit_of_false {sf : State} {code : BitVec 64} {R' : SepProp}
    (_hex : sf.status = .Exited code) (hm : sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') : False :=
  not_satisfies_false_sepConj hm

private theorem sepWPp_to_subroutineOutcome_budget {α : Type} {prog : Program}
    {spec : Spec α} {x : α} {s0 : State} {P R : SepProp}
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (NoPanicPost R)) :
    ∃ sf, Steps prog s0 sf ∧ SubroutineOutcome spec x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨_, _, hmf, hpanic⟩ | ⟨_, hoom⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact (hpanic hmf).elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem epilogue_vtableDrop_0x2d8_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {v rest : List (BitVec 8)} {st : M.σ} {s0 s : State} {R : SepProp}
    {tmpPtr ptr' : BitVec 64}
    (hpc : s.pc = (blkPl_7).base + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length + BitVec.ofNat 64 v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    let st_mid := M.stepEvents (bytesMergeAllocEvents x.valCap.toNat v.length) st
    let cap' := bytesMergeOutCap x.valCap v.length
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st_mid s ∗
        (vecU8At A.repAlloc x.valPtr cap' ptr' v ∗
          bytesBoxU8Buf A.repAlloc tmpPtr v ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x v rest st s0 R) (NoPanicPost R) := by
  intro st_mid cap'
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  have hdrop_le : extHookStack + 48 ≤ bmSliceStack decodeErrorHookStackW := by decide
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hVtableDrop := bytesVtableDrop_budget_placed_ok_cl hA
    (callerProg := (blkPC_7).rebase (blkPl_7).base H) tmpPtr v v.length
  dsimp only [savedRegsStack] at hpc ⊢
  apply sepWPp_seq_lsclro_vm hcl hro (mid := bytesPlacedDropFnAddr tmpPtr v.length)
  apply SepWP.with_vtableSlot_placed tmpPtr v.length hro
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.drop_left
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl_call hro_call
  rw [← A.pool_transport lim _ _ _ hvm1]
  refine SepWPp.bm_call_frame_lscl (x := st_mid)
    (T := bytesBoxU8Buf A.repAlloc tmpPtr v ∗ A.pool lim st_mid _ ∗
      stackAt (s0.sp - 224#64) (extHookStack + 48))
    hVtableDrop hcl_call hro_call
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by dsimp only [bytesVtableDropBudgetSpec]; simp (config := { decide := true }) only [State.sp_setMem, State.sp_setPC, State.sp_setPState, State.sp_writeReg64_of_isSp_false, hsp]; rfl)
    (by exact ⟨Nat.le_refl _,
               by simp (config := { decide := true }) only [arm64_norm, hx22],
               by simp (config := { decide := true }) only [arm64_norm, hx21],
               by simp (config := { decide := true }) only [arm64_norm, Nat.sub_self, BitVec.ofNat_eq_ofNat],
               by simp (config := { decide := true }) only [blkPl_7, wp_norm, arm64_norm]⟩)
    (by rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW (extHookStack + 48) hdrop_le hbnd]; sep_focus)
    (fun _ _ _ => noExit_of_false)
    (fun _ _ => noPanicPost_of_false) ?_
  intro sf_dr hpcf hrunf hspf hcsf _ _
  have hhigh' : bm_HighCalleeSaved s0 sf_dr := hhigh.of_calleeSaved hcsf
  obtain ⟨h25, h26, h27, h28⟩ := hhigh'
  simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf
  simp (config := { decide := true }) only [bytesVtableDropBudgetSpec, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW))
    (by rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW (extHookStack + 48) hdrop_le hbnd]; exact Entails.refl _)
    (by sep_focus)
  have hev_eq : M.stepEvents (bytesDropEvents v.length) st_mid =
      M.stepEvents (bytesMergeEvents x.valCap.toNat v.length) st := by
    dsimp [st_mid, bytesMergeEvents]
    rw [AllocCostModel.stepEvents_append]
  rw [hev_eq]
  apply SepWPp.of_sepWP_ret
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (fold_stackAt_bytesMergeGen s0.sp decodeErrorHookStackW hbnd
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
      (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm_ret
  rw [← A.pool_transport lim _ _ _ hvm_ret]
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  refine ⟨?_, by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf],
    by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self]⟩
  intro hmf
  dsimp only [MergeBudgetPost, bytesMergeSomeBudgetSpecW]
  simp (config := { decide := true }) only [State.readReg64_setPC, State.readReg64_writeReg64,
    State.trace_setPC, State.trace_writeReg64, Reg.x0, htr, and_self, pure_true, emp_sepConj]
  have hptr_ex : vecU8At A.repAlloc x.valPtr cap' ptr' v ⊢
      ∃∗ p : BitVec 64, vecU8At A.repAlloc x.valPtr cap' p v :=
    Entails.sepExists_intro (P := fun p : BitVec 64 => vecU8At A.repAlloc x.valPtr cap' p v) ptr'
  have hmf' := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hptr_ex)))) hmf
  change _ ⊨ _
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf'

private theorem phase3_from_0x2b4_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {v rest : List (BitVec 8)} {st : M.σ} {s0 s : State} {R : SepProp}
    {tmpPtr ptr' : BitVec 64}
    (hcap' : v.length ≤ (bytesMergeOutCap x.valCap v.length).toNat)
    (hv_len : v.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_7).base + 692#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    let st_mid := M.stepEvents (bytesMergeAllocEvents x.valCap.toNat v.length) st
    let cap' := bytesMergeOutCap x.valCap v.length
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st_mid s ∗
        (vecU8At A.repAlloc x.valPtr cap' ptr' [] ∗
          bytesBoxU8Buf A.repAlloc tmpPtr v ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x v rest st s0 R) (NoPanicPost R) := by
  intro st_mid cap'
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  have hmc_le : extHookStack ≤ bmSliceStack decodeErrorHookStackW := by decide
  rcases v with _ | ⟨b0, v'⟩
  · apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_7).base + bv% (728))
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm1 hcl1 hro1
    rw [← A.pool_transport lim _ _ _ hvm1]
    exact epilogue_vtableDrop_0x2d8_budget hA
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      hhigh hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])
  · set v := b0 :: v'
    have hmc := memcpy_extern_of_budgetPlaced hA
      (callerProg := (blkPC_7).rebase (blkPl_7).base H)
    have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
      apply beq_false_of_ne; intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2; exact absurd h2 (by dsimp [v]; omega)
    have hbytesPtr : bytesPtr tmpPtr v.length = tmpPtr := by
      unfold bytesPtr; have : v.length ≠ 0 := by omega
      simp [this]
    rw [vecU8At_nil_eq A.repAlloc x.valPtr cap' ptr' v hpos hcap',
      bytesBoxU8Buf_nonempty A.repAlloc tmpPtr v hpos]
    refine SepWPp.weaken_pre (P' :=
      ⌜0 ≤ cap'.toNat ∧ cap'.toNat < 2 ^ 63 ∧ ptr' ≠ 0#64⌝ ∗
        (⌜tmpPtr ≠ 0#64 ∧ v.length < 2 ^ 63⌝ ∗
          (A.pool lim st_mid s ∗
            ((x.valPtr ↦₆₄ cap') ∗ ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
              A.repAlloc.live ptr' cap'.toNat 1 ∗ memRegion ptr' v.length ∗
              memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ∗
              A.repAlloc.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ∗
              (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
              stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
              memRegion (s0.sp - 224#64) 8 ∗
              memRegion (s0.sp - 216#64) 48 ∗
              memRegion (s0.sp - 168#64) 104 ∗
              savedRegsStack s0.sp s0)))) (Entails.of_eq (by dsimp only [cap', v]; sep_ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨_, hcap_lt, hptr'⟩ => ?_
    refine SepWPp.pure_elim fun ⟨htmp_ne, hv_lt63⟩ => ?_
    apply sepWPp_seq_lsclro_vm hcl hro (mid := lsρ "memcpy")
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm1 hcl1 hro1
    rw [← A.pool_transport lim _ _ _ hvm1]
    rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW extHookStack hmc_le hbnd]
    refine SepWPp.bm_call_frame_lscl (x := (ptr', tmpPtr, v))
      (T := memRegion ptr' v.length ∗ (tmpPtr ↦ₛ v) ∗ stackAt (s0.sp - 224#64) extHookStack)
      hmc hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hlen_ne])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [memcpyVmExternSpecX, arm64_norm, hsp]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm, hlen_toNat, and_self])
      (by sep_focus)
      (fun _ _ _ => noExit_of_false)
      (fun _ _ => noPanicPost_of_false) ?_
    intro sf_mc hpcf hrunf hspf hcsf hclf hrof
    have hhigh' : bm_HighCalleeSaved s0 sf_mc := hhigh.of_calleeSaved hcsf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, _, _, _, _, h29f⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h29f
    simp (config := { decide := true }) only [memcpyVmExternSpecX, arm64_norm, hsp, htrace]
    refine SepWPp.pure_elim fun ⟨_, htr, hvm_mc⟩ => ?_
    rw [← A.pool_transport lim st_mid s sf_mc (hvm1.trans hvm_mc)]
    apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW))
      (by rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW extHookStack hmc_le hbnd]; exact Entails.refl _)
      (by sep_focus)
    refine SepWPp.weaken_pre (P' := A.pool lim st_mid sf_mc ∗
      (((x.valPtr ↦₆₄ cap') ∗ ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
        A.repAlloc.live ptr' cap'.toNat 1 ∗ (ptr' ↦ₛ v) ∗
        memRegion (ptr' + BitVec.ofNat 64 v.length) (cap'.toNat - v.length) ∗
        A.repAlloc.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0))) (Entails.of_eq (by sep_ac_rfl)) ?_
    apply sepWPp_seq_lsclro_vm hclf hrof (mid := (blkPl_7).base + bv% (728))
    by_vm_steps_withSvc (
      wp_steps
      apply SepWP.fold (fold_bytesBoxU8Buf_nonempty A.repAlloc tmpPtr v hpos htmp_ne hv_lt63)
        (by sep_focus)
      apply SepWP.fold (fold_vecU8At_copied A.repAlloc x.valPtr cap' ptr' v hpos hcap' hcap_lt hptr')
        (by sep_focus)
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim _ _ _ hvm2]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (epilogue_vtableDrop_0x2d8_budget hA
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh'; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21, h20f, hx20, hbytesPtr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24]))

private theorem phase3_from_0x294_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {v rest : List (BitVec 8)} {st : M.σ} {s0 s : State} {R : SepProp}
    {tmpPtr : BitVec 64}
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63)
    (_hbs63 : x.bs.length < 2 ^ 63)
    (hcap2 : 2 * x.valCap.toNat + 1 ≤ 2 ^ 63)
    (hfit_res : FitsEvents M lim
      (M.stepEvents (if v.length = 0 then [] else rustAllocEvents v.length 1) st)
      (if x.valCap.toNat < v.length then doReserveEvents x.valCap.toNat 0 v.length else []))
    (hpc : s.pc = (blkPl_7).base + 660#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    let st_alloc := M.stepEvents (if v.length = 0 then [] else rustAllocEvents v.length 1) st
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st_alloc s ∗
        (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          bytesBoxU8Buf A.repAlloc tmpPtr v ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x v rest st s0 R) (NoPanicPost R) := by
  intro st_alloc
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  have hres_le : doReserveStackX ≤ bmSliceStack decodeErrorHookStackW := by decide
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr x.valCap x.valBuf x.valBs]
  dsimp only [vecHeader] at hpc ⊢
  apply sepWPp_seq_lsclro_vm hcl hro
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true
      then (blkPl_7).base + bv% (800) else (blkPl_7).base + bv% (676))
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (fold_vecU8At_clear A.repAlloc x.valPtr x.valCap x.valBuf x.valBs) (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim _ _ _ hvm1]
  by_cases hult : x.valCap.ult (BitVec.ofNat 64 v.length) = true
  · simp only [hult, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_lt : x.valCap.toNat < v.length := by
      simpa [BitVec.ult, hlen_toNat] using hult
    have hfit_do : FitsEvents M lim st_alloc (doReserveEvents x.valCap.toNat 0 v.length) := by
      simpa only [hcap_lt, ↓reduceIte] using hfit_res
    have hnewCap_bound : reserveCap x.valCap.toNat ([] : List (BitVec 8)).length v.length + 1 ≤ 2 ^ 63 := by
      dsimp [reserveCap]; omega
    have hnewCap_ge : v.length ≤ (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)).toNat := by
      dsimp [reserveCap] at hnewCap_bound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    have hnewCap_ule :
        (BitVec.ofNat 64 v.length).ule (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) = true := by
      simp only [BitVec.ule, hlen_toNat, decide_eq_true_eq]; exact hnewCap_ge
    have houtCap_eq : bytesMergeOutCap x.valCap v.length =
        BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length) := by
      simp [bytesMergeOutCap, hcap_lt]
    have hst_mid_eq : M.stepEvents (doReserveEvents x.valCap.toNat 0 v.length) st_alloc =
        M.stepEvents (bytesMergeAllocEvents x.valCap.toNat v.length) st := by
      dsimp [st_alloc, bytesMergeAllocEvents]
      rw [AllocCostModel.stepEvents_append]
      simp [hcap_lt]
    have hReserve := do_reserve_budget_placed_ok_cl hA
      (callerProg := (blkPC_7).rebase (blkPl_7).base H)
    apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := lsmpl.base 13)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim _ _ _ hvm2]
    rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW doReserveStackX hres_le hbnd]
    refine SepWPp.bm_call_frame_lscl
      (x := ({ v := x.valPtr, cap := x.valCap, ptr := x.valBuf, bs := [], additional := v.length }, st_alloc))
      (T := vecU8At A.repAlloc x.valPtr x.valCap x.valBuf [] ∗ A.pool lim st_alloc _ ∗
        stackAt (s0.sp - 224#64) doReserveStackX)
      hReserve hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by dsimp only [doReserveBudgetSpecX]; simp (config := { decide := true }) only [State.sp_setMem, State.sp_setPC, State.sp_setPState, State.sp_writeReg64_of_isSp_false, hsp]; rfl)
      (by exact ⟨by simp (config := { decide := true }) only [arm64_norm, hx19],
                 by simp (config := { decide := true }) only [arm64_norm],
                 by simp (config := { decide := true }) only [arm64_norm, hx20, hlen_toNat],
                 by simp (config := { decide := true }) only [arm64_norm],
                 by simp (config := { decide := true }) only [arm64_norm],
                 hnewCap_bound, hfit_do⟩)
      (by sep_focus)
      (fun _ _ _ => noExit_of_false)
      (fun _ _ => noPanicPost_of_false) ?_
    intro sf_res hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
    obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
    dsimp only [doReserveBudgetSpecX, List.length_nil]
    rw [hst_mid_eq, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptr' => ?_
    rw [bm_vecU8At_eq_header_sep_buf A.repAlloc x.valPtr
      (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []]
    dsimp only [vecHeader, List.length_nil]
    refine SepWPp.weaken_pre (P' :=
      A.pool lim (M.stepEvents (bytesMergeAllocEvents x.valCap.toNat v.length) st) sf_res ∗
        (((x.valPtr ↦₆₄ BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ∗
          ((x.valPtr + 8#64) ↦₆₄ ptr') ∗ ((x.valPtr + 16#64) ↦₆₄ 0#64) ∗
          bm_vecU8Buf A.repAlloc (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [] ∗
          stackAt (sf_res.sp) doReserveStackX ∗
          bytesBoxU8Buf A.repAlloc tmpPtr v ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          bmExtraStack s0.sp decodeErrorHookStackW doReserveStackX ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0)))
      (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp, hspf]; sep_ac_rfl)) ?_
    apply sepWPp_seq_lsclro_vm hclf hrof (mid := (blkPl_7).base + bv% (692))
    by_vm_steps_withSvc (
      wp_steps
      apply SepWP.fold
        (fold_vecU8At_clear A.repAlloc x.valPtr
          (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [])
        (by sep_focus)
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm3 hcl3 hro3
    rw [← A.pool_transport lim _ _ _ hvm3]
    refine SepWPp.weaken_pre (P' :=
      A.pool lim (M.stepEvents (bytesMergeAllocEvents x.valCap.toNat v.length) st) _ ∗
        (vecU8At A.repAlloc x.valPtr (bytesMergeOutCap x.valCap v.length) ptr' [] ∗
          bytesBoxU8Buf A.repAlloc tmpPtr v ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by
        rw [houtCap_eq, hspf, stackAt_sliceGen_split s0.sp decodeErrorHookStackW doReserveStackX hres_le hbnd]
        sep_ac_rfl)) ?_
    exact phase3_from_0x2b4_budget (tmpPtr := tmpPtr) (ptr' := ptr') hA (by rw [houtCap_eq]; exact hnewCap_ge) hv_len
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl3 hro3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h23f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24])
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simpa [BitVec.ult, hlen_toNat] using hult_eq
    have hcap_nlt : ¬ x.valCap.toNat < v.length := by omega
    have houtCap_eq : bytesMergeOutCap x.valCap v.length = x.valCap := by
      simp [bytesMergeOutCap, hcap_nlt]
    have hst_mid_eq : st_alloc = M.stepEvents (bytesMergeAllocEvents x.valCap.toNat v.length) st := by
      dsimp [st_alloc, bytesMergeAllocEvents]
      rw [AllocCostModel.stepEvents_append]
      simp [hcap_nlt, AllocCostModel.stepEvents]
    apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_7).base + bv% (692))
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim _ _ _ hvm2]
    refine SepWPp.weaken_pre (P' :=
      A.pool lim (M.stepEvents (bytesMergeAllocEvents x.valCap.toNat v.length) st) _ ∗
        (vecU8At A.repAlloc x.valPtr (bytesMergeOutCap x.valCap v.length) x.valBuf [] ∗
          bytesBoxU8Buf A.repAlloc tmpPtr v ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by rw [hst_mid_eq, houtCap_eq]; sep_ac_rfl)) ?_
    exact phase3_from_0x2b4_budget (tmpPtr := tmpPtr) (ptr' := x.valBuf) hA (by rw [houtCap_eq]; exact hcap_ge) hv_len
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])

private theorem phase2_from_0x23c_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {v rest : List (BitVec 8)} {st : M.σ} {s0 s : State} {R : SepProp}
    {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63)
    (hbs63 : x.bs.length < 2 ^ 63)
    (hcap2 : 2 * x.valCap.toNat + 1 ≤ 2 ^ 63)
    (hfit_res : FitsEvents M lim
      (M.stepEvents (if v.length = 0 then [] else rustAllocEvents v.length 1) st)
      (if x.valCap.toNat < v.length then doReserveEvents x.valCap.toNat 0 v.length else []))
    (hpc : s.pc = (blkPl_7).base + 572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 v.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx22 : s.readReg64 .x22 = bytesMutDataWord (BitVec.ofNat 64 v.length))
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    let st_alloc := M.stepEvents (if v.length = 0 then [] else rustAllocEvents v.length 1) st
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st_alloc s ∗
        (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
          ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
          ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
          ((s0.sp - 120#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 112#64) 32 ∗
          ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
          bm_vecU8Buf A.repAlloc (BitVec.ofNat 64 v.length) tmpPtr v ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x v rest st s0 R) (NoPanicPost R) := by
  intro st_alloc
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  have hbfv_le : bytesFromVecStack ≤ bmSliceStack decodeErrorHookStackW := by decide
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hBytesFromVec := bytesFromVec_vmPreserved_placed_ok_cl (A := A.repAlloc)
    (callerProg := (blkPC_7).rebase (blkPl_7).base H)
  apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 250)
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (fold_vecU8At_sp136 A.repAlloc s0.sp (BitVec.ofNat 64 v.length) tmpPtr v)
      (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
        bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim _ _ _ hvm1]
  rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW bytesFromVecStack hbfv_le hbnd]
  refine SepWPp.bm_call_frame_lscl
    (x := (s0.sp - 136#64, s0.sp - 112#64, BitVec.ofNat 64 v.length, tmpPtr, v))
    (T := vecU8At A.repAlloc (s0.sp - 136#64) (BitVec.ofNat 64 v.length) tmpPtr v ∗
      memRegion (s0.sp - 112#64) 32 ∗
      stackAt (s0.sp - 224#64) bytesFromVecStack)
    hBytesFromVec hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [withVmPreserved, bytesFromVecPlacedSpec, arm64_norm, hsp, hx29])
    hlen_toNat
    (by sep_focus)
    (fun _ _ _ => noExit_of_false)
    (fun _ _ => noPanicPost_of_false) ?_
  intro sf_bfv hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx19, hx20, hx21, hx22, hx29,
    bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero]
    at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  dsimp only [withVmPreserved, bytesFromVecPlacedSpec]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun hvm_bfv => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr => ?_
  rw [← A.pool_transport lim st_alloc _ sf_bfv hvm_bfv,
    unfold_vecHeader_sp136, unfold_bytesPlacedAt_sp112]
  refine SepWPp.weaken_pre (P' :=
    A.pool lim st_alloc sf_bfv ∗
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗ ((s0.sp - 128#64) ↦₆₄ tmpPtr) ∗
        ((s0.sp - 120#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
        ((s0.sp - 112#64) ↦₆₄ bytesPlacedVtable tmpPtr v.length) ∗
        ((s0.sp - 104#64) ↦₆₄ bytesPtr tmpPtr v.length) ∗
        ((s0.sp - 96#64) ↦₆₄ BitVec.ofNat 64 v.length) ∗
        ((s0.sp - 88#64) ↦₆₄ bytesData tmpPtr v.length) ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        bytesBoxU8Buf A.repAlloc tmpPtr v ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        stackAt (sf_bfv.sp) bytesFromVecStack ∗
        bmExtraStack s0.sp decodeErrorHookStackW bytesFromVecStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0))
    (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp, hspf]; sep_ac_rfl)) ?_
  apply sepWPp_seq_lsclro_vm hclf hrof (mid := (blkPl_7).base + bv% (660))
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (memRegion_104_fold s0.sp w0 w1 w2 w3
      (BitVec.ofNat 64 v.length) tmpPtr (BitVec.ofNat 64 v.length)
      (bytesPlacedVtable tmpPtr v.length) (bytesPtr tmpPtr v.length)
      (BitVec.ofNat 64 v.length) (bytesData tmpPtr v.length) 0#64) (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim _ _ _ hvm2]
  refine SepWPp.weaken_pre
    (Entails.of_eq (by
      rw [hspf, stackAt_sliceGen_split s0.sp decodeErrorHookStackW bytesFromVecStack hbfv_le hbnd]
      sep_ac_rfl))
    (phase3_from_0x294_budget hA hmerge hv_len hbs63 hcap2 hfit_res
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))


private theorem phase2_from_0x168_nonempty_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {st : M.σ} {s0 s : State} {R : SepProp}
    {pfx rest0 : List (BitVec 8)} {b0 : BitVec 8} {v' : List (BitVec 8)}
    {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hvar : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
    (hpfx : x.bs = pfx ++ rest0)
    (hle : (b0 :: v').length ≤ rest0.length)
    (hv_take : rest0.take (b0 :: v').length = b0 :: v')
    (hwt : x.wt = .lengthDelimited)
    (hbs63 : x.bs.length < 2 ^ 63)
    (hcap2 : 2 * x.valCap.toNat + 1 ≤ 2 ^ 63)
    (hfit_res : FitsEvents M lim
      (M.stepEvents (if (b0 :: v').length = 0 then [] else rustAllocEvents (b0 :: v').length 1) st)
      (if x.valCap.toNat < (b0 :: v').length then doReserveEvents x.valCap.toNat 0 (b0 :: v').length else []))
    (htmp_ne : tmpPtr ≠ 0#64)
    (hpc : s.pc = (blkPl_7).base + 360#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (b0 :: v').length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx24 : s.readReg64 .x24 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    let st_alloc := M.stepEvents (rustAllocEvents (b0 :: v').length 1) st
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st_alloc s ∗
        (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
          ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
          ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
          ((s0.sp - 120#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 112#64) 32 ∗
          ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
          A.live tmpPtr (b0 :: v').length 1 ∗ memRegion tmpPtr (b0 :: v').length ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x (b0 :: v') (rest0.drop (b0 :: v').length) st s0 R) (NoPanicPost R) := by
  intro st_alloc
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  have hext_le : extHookStack ≤ bmSliceStack decodeErrorHookStackW := by decide
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  set v := b0 :: v'
  have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hv_len : v.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmin_v : (if (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true
      then BitVec.ofNat 64 v.length else BitVec.ofNat 64 rest0.length) = BitVec.ofNat 64 v.length := by
    by_cases hlt : v.length < rest0.length
    · have hult : (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true := by
        simp [BitVec.ult, hlen_toNat, hrest0_toNat, hlt]
      simp [hult]
    · have heq : rest0.length = v.length := by omega
      simp [heq]
  have hrest0_ult_v : (BitVec.ofNat 64 rest0.length).ult (BitVec.ofNat 64 v.length) = false := by
    simp [BitVec.ult, hlen_toNat, hrest0_toNat, hle]
  have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [hlen_toNat] at h2
    exact absurd h2 (by dsimp [v]; omega)
  have hmerge : mergeBytes x.wt x.bs = some (v, rest0.drop v.length) := by
    have hm := mergeBytes_lengthDelimited_ok hwt hvar (by rw [hlen_toNat]; exact hle)
    rwa [hlen_toNat, hv_take] at hm
  have hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl memcpyVmExternSpecX) :=
    memcpy_extern_of_budgetPlaced hA (callerProg := (blkPC_7).rebase (blkPl_7).base H)
  rw [sliceCursorAfter_split_copy x.slot x.ptr x.bs pfx rest0 v.length hpfx hle]
  rw [hv_take]
  have hadv := sliceCursorAfter_advance_fold x.slot x.ptr x.bs pfx rest0 v.length hpfx hle hbs63
  dsimp only at hadv
  rw [hv_take] at hadv
  clear hpfx
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_7).ρ "memcpy")
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
        hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim _ _ _ hvm1]
  rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW extHookStack hext_le hbnd]
  refine SepWPp.bm_call_frame_lscl
    (x := (tmpPtr, x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length), v))
    (T := memRegion tmpPtr v.length ∗ ((x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)) ↦ₛ v) ∗
      stackAt (s0.sp - 224#64) extHookStack)
    hmc hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [memcpyVmExternSpecX, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, hlen_toNat, and_self])
    (by sep_focus)
    (fun _ _ _ => noExit_of_false)
    (fun _ _ => noPanicPost_of_false) ?_
  intro sf_mc hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx21, hx24, hx29, hmin_v]
    at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [memcpyVmExternSpecX, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨_, htr, hvm_mc⟩ => ?_
  rw [← A.pool_transport lim st_alloc _ sf_mc hvm_mc]
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW))
    (by rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW extHookStack hext_le hbnd]; exact Entails.refl _)
    (by sep_focus)
  rw [← LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm]
  apply sepWPp_seq_lsclro_vm hclf hrof (mid := (blkPl_7).base + bv% (572))
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (fold_vecU8Buf_nonempty A.repAlloc tmpPtr v hpos hv_len htmp_ne) (by sep_focus)
    apply SepWP.fold hadv (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim _ _ _ hvm2]
  have hst_eq : st_alloc = M.stepEvents (if v.length = 0 then [] else rustAllocEvents v.length 1) st := by
    simp only [st_alloc, v, Nat.ne_of_gt hpos, ↓reduceIte]
  rw [hst_eq]
  have hcont := phase2_from_0x23c_budget (R := R)
    (tmpPtr := tmpPtr) (w0 := tmpPtr) (w1 := BitVec.ofNat 64 v.length)
    (w2 := BitVec.ofNat 64 v.length) (w3 := bytesMutDataWord (BitVec.ofNat 64 v.length))
    (w4 := w4) (w5 := w5) (w6 := w6) (w80 := w80)
    hA hmerge hv_len hbs63 hcap2 hfit_res
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
    hsp_align
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
    (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
    hcl2 hro2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
    (by simp (config := { decide := true }) only [bytesMutDataWord, wp_norm, arm64_norm, h22f, ProofLib.ofNat_countLeadingZeros64])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f])
  exact SepWPp.weaken_pre
    (Entails.of_eq (by dsimp only [bytesMutDataWord]; simp only [ProofLib.ofNat_countLeadingZeros64]; sep_ac_rfl))
    hcont

private theorem phase2_from_0x0e0_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {v_out rest_out : List (BitVec 8)} {st : M.σ} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hmerge : mergeBytes x.wt x.bs = some (v_out, rest_out))
    (hbs63 : x.bs.length < 2 ^ 63)
    (hcap2 : 2 * x.valCap.toNat + 1 ≤ 2 ^ 63)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents x.valCap.toNat v_out.length))
    (hpc : s.pc = (blkPl_7).base + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st s ∗
        (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x v_out rest_out st s0 R) (NoPanicPost R) := by
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  have hext_le : extHookStack ≤ bmSliceStack decodeErrorHookStackW := by decide
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true := by
    by_contra hnot
    have hule_f : len.ule (BitVec.ofNat 64 rest0.length) = false := Bool.eq_false_iff.mpr hnot
    have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule_f; omega
    rw [mergeBytes_lengthDelimited_underflow hwt hvar hlt] at hmerge
    cases hmerge
  have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
  have hlen_lt32 : len.toNat < 2 ^ 63 := by omega
  dsimp only [sliceCursorAfter]
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_7).base + bv% (280))
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
        sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hule_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim _ _ _ hvm1]
  refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 168#64) 104 ∗
    (A.pool lim st _ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
      stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      savedRegsStack s0.sp s0)) (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPp.unfold_memRegion_168 fun w0 w1 w2 w3 w4 w5 w6 w80 => ?_
  rcases hv : rest0.take len.toNat with _ | ⟨b0, v'⟩
  · have hlen0 : len = 0#64 := by
      have hv_len0 : (rest0.take len.toNat).length = 0 := by rw [hv]; rfl
      rw [List.length_take_of_le hle] at hv_len0
      exact BitVec.eq_of_toNat_eq hv_len0
    have hmerge0 : mergeBytes x.wt x.bs = some ([], rest0) := by
      have hv_len0 : len.toNat = 0 := by rw [hlen0]; rfl
      have hdrop0 : rest0.drop len.toNat = rest0 := by rw [hv_len0]; rfl
      have hm := mergeBytes_lengthDelimited_ok hwt hvar hle
      rwa [hv, hdrop0] at hm
    have hv_eq : v_out = [] ∧ rest_out = rest0 := Option.some.inj (hmerge.symm.trans hmerge0) |> Prod.mk.inj
    rcases hv_eq with ⟨rfl, hrest_eq⟩
    subst rest_out
    clear hv
    have hfit_res0 : FitsEvents M lim
        (M.stepEvents (if ([] : List (BitVec 8)).length = 0 then [] else rustAllocEvents ([] : List (BitVec 8)).length 1) st)
        (if x.valCap.toNat < ([] : List (BitVec 8)).length then doReserveEvents x.valCap.toNat 0 ([] : List (BitVec 8)).length else []) := by
      dsimp only [bytesMergeAllocEvents] at hfit
      exact ((fitsEvents_append M lim _ _ _).mp hfit).2
    have hmin0 : (if (0#64).ult (BitVec.ofNat 64 rest0.length) = true then 0#64 else BitVec.ofNat 64 rest0.length) = 0#64 :=
      bitvec_if_zero_ult_self (BitVec.ofNat 64 rest0.length)
    dsimp only [sliceCursorAfter]
    refine SepWPp.weaken_pre (P' := A.pool lim st _ ∗
      (emp ∗ ((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗ memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ∗
        stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
        memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0))
      (Entails.of_eq (by rw [emp_sepConj]; sep_ac_rfl)) ?_
    apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_7).base + bv% (572))
    by_vm_steps_withSvc (
      wp_steps
      apply SepWP.fold (vecU8Buf_nil_one A.repAlloc) (by sep_focus)
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp, hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim _ _ _ hvm2]
    have hst0 : st = M.stepEvents (if ([] : List (BitVec 8)).length = 0 then [] else rustAllocEvents ([] : List (BitVec 8)).length 1) st := by
      simp only [List.length_nil, ↓reduceIte, AllocCostModel.stepEvents_nil]
    rw [hst0]
    refine SepWPp.weaken_pre
      (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; sep_ac_rfl))
      (phase2_from_0x23c_budget hA hmerge0 (by decide) hbs63 hcap2 hfit_res0
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp, hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, bytesMutDataWord_zero])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
  · have hlen_v : len = BitVec.ofNat 64 (b0 :: v').length := by
      have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      rw [hv_len_eq, BitVec.ofNat_toNat]; rfl
    have hle' : (b0 :: v').length ≤ rest0.length := by
      have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      omega
    have hv_take' : rest0.take (b0 :: v').length = b0 :: v' := by
      have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
      rw [hv_len_eq]; exact hv
    have hmerge1 : mergeBytes x.wt x.bs = some (b0 :: v', rest0.drop (b0 :: v').length) := by
      have hm := mergeBytes_lengthDelimited_ok hwt hvar hle
      have hv_len_eq : len.toNat = (b0 :: v').length := by rw [← hv, List.length_take_of_le hle]
      rwa [hv, hv_len_eq] at hm
    have hv_eq : v_out = b0 :: v' ∧ rest_out = rest0.drop (b0 :: v').length :=
      Option.some.inj (hmerge.symm.trans hmerge1) |> Prod.mk.inj
    rcases hv_eq with ⟨rfl, rfl⟩
    clear hv
    have hpos : 0 < (b0 :: v').length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
    have hv_len : (b0 :: v').length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 (b0 :: v').length).toNat = (b0 :: v').length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmsb : (BitVec.ofNat 64 (b0 :: v').length).getLsbD 63 = false :=
      bitvec_getLsbD_63_of_lt32 hv_len
    have hlen_ne : (BitVec.ofNat 64 (b0 :: v').length == 0#64) = false := by
      apply beq_false_of_ne
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [hlen_toNat] at h2
      exact absurd h2 (by simp)
    have hfit_split := (fitsEvents_append M lim _ _ _).mp (by dsimp only [bytesMergeAllocEvents] at hfit; exact hfit)
    have hfit_al : FitsEvents M lim st (rustAllocEvents (b0 :: v').length 1) := by
      simpa only [Nat.ne_of_gt hpos, ↓reduceIte] using hfit_split.1
    have hfit_res : FitsEvents M lim
        (M.stepEvents (if (b0 :: v').length = 0 then [] else rustAllocEvents (b0 :: v').length 1) st)
        (if x.valCap.toNat < (b0 :: v').length then doReserveEvents x.valCap.toNat 0 (b0 :: v').length else []) :=
      hfit_split.2
    have hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) ((blkPl_7).ρ lsRustNoAllocShimSym)
        (withLsCl lsmpl shimVmExternSpecX) :=
      shim_extern_of_budgetPlaced hA (callerProg := (blkPC_7).rebase (blkPl_7).base H)
    have halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) ((blkPl_7).ρ lsRustAllocSym)
        (withLsCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)) :=
      alloc_extern_of_budgetPlaced hA (callerProg := (blkPC_7).rebase (blkPl_7).base H)
    refine SepWPp.weaken_pre (P' := A.pool lim st _ ∗
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗ memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
        stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
        memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by sep_ac_rfl)) ?_
    apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_7).ρ lsRustNoAllocShimSym)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
          bitvec_getLsbD_63_of_lt32])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim _ _ _ hvm2]
    rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW extHookStack hext_le hbnd]
    refine SepWPp.bm_call_frame_lscl (x := ()) (φ := True)
      (T := stackAt (s0.sp - 224#64) extHookStack)
      hshim hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
        hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
        bitvec_getLsbD_63_of_lt32])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [shimVmExternSpecX, arm64_norm, hsp, pure_true, emp_sepConj])
      trivial (by sep_focus)
      (fun _ _ _ => noExit_of_false)
      (fun _ _ => noPanicPost_of_false) ?_
    intro sf_sh hpcf_sh hrunf_sh hspf_sh hcsf_sh hclf_sh hrof_sh
    obtain ⟨h19_sh, h20_sh, h21_sh, h22_sh, h23_sh, h24_sh, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh⟩ := hcsf_sh
    simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx2, hx19, hx29, hlen_v]
      at hpcf_sh hspf_sh h19_sh h20_sh h21_sh h22_sh h23_sh h24_sh h25_sh h26_sh h27_sh h28_sh h29_sh
    simp (config := { decide := true }) only [shimVmExternSpecX, arm64_norm, hsp]
    refine SepWPp.pure_elim fun ⟨htr_sh, hvm_sh⟩ => ?_
    rw [← A.pool_transport lim st s sf_sh (hvm1.trans (hvm2.trans hvm_sh))]
    refine SepWPp.weaken_pre (P' := A.pool lim st sf_sh ∗
      (stackAt (s0.sp - 224#64) extHookStack ∗
        bmExtraStack s0.sp decodeErrorHookStackW extHookStack ∗
        ((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗ memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
        memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by sep_ac_rfl)) ?_
    apply sepWPp_seq_lsclro_vm hclf_sh hrof_sh (mid := (blkPl_7).ρ lsRustAllocSym)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm3 hcl3 hro3
    rw [← A.pool_transport lim _ _ _ hvm3]
    have hrlay : RustLayoutOk (b0 :: v').length 1 :=
      rustLayoutOk_of_layoutOk (by decide) ⟨hpos, ⟨0, rfl⟩, by simp only [List.length_cons] at hv_len ⊢; omega⟩
    refine SepWPp.bm_call_frame_lscl (x := ((b0 :: v').length, 1, st))
      (T := A.pool lim st _ ∗ stackAt (s0.sp - 224#64) extHookStack)
      halloc hcl3 hro3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hspf_sh, hsp_align]) rfl
      (by dsimp only [rustCliAllocNoOomExternSpecWithStack,
            LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack];
          simp (config := { decide := true }) only [State.sp_setMem, State.sp_setPC, State.sp_setPState, State.sp_writeReg64_of_isSp_false, hspf_sh]; rfl)
      (by exact ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm, hlen_toNat],
                 by simp (config := { decide := true }) only [wp_norm, arm64_norm],
                 hrlay, hfit_al,
                 by simp (config := { decide := true }) only [blkPl_7, wp_norm, arm64_norm, hpcf_sh]⟩)
      (by sep_focus)
      (fun _ _ _ => noExit_of_false)
      (fun _ _ => noPanicPost_of_false) ?_
    intro sf_al hpcf_al hrunf_al hspf_al hcsf_al hclf_al hrof_al
    obtain ⟨h19_al, h20_al, h21_al, h22_al, h23_al, h24_al, h25_al, h26_al, h27_al, h28_al, h29_al⟩ := hcsf_al
    simp (config := { decide := true }) only [arm64_norm, hspf_sh, h19_sh, h21_sh, h24_sh, h29_sh]
      at hpcf_al hspf_al h19_al h20_al h21_al h22_al h23_al h24_al h25_al h26_al h27_al h28_al h29_al
    simp (config := { decide := true }) only [rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
      arm64_norm, htr_sh, htrace, ↓reduceIte]
    refine SepWPp.pure_elim fun ⟨htr_al, h0_64, _⟩ => ?_
    have h0_beq : (sf_al.readReg64 .x0 == 0#64) = false := beq_false_of_ne h0_64
    refine SepWPp.weaken_pre (P' :=
      A.pool lim (M.stepEvents (rustAllocEvents (b0 :: v').length 1) st) sf_al ∗
        (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
          ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
          ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
          ((s0.sp - 120#64) ↦₆₄ w6) ∗ memRegion (s0.sp - 112#64) 32 ∗
          ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
          A.live (sf_al.readReg64 .x0) (b0 :: v').length 1 ∗
          memRegion (sf_al.readReg64 .x0) (b0 :: v').length ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64) 48 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by
        simp (config := { decide := true }) only [arm64_norm, hspf_sh]
        rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW extHookStack hext_le hbnd]
        sep_ac_rfl)) ?_
    dsimp only [sliceCursorAfter]
    apply sepWPp_seq_lsclro_vm hclf_al hrof_al (mid := (blkPl_7).base + bv% (360))
    by_vm_steps_withSvc (
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm4 hcl4 hro4
    rw [← A.pool_transport lim _ _ _ hvm4]
    have hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0) := by rwa [← hlen_v]
    obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (phase2_from_0x168_nonempty_budget hA hvar' hpfx hle' hv_take' hwt hbs63 hcap2 hfit_res h0_64
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf_al])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_al])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
          h25_al, h26_al, h27_al, h28_al, h29_al, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh,
          h25_0, h26_0, h27_0, h28_0, and_self])
        hcl4 hro4
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29_al]))


private theorem phase1_from_0x08c_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {v_out rest_out : List (BitVec 8)} {st : M.σ} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hmerge : mergeBytes x.wt x.bs = some (v_out, rest_out))
    (hbs63 : x.bs.length < 2 ^ 63)
    (hcap2 : 2 * x.valCap.toNat + 1 ≤ 2 ^ 63)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents x.valCap.toNat v_out.length))
    (hpre : VarintSlicePre x.bs)
    (hpc : s.pc = (blkPl_7).base + 140#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx1 : s.readReg64 .x1 = x.ptr)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.bs.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = x.slot)
    (hx21 : s.readReg64 .x21 = x.bufRef)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st s ∗
        (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x v_out rest_out st s0 R) (NoPanicPost R) := by
  rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
  · rw [mergeBytes_of_decodeVarint_none hvar] at hmerge; cases hmerge
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hbs_toNat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hVarintSlice := decode_varint_slice_some_placed_ok_cl
    (callerProg := (blkPC_7).rebase (blkPl_7).base H) (errStack := decodeErrorHookStackW) (by decide)
  dsimp only [sliceCursorAt] at hpc ⊢
  rw [memRegion_48_sret24 (s0.sp - 216#64)]
  apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 76)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim _ _ _ hvm1]
  refine SepWPp.bm_call_frame_lscl
    (x := ({ ret := s0.sp - 216#64, ptr := x.ptr, bs := x.bs }, len, rest0))
    (T := memRegion (s0.sp - 216#64) 24 ∗ (x.ptr ↦ₛ x.bs) ∗
      stackAt (s0.sp - 224#64) (0x50 + decodeErrorHookStackW))
    hVarintSlice hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by dsimp only [decodeVarintSliceSomeSpecGen]; simp (config := { decide := true }) only [State.sp_setMem, State.sp_setPC, State.sp_setPState, State.sp_writeReg64_of_isSp_false, hsp]; rfl)
    (by exact ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp],
               by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1],
               by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8, hbs_toNat],
               hbs63, hpre, hvar⟩)
    (by change _ = _; sep_focus)
    (fun _ _ _ => noExit_of_false)
    (fun _ _ => noPanicPost_of_false) ?_
  intro sf_vs hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx29]
    at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [decodeVarintSliceSomeSpecGen, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨htr, hvm_vs⟩ => ?_
  rw [← A.pool_transport lim st s sf_vs (hvm1.trans hvm_vs)]
  have hrest0_le : rest0.length ≤ x.bs.length := by
    obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
    rw [hpfx, List.length_append]; omega
  have hcons_toNat : (BitVec.ofNat 64 (x.bs.length - rest0.length)).toNat = x.bs.length - rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hult_cons : (BitVec.ofNat 64 x.bs.length).ult (BitVec.ofNat 64 (x.bs.length - rest0.length)) = false := by
    simp [BitVec.ult, hbs_toNat, hcons_toNat]
  have hule_cons : (BitVec.ofNat 64 (x.bs.length - rest0.length)).ule (BitVec.ofNat 64 x.bs.length) = true := by
    simp [BitVec.ule, hbs_toNat, hcons_toNat]
  refine SepWPp.weaken_pre (P' := A.pool lim st sf_vs ∗
    (((s0.sp - 216#64) ↦₆₄ 0#64) ∗ ((s0.sp - 216#64 + 8#64) ↦₆₄ len) ∗
      ((s0.sp - 216#64 + 16#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - rest0.length)) ∗
      memRegion (s0.sp - 216#64 + 24#64) 24 ∗
      (x.ptr ↦ₛ x.bs) ∗ (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 168#64) 104 ∗
      savedRegsStack s0.sp s0))
    (Entails.of_eq (by change _ = _; sep_ac_rfl)) ?_
  apply sepWPp_seq_lsclro_vm hclf hrof (mid := (blkPl_7).base + bv% (224))
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (fold_memRegion_48_sret_ok (s0.sp - 216#64) 0#64 len
      (BitVec.ofNat 64 (x.bs.length - rest0.length))) (by sep_focus)
    apply SepWP.fold (fold_sliceCursorAfter_from_consumed x.slot x.ptr x.bs rest0 hrest0_le) (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim _ _ _ hvm2]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (phase2_from_0x0e0_budget hA hwt hvar hmerge hbs63 hcap2 hfit
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))

private theorem phase1_from_0x398_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {v_out rest_out : List (BitVec 8)} {st : M.σ} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hmerge : mergeBytes x.wt x.bs = some (v_out, rest_out))
    (hbs63 : x.bs.length < 2 ^ 63)
    (hcap2 : 2 * x.valCap.toNat + 1 ≤ 2 ^ 63)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents x.valCap.toNat v_out.length))
    (hpc : s.pc = (blkPl_7).base + 920#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = x.bufRef)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st s ∗
        (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x v_out rest_out st s0 R) (NoPanicPost R) := by
  rcases hvs : varintSlow x.bs with _ | ⟨len, k⟩
  · rw [mergeBytes_of_decodeVarint_none ((varintSlow_none_iff x.bs).mp hvs)] at hmerge; cases hmerge
  obtain ⟨_, hkl, hvar⟩ := (varintSlow_some_iff x.bs len k).mp hvs
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  have hslow_le : 0x40 + decodeErrorHookStackW ≤ bmSliceStack decodeErrorHookStackW := by decide
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hVarintSlow := decode_varint_slow_some_withStack_placed_ok_cl
    (callerProg := (blkPC_7).rebase (blkPl_7).base H) (errStack := decodeErrorHookStackW) (by decide)
  dsimp only [sliceCursorAt] at hpc ⊢
  apply sepWPp_seq_lsclro_vm hcl hro (mid := lsmpl.base 293)
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim _ _ _ hvm1]
  rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW (0x40 + decodeErrorHookStackW) hslow_le hbnd]
  refine SepWPp.bm_call_frame_lscl
    (x := ((x.bufRef, x.slot, x.ptr, x.bs), len, k))
    (T := (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      (x.ptr ↦ₛ x.bs) ∗ stackAt (s0.sp - 224#64) (0x40 + decodeErrorHookStackW))
    hVarintSlow hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by dsimp only [decodeVarintSlowSomeWithStackSpec]; simp (config := { decide := true }) only [State.sp_setMem, State.sp_setPC, State.sp_setPState, State.sp_writeReg64_of_isSp_false, hsp]; rfl)
    (by exact ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21], by omega, hvs⟩)
    (by sep_focus)
    (fun _ _ _ => noExit_of_false)
    (fun _ _ => noPanicPost_of_false) ?_
  intro sf_vs hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx21, hx29]
    at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [decodeVarintSlowSomeWithStackSpec, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf, htr, hvm_vs⟩ => ?_
  rw [← A.pool_transport lim st s sf_vs (hvm1.trans hvm_vs)]
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW))
    (by rw [stackAt_sliceGen_split s0.sp decodeErrorHookStackW (0x40 + decodeErrorHookStackW) hslow_le hbnd]; exact Entails.refl _)
    (by sep_focus)
  refine SepWPp.weaken_pre (P' := A.pool lim st sf_vs ∗
    ((x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 k)) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - k)) ∗
      (x.ptr ↦ₛ x.bs) ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104 ∗
      savedRegsStack s0.sp s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  apply sepWPp_seq_lsclro_vm hclf hrof (mid := (blkPl_7).base + bv% (224))
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (fold_sliceCursorAfter_drop x.slot x.ptr x.bs k hkl) (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm2 hcl2 hro2
  rw [← A.pool_transport lim _ _ _ hvm2]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (phase2_from_0x0e0_budget hA hwt hvar hmerge hbs63 hcap2 hfit
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm,
        h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))

private theorem phase1_from_0x074_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {x : BytesMergeGhost} {v_out rest_out : List (BitVec 8)} {st : M.σ} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hne : x.bs ≠ [])
    (hmerge : mergeBytes x.wt x.bs = some (v_out, rest_out))
    (hbs63 : x.bs.length < 2 ^ 63)
    (hcap2 : 2 * x.valCap.toNat + 1 ≤ 2 ^ 63)
    (hfit : FitsEvents M lim st (bytesMergeAllocEvents x.valCap.toNat v_out.length))
    (hpc : s.pc = (blkPl_7).base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx1 : s.readReg64 .x1 = x.ptr)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.bs.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (A.pool lim st s ∗
        (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
          stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (MergeBudgetPost M A lim x v_out rest_out st s0 R) (NoPanicPost R) := by
  have hbs_toNat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  apply sepWPp_seq_lsclro_vm hcl hro
    (mid := if (10#64).ult (BitVec.ofNat 64 x.bs.length) = true then (blkPl_7).base + bv% (140) else (blkPl_7).base + bv% (128))
  by_vm_steps_withSvc (
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim _ _ _ hvm1]
  by_cases h11 : (10#64).ult (BitVec.ofNat 64 x.bs.length) = true
  · simp only [h11, ↓reduceIte] at hcl1 hro1 ⊢
    have hge11 : 11 ≤ x.bs.length := by
      have : 10 < x.bs.length := by simpa [BitVec.ult, hbs_toNat] using h11
      omega
    exact phase1_from_0x08c_budget hA hwt hmerge hbs63 hcap2 hfit (Or.inl hge11)
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx8, h11])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29])
  · have h11_eq : (10#64).ult (BitVec.ofNat 64 x.bs.length) = false := Bool.eq_false_iff.mpr h11
    simp only [h11_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    dsimp only [sliceCursorAt]
    rw [bm_pointsToBytes_split_last x.ptr x.bs hne hbs63]
    by_cases hlast : (x.bs.getLast hne).getLsbD 7 = true
    · have hlast31 : (((x.bs.getLast hne).signExtend 32).zeroExtend 64).getLsbD 31 = true := by
        rw [signExtend32_zeroExtend64_getLsbD_31, hlast]
      apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_7).base + bv% (920))
      by_vm_steps_withSvc (
        wp_steps
        apply SepWP.fold (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
            (x.ptr ↦ₛ x.bs.dropLast) ∗
            ((x.ptr + BitVec.ofNat 64 x.bs.length + 0xffffffffffffffff#64) ↦₈ x.bs.getLast hne) ⊢
            sliceCursorAt x.slot x.ptr x.bs from by
          unfold sliceCursorAt
          rw [← bm_pointsToBytes_split_last x.ptr x.bs hne hbs63]
          exact Entails.of_eq (by sep_ac_rfl)) (by sep_focus)
        refine SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
      intro hvm2 hcl2 hro2
      rw [← A.pool_transport lim _ _ _ hvm2]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (phase1_from_0x398_budget hA hwt hmerge hbs63 hcap2 hfit
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
          hcl2 hro2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
    · have hlast_eq : (x.bs.getLast hne).getLsbD 7 = false := Bool.eq_false_iff.mpr hlast
      have hlast31 : (((x.bs.getLast hne).signExtend 32).zeroExtend 64).getLsbD 31 = false := by
        rw [signExtend32_zeroExtend64_getLsbD_31, hlast_eq]
      apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_7).base + bv% (140))
      by_vm_steps_withSvc (
        wp_steps
        apply SepWP.fold (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
            (x.ptr ↦ₛ x.bs.dropLast) ∗
            ((x.ptr + BitVec.ofNat 64 x.bs.length + 0xffffffffffffffff#64) ↦₈ x.bs.getLast hne) ⊢
            sliceCursorAt x.slot x.ptr x.bs from by
          unfold sliceCursorAt
          rw [← bm_pointsToBytes_split_last x.ptr x.bs hne hbs63]
          exact Entails.of_eq (by sep_ac_rfl)) (by sep_focus)
        refine SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
      intro hvm2 hcl2 hro2
      rw [← A.pool_transport lim _ _ _ hvm2]
      have hpre : VarintSlicePre x.bs := Or.inr ⟨hne, toNat_le_0x7f_of_getLsbD_7_false hlast_eq⟩
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (phase1_from_0x08c_budget hA hwt hmerge hbs63 hcap2 hfit hpre
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
          hcl2 hro2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))

/-- Relocatable `[LibsignalPlacement]` total-correctness (`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`)
proof of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>` (Block `7`, `bytesMergeStackW`)
for general destination capacity `x.valCap` on `mergeBytes x.wt x.bs = some (v, rest)`. -/
theorem bytes_merge_some_budget_placed_okW [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeSomeBudgetSpecW M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, v, rest, st⟩ R s0 hpc hrun hpre hsp_align =>
    reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMergeSomeBudgetSpecW, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs63, hcap2, hmerge, hfit⟩, hm⟩ := hpre
  have hwt : x.wt = .lengthDelimited := by
    by_contra hne
    rw [mergeBytes_ne_lengthDelimited hne] at hmerge; cases hmerge
  have hbnd : bmTotalStack decodeErrorHookStackW ≤ 2 ^ 64 := by decide
  suffices hwp : SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s0
      (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
        A.pool lim st s0 ∗ stackAt s0.sp bytesMergeStackW)
      (MergeBudgetPost M A lim x v rest st s0 R) (NoPanicPost R) by
    obtain ⟨sf, hsteps, hout⟩ :=
      sepWPp_to_subroutineOutcome_budget (spec := bytesMergeSomeBudgetSpecW M A lim)
        (x := (x, v, rest, st)) hm hL hwp
    refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · exact Or.inl ⟨hret, hcc, hpost⟩
    · exact (not_satisfies_false_sepConj hpan).elim
    · exact (not_satisfies_false_sepConj hex).elim
    · exact (not_satisfies_false_sepConj hoom).elim
  change SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s0
    (vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s0 ∗ stackAt s0.sp (bmTotalStack decodeErrorHookStackW)) _ _
  rw [stackAt_bytesMergeGen_entry s0.sp decodeErrorHookStackW hbnd]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (A.pool lim st s0 ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  have hw0_br :
      (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
    rw [truncate32_and_255_of_setWidth8_eq_two (by rw [hw0, hwt]; rfl)]
    decide
  refine SepWPp.weaken_pre (P' := A.pool lim st s0 ∗
    (((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
      ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
      ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
      ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      stackAt (s0.sp - 224#64) (bmSliceStack decodeErrorHookStackW) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  apply sepWPp_seq_lsclro_vm hcl hro (mid := (blkPl_7).base + bv% (36))
  by_vm_steps_withSvc (
    wp_steps
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    refine SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
  intro hvm1 hcl1 hro1
  rw [← A.pool_transport lim _ _ _ hvm1]
  rcases hbs : x.bs with _ | ⟨b0, bs'⟩
  · rw [hbs, mergeBytes_nil] at hmerge; cases hmerge
  have hbs_ne : x.bs ≠ [] := by simp [hbs]
  have hbs_len' : (b0 :: bs').length < 2 ^ 63 := by simpa [hbs] using hbs63
  have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs').length).toNat = (b0 :: bs').length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen_ne0 : (BitVec.ofNat 64 (b0 :: bs').length == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [hlen_toNat] at h2
    exact absurd h2 (by simp)
  dsimp only [sliceCursorAt]
  rw [pointsToBytes_cons]
  by_cases hb0 : (b0.signExtend 64).getLsbD 63 = false
  · apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_7).base + bv% (64))
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim _ _ _ hvm2]
    have hvar : decodeVarint x.bs = some (b0.signExtend 64, bs') := by
      rw [hbs]; exact decodeVarint_cons_of_signExtend_63_false hb0
    apply sepWPp_seq_lsclro_vm hcl2 hro2 (mid := (blkPl_7).base + bv% (224))
    by_vm_steps_withSvc (
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + 1#64)) ∗
          ((x.slot + 8#64) ↦₆₄ (BitVec.ofNat 64 (b0 :: bs').length - 1#64)) ∗
          (x.ptr ↦₈ b0) ∗ ((x.ptr + 1#64) ↦ₛ bs') ⊢
          sliceCursorAfter x.slot x.ptr x.bs bs' from by
        rw [hbs]; exact fold_sliceCursorAfter_cons x.slot x.ptr b0 bs') (by sep_focus)
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm3 hcl3 hro3
    rw [← A.pool_transport lim _ _ _ hvm3]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (phase2_from_0x0e0_budget hA hwt hvar hmerge hbs63 hcap2 hfit
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
        hcl3 hro3
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
  · have hb0_eq : (b0.signExtend 64).getLsbD 63 = true := Bool.eq_true_of_not_eq_false hb0
    apply sepWPp_seq_lsclro_vm hcl1 hro1 (mid := (blkPl_7).base + bv% (116))
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0_eq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro hvm2 hcl2 hro2
    rw [← A.pool_transport lim _ _ _ hvm2]
    apply SepWPp.fold (T' := sliceCursorAt x.slot x.ptr x.bs)
      (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bs').length) ∗
          (x.ptr ↦₈ b0) ∗ ((x.ptr + 1#64) ↦ₛ bs') ⊢
          sliceCursorAt x.slot x.ptr x.bs from by
        unfold sliceCursorAt
        rw [hbs, pointsToBytes_cons]
        exact Entails.of_eq (by sep_ac_rfl)) (by sep_focus)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (phase1_from_0x074_budget hA hwt hbs_ne hmerge hbs63 hcap2 hfit
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0_eq])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hbs])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))

private theorem ls_subroutine_ok_ro_of_callee_7 [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] {spec : Spec α}
    (h : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base 7) (withLsCodeRoLoaded lsmpl spec) := by
  let specRo : Spec α :=
    { spec with pre := fun x s0 => ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ spec.pre x s0 }
  have h1 : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (withLsCodeLoaded lsmpl specRo) := by
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
    obtain ⟨hcl, hpre_ro⟩ := extract_withLsCodeLoaded hpre
    dsimp only [specRo] at hpre_ro
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_ro
    obtain ⟨hro, hm⟩ := hpre_ro
    have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s0 ∗ R := by
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨⟨hcl, hro⟩, hm⟩
    exact h.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)
  have h2 : subroutine_ok callerProg (lsmpl.base 7) (withLsCodeLoaded lsmpl specRo) :=
    ls_subroutine_ok_of_callee (j := 7) h1
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨⟨hcl, hro⟩, hm⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl specRo).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded, specRo]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hro, hm⟩
  exact h2.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)

/-- Caller-block-polymorphic `withLsCodeRoLoaded` form of `bytes_merge_some_budget_placed_okW`. -/
theorem bytes_merge_some_budget_placed_okW_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeSomeBudgetSpecW M A lim)) :=
  ls_subroutine_ok_ro_of_callee_7 (bytes_merge_some_budget_placed_okW hA)

/-- Fresh-destination (`x.valCap = 0#64`, `x.valBs = []`) specialization of
`bytesMergeSomeBudgetSpecW` (Block `7`, `bytesMergeStackW`). -/
def bytesMergeFreshBudgetSpecW (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BytesMergeGhost × List (BitVec 8) × List (BitVec 8) × M.σ) where
  pre := fun (x, v, rest, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧ x.valCap = 0#64 ∧ x.valBs = [] ∧
      mergeBytes x.wt x.bs = some (v, rest) ∧
      FitsEvents M lim st (bytesMergeAllocEvents 0 v.length)⌝ ∗
      vecU8At A.repAlloc x.valPtr 0#64 x.valBuf [] ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMergeStackW
  post := fun (x, v, rest, st) s0 sf =>
    let cap' := bytesMergeOutCap 0#64 v.length
    let st' := M.stepEvents (bytesMergeEvents 0 v.length) st
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ ptr' : BitVec 64, vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
      A.pool lim st' sf ∗ stackAt s0.sp bytesMergeStackW

theorem bytes_merge_fresh_budget_placed_okW [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeFreshBudgetSpecW M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, v, rest, st⟩ R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcrl, hpre_raw⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMergeFreshBudgetSpecW, sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  obtain ⟨⟨hw0, hx1, hx2, hbs63, hcap0, hbs0, hmerge, hfit⟩, hm⟩ := hpre_raw
  have hpre_some : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMergeSomeBudgetSpecW M A lim)).pre
      (x, v, rest, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, bytesMergeSomeBudgetSpecW]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hx1, hx2, hbs63, by rw [hcap0]; decide, hmerge, by simpa [hcap0] using hfit⟩, ?_⟩
    simpa [hcap0, hbs0] using hm
  refine (bytes_merge_some_budget_placed_okW hA).mono_outcome (x, v, rest, st) R s0 hpc hrun hpre_some hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa [withLsCodeRoLoaded, bytesMergeSomeBudgetSpecW, bytesMergeFreshBudgetSpecW, hcap0] using hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Caller-block-polymorphic `withLsCodeRoLoaded` form of `bytes_merge_fresh_budget_placed_okW`. -/
theorem bytes_merge_fresh_budget_placed_okW_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeFreshBudgetSpecW M A lim)) :=
  ls_subroutine_ok_ro_of_callee_7 (bytes_merge_fresh_budget_placed_okW hA)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget
