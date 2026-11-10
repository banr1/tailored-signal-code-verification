/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Stepping Helpers for `encode<PolynomialDecoder> [local#3]` (Block `455`)

Proves zero-allocation `VmPreserved` budget adapters, `PolyDecoderBudgetInv`, and `2^60`-cap and
exact `2^59`-cap stage steppers on CLI Block `455` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents
   RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
   rustReallocEvents zeroBudgetLimits)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder)
open CryptoVerification.LibsignalSpqrV1.Proto
  (WireType encodeBoolField encodeKey encodeUint32Field)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialDecoderGhost boolByte protoPolynomialDecoderPinnedAt)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedBytes encodeRepeatedStackOf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero ofNat_countLeadingZeros_32
   ofNat_countLeadingZeros_64 ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyDecoderPinnedGhost MsgEnc48CalleeSavedPlaced
   bs0_append_polyDecoderHeaderBytes bs_append_boolField_4_false bs_append_boolField_4_true
   bs_append_polys_of_ne_zero bs_append_polys_of_zero
   bs_append_ptsNeeded_of_ne_zero bs_append_ptsNeeded_of_zero
   encodePolyDecoderMsg encodeVarint_polyDecoder_tag_eq_proto
   msgEnc48RepeatedStackOf msgEnc48SavedFrame
   polyDecoderElemsAt polyDecoderHeaderBytes polyDecoderHeaderBytes_len_bounds
   polyDecoderRestAt polynomialDecoderPBEncodedLen
   polys_field_len_of_ne_zero protoEncodeBoolField_4_true
   ptsNeeded_field_len_of_ne_zero withMsgEnc48CSPlaced)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (cap_beq_len_false_of_lt_placed)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPl_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed
  (blkPl_448 lsProg_448 blkPl_451 lsProg_451)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced (blkPl_493)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_455 lsProg_455)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents encodeVarintEvents_of_spare pushByteStep)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeRepeatedEvents encodeRepeatedSpecOf encodeVarintDetSpecOf
   vecU8ReserveChain_encodeRepeatedStep vecU8ReserveChain_pushBytesStep
   vecU8ReserveChain_reserveStep)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
  (encodeVarint2_fit_placed_ok_of_doReserve)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1PlacedBudget
  (encodeVarint2_det_placed_ok_of_doReserve encode_repeated_1_59_placed_ok_of_callees)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (encodeRepeatedStep pushBytesStep pushBytesStep_snd_eq reserveStep_one_eq_pushByteStep
   sepWP_done_tpidr_placed sepWP_done_vm_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget (VecU8ReserveChain)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
  (step_msg48_encode_repeated_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
  (step_msg48rep_encode_varint_call_placed step_msg48rep_encode_varint_det_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
  (EncodePolyDecoderPinnedEnv polynomialDecoderEncodedLenElemsOutSpec
   step_msg48rep_polyDecLen_call_prog)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
  (step_hdr_1_placed step_polyDecoder_check_isComplete_placed step_polyDecoder_check_polys_placed
   step_polyDecoder_check_ptsNeeded_placed step_polyDecoder_mov_x0_x20_40_placed
   step_polyDecoder_mov_x1_x19_48_placed step_polyDecoder_prep_pts_placed
   step_polyDecoder_prologue_placed step_polyDecoder_push_isComplete_tag_placed
   step_polyDecoder_push_isComplete_val_epilogue_placed
   step_polyDecoder_push_polys_tag_placed step_polyDecoder_push_ptsNeeded_tag_placed
   step_reserve_64_1_placed step_reserve_116_1_placed
   step_reserve_188_1_exact_placed step_reserve_188_1_placed
   step_reserve_228_1_exact_placed step_reserve_228_1_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodeRepeated59ExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
  (encodeRepeated59SpecOf_of_det_placed step_msg48_encode_repeated59_exact_call_placed
   subroutine_ok_encodeRepeated59Exact_of_59_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
  (impossibleEnforcedLimits not_fitsEnv_doReserve_impossible)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32 ProofLib.truncate32_ofNat64
  hwVarintLen_eq_ofNat_varintLen_norm hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  zext64_truncate32 noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm] private theorem blkPl_451_base_eq [LibsignalPlacement] :
    (blkPl_451).base = lsmpl.base 451 := rfl
@[local arm64_norm] private theorem blkPl_460_base_eq [LibsignalPlacement] :
    (blkPl_460).base = lsmpl.base 460 := rfl
@[local arm64_norm] private theorem blkPl_448_base_eq [LibsignalPlacement] :
    (blkPl_448).base = lsmpl.base 448 := rfl
@[local arm64_norm] private theorem blkPl_493_base_eq [LibsignalPlacement] :
    (blkPl_493).base = lsmpl.base 493 := rfl

local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(CryptoVerification.SpqrV1.Prost.MessageEncode.MsgEnc48CalleeSavedPlaced.step $hcs
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) $hinv)

/-! ## 1. Zero-Allocation `VmPreserved` Budget Adapters & Exact Callee Bridges -/

abbrev noAllocCostModel : AllocCostModel where
  σ := Unit; init := (); step := fun _ _ => (); footprint := fun _ => 0; maxDynIvs := fun _ => 0
  stepReserve := fun ev _ => ev.reqBytes + 1; liveBytes := fun _ => 0
  footprint_mono := fun _ _ => Nat.le_refl 0; maxDynIvs_mono := fun _ _ => Nat.le_refl 0
  stepReserve_mono := fun _ _ _ => Nat.le_refl _; req_le_stepReserve := fun _ _ => Nat.le_succ _
  liveBytes_free_le := fun _ _ _ => Nat.le_refl 0

def zeroEnforcedLimits : BudgetLimits :=
  { staticCount := 0, staticBytes := 0, physCap := 0, enforced := true }

def rawVmRecordBudget (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (s0 : State) : RustCliAllocBudget noAllocCostModel where
  pool := fun lim _ s => if lim.enforced then ⌜VmPreserved s0 s⌝ else emp
  live := A.live; block_valid := hblk
  pool_transport := by
    intro lim _ s s' hvm; split_ifs
    · exact congrArg SepProp.pure (propext ⟨fun h => h.trans hvm.symm, fun h => h.trans hvm⟩)
    · rfl
  pool_zero_transport := by
    intro _ _ _ _; dsimp only [zeroBudgetLimits]; simp only [Bool.false_eq_true, ↓reduceIte]

abbrev vmRecordBudget {M : AllocCostModel} (A : RustCliAllocBudget M) (s0 : State) :
    RustCliAllocBudget noAllocCostModel :=
  rawVmRecordBudget A.repAlloc A.block_valid s0

theorem vecU8At_rawVmRecordBudget (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (s0 : State) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At (rawVmRecordBudget A hblk s0).repAlloc v cap ptr bs = vecU8At A v cap ptr bs := rfl

theorem protoPolynomialDecoderPinnedAt_rawVmRecordBudget (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (s0 : State) (g : ProtoPolynomialDecoderGhost) (decA : BitVec 64)
    (dec : ProtoPolynomialDecoder) :
    protoPolynomialDecoderPinnedAt (rawVmRecordBudget A hblk s0).repAlloc g decA dec =
      protoPolynomialDecoderPinnedAt A g decA dec := rfl

theorem vmRecordBudget_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) (s0 : State) :
    (vmRecordBudget A s0).repAlloc = A.repAlloc := rfl

theorem rawVmRecordBudget_pool_zeroEnforced (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (s0 s : State) (st : noAllocCostModel.σ) :
    (rawVmRecordBudget A hblk s0).pool zeroEnforcedLimits st s = ⌜VmPreserved s0 s⌝ := rfl

theorem vmRecordBudget_pool_zeroEnforced {M : AllocCostModel}
    (A : RustCliAllocBudget M) (s0 s : State) (st : noAllocCostModel.σ) :
    (vmRecordBudget A s0).pool zeroEnforcedLimits st s = ⌜VmPreserved s0 s⌝ := rfl

theorem not_fitsEvent_zeroEnforcedLimits (ev : AllocEvent) :
    ¬ FitsEvent noAllocCostModel zeroEnforcedLimits () ev := by
  rintro ⟨_, _, hram, _⟩; dsimp only [noAllocCostModel, zeroEnforcedLimits] at hram; omega

theorem not_fitsEvents_zeroEnforcedLimits_doReserve (d : DoReserveCall) :
    ¬ FitsEvents noAllocCostModel zeroEnforcedLimits () (doReserveEvents d) := by
  dsimp only [doReserveEvents, rustAllocEvents, rustReallocEvents]
  split_ifs <;> intro h <;> exact not_fitsEvent_zeroEnforcedLimits _ h.1

theorem vacuous_doReserve2_placed_ok [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {resStack : Nat} (B : RustCliAllocBudget noAllocCostModel) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack B zeroEnforcedLimits)) := by
  refine subroutine_ok_outcome_intro fun ⟨d, st⟩ R s _ _ hpre _ => ?_
  dsimp only [withLsCodeLoaded, doReserve2SpecOf] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨_, hpre⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, _, _, _, hEnv⟩, _⟩; cases st
  exact False.elim (not_fitsEvents_zeroEnforcedLimits_doReserve d ((fitsEnv_doReserve_iff d).mp hEnv))

theorem doReserve2_impossible_ok [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel} (B : RustCliAllocBudget M) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack B impossibleEnforcedLimits)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 _ _ hpre _ => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨_, hpre⟩ := hpre
  dsimp only [doReserve2SpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1 with ⟨_, _, _, _, hfits⟩
  exact (not_fitsEnv_doReserve_impossible st x hfits).elim

theorem encodeVarint2_fit_impossible_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (B : RustCliAllocBudget M) (H : LibsignalHooks) :
    subroutine_ok (lsProg_451 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack B impossibleEnforcedLimits)) :=
  encodeVarint2_fit_placed_ok_of_doReserve hres B impossibleEnforcedLimits H
    (doReserve2_impossible_ok B)

theorem encode_repeated_1_59_exact_impossible_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 80 < 2 ^ 64) {M : AllocCostModel}
    (B : RustCliAllocBudget M) {H : LibsignalHooks}
    (hmc : HookSat H spqrMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_448 H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59ExactSpecOf resStack B impossibleEnforcedLimits)) :=
  subroutine_ok_encodeRepeated59Exact_of_59_placed
    (encodeRepeated59SpecOf_of_det_placed
      (encode_repeated_1_59_placed_ok_of_callees hres
        (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
          (encodeVarint2_det_placed_ok_of_doReserve (by omega) B impossibleEnforcedLimits H
            (doReserve2_impossible_ok B)))
        (doReserve2_impossible_ok B)
        (spqr_hook_ok_of_mem hmc)))

/-! ## 2. `PolyDecoderBudgetInv` & Part 1 (`2^60` Cap) Stage Steppers on Block `455` -/

structure PolyDecoderBudgetInv (M : AllocCostModel) (lim : BudgetLimits)
    (x : EncodePolyDecoderPinnedGhost) (st0 : M.σ) (curCap : Nat)
    (accEvs : List AllocEvent) : Prop where
  fitsEnv : FitsEnv M lim st0 (EncodePolyDecoderPinnedEnv x)
  chain : VecU8ReserveChain x.cap.toNat curCap
    (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length) accEvs

theorem PolyDecoderBudgetInv.init {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ}
    (hEnv : FitsEnv M lim st0 (EncodePolyDecoderPinnedEnv x)) :
    PolyDecoderBudgetInv M lim x st0 x.cap.toNat [] :=
  ⟨hEnv, .nil _ _⟩

theorem PolyDecoderBudgetInv.fits_pushBytes {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent} (n : Nat)
    (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + n ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length) :
    FitsEvents M lim (M.stepEvents accEvs st0)
      (pushBytesStep n curCap.toNat curBs.length).2 := by
  have hstep := vecU8ReserveChain_pushBytesStep n curCap.toNat curBs.length _ hle
  have hall := inv.fitsEnv _ ⟨_, inv.chain.trans (Nat.le_refl _) hstep⟩
  exact ((fitsEvents_append M lim accEvs _ st0).mp hall).2

theorem PolyDecoderBudgetInv.step_pushBytes {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {curCap nextCap : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent} (n : Nat)
    (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + n ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hcap_eq : nextCap.toNat = (pushBytesStep n curCap.toNat curBs.length).1) :
    PolyDecoderBudgetInv M lim x st0 nextCap.toNat
      (accEvs ++ (pushBytesStep n curCap.toNat curBs.length).2) := by
  have hstep := vecU8ReserveChain_pushBytesStep n curCap.toNat curBs.length _ hle
  rw [← hcap_eq] at hstep
  exact ⟨inv.fitsEnv, inv.chain.trans (Nat.le_refl _) hstep⟩

theorem PolyDecoderBudgetInv.fits_varint {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {curCap curPtr val : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent}
    (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + (encodeVarint val).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length) :
    FitsEvents M lim (M.stepEvents accEvs st0)
      (encodeVarintEvents (EncodeVarintGhost.mk val x.v curCap curPtr curBs)) := by
  simpa only [encodeVarintEvents, pushBytesStep_snd_eq] using
    inv.fits_pushBytes (encodeVarint val).length hle

theorem PolyDecoderBudgetInv.step_varint {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {curCap nextCap val : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent}
    (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + (encodeVarint val).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hcap_eq : nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1) :
    PolyDecoderBudgetInv M lim x st0 nextCap.toNat
      (accEvs ++ (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2) :=
  inv.step_pushBytes (encodeVarint val).length hle hcap_eq

theorem PolyDecoderBudgetInv.fits_pushByte {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent}
    (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + 1 ≤ x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length) :
    FitsEvents M lim (M.stepEvents accEvs st0) (pushByteStep curCap.toNat curBs.length).2 := by
  rw [← reserveStep_one_eq_pushByteStep]
  have hstep := vecU8ReserveChain_reserveStep (cap := curCap.toNat) hle
  have hall := inv.fitsEnv _ ⟨_, inv.chain.trans (Nat.le_refl _) hstep⟩
  exact ((fitsEvents_append M lim accEvs _ st0).mp hall).2

theorem PolyDecoderBudgetInv.step_pushByte {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {curCap nextCap : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent}
    (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + 1 ≤ x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hcap_eq : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    PolyDecoderBudgetInv M lim x st0 nextCap.toNat
      (accEvs ++ (pushByteStep curCap.toNat curBs.length).2) := by
  rw [← reserveStep_one_eq_pushByteStep] at hcap_eq ⊢
  have hstep := vecU8ReserveChain_reserveStep (cap := curCap.toNat) hle
  rw [← hcap_eq] at hstep
  exact ⟨inv.fitsEnv, inv.chain.trans (Nat.le_refl _) hstep⟩

theorem PolyDecoderBudgetInv.fits_repeated {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {curCap curPtr base : BitVec 64}
    {elems : List (BitVec 64 × List (BitVec 8))} {curBs : List (BitVec 8)}
    {accEvs : List AllocEvent} {tag : Nat}
    (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length) :
    FitsEvents M lim (M.stepEvents accEvs st0)
      (encodeRepeatedEvents (EncodeRepeatedGhost.mk tag base elems x.v curCap curPtr curBs)) := by
  have hstep := vecU8ReserveChain_encodeRepeatedStep tag curCap.toNat curBs.length _ (elems.map Prod.snd) hle
  have hall := inv.fitsEnv _ ⟨_, inv.chain.trans (Nat.le_refl _) hstep⟩
  exact ((fitsEvents_append M lim accEvs _ st0).mp hall).2

theorem PolyDecoderBudgetInv.step_repeated {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodePolyDecoderPinnedGhost} {st0 : M.σ} {curCap nextCap : BitVec 64}
    {elems : List (BitVec 64 × List (BitVec 8))} {curBs : List (BitVec 8)}
    {accEvs : List AllocEvent} {tag : Nat}
    (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hcap_eq : nextCap.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).1) :
    PolyDecoderBudgetInv M lim x st0 nextCap.toNat
      (accEvs ++ (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).2) := by
  have hstep := vecU8ReserveChain_encodeRepeatedStep tag curCap.toNat curBs.length _ (elems.map Prod.snd) hle
  rw [← hcap_eq] at hstep
  exact ⟨inv.fitsEnv, inv.chain.trans (Nat.le_refl _) hstep⟩

theorem step_pd1_hdr_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} {s0 s : State}
    (hencLen : subroutine_ok (lsProg_455 H) (blkPl_493).base
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A.repAlloc)))
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (x : EncodePolyDecoderPinnedGhost) (st0 : M.σ) (sp : BitVec 64)
    (inv0 : PolyDecoderBudgetInv M lim x st0 x.cap.toNat [])
    (hlen_lt : polynomialDecoderPBEncodedLen x.dec < 2 ^ 64)
    (hrem : x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hfit_hdr : x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length ≤ x.cap.toNat ∨
      x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length + 10 < 2 ^ 62)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_455).base) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = x.tag) (hx1 : s.readReg64 .x1 = x.decA) (hx2 : s.readReg64 .x2 = x.v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialDecoderPinnedAt A.repAlloc x.g x.decA x.dec ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s ∗
      stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64)
      (ptsElems : List (BitVec 64 × List (BitVec 8))) (evs1 : List AllocEvent),
      ptsElems.map Prod.snd = x.dec.pts → x.dec.pts.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_455).base + 56#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = x.v → sm.readReg64 .x20 = x.decA →
      MsgEnc48CalleeSavedPlaced s0 sm → x.cap.toNat ≤ cap1.toNat →
      (x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length ≤ x.cap.toNat →
        cap1 = x.cap ∧ ptr1 = x.ptr) →
      PolyDecoderBudgetInv M lim x st0 cap1.toNat evs1 →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
          polyDecoderRestAt A.repAlloc x.decA x.g ptsElems ∗
          vecU8At A.repAlloc x.v cap1 ptr1 (x.bs ++ polyDecoderHeaderBytes x.tag x.dec) ∗
          A.pool lim (M.stepEvents evs1 st0) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  have hfits0 := inv0.fits_pushBytes (curCap := x.cap) (curBs := x.bs)
    (polyDecoderHeaderBytes x.tag x.dec).length hrem
  dsimp only [AllocCostModel.stepEvents] at hfits0
  refine step_hdr_1_placed hres A lim H hencLen hencVarint x.tag x.decA x.v x.cap x.ptr sp
    x.g x.dec x.bs st0 hlen_lt hfit_hdr hfits0 hhs0 hpc hrun hsp halign htr hw0 hx1 hx2 hcs hP ?_
  intro sm sv3 cap1 ptr1 ptsElems hpts_eq hpts_lt hpcm hrunm hspm htrm hx19m hx20m hcsm
    hge1 hpres1 hcap1_eq
  have inv1 := inv0.step_pushBytes (curCap := x.cap) (curBs := x.bs)
    (polyDecoderHeaderBytes x.tag x.dec).length hrem hcap1_eq
  rw [List.nil_append] at inv1
  exact hnext sm sv3 cap1 ptr1 ptsElems _ hpts_eq hpts_lt hpcm hrunm hspm htrm
    hx19m hx20m hcsm hge1 hpres1 inv1

theorem step_ptsNeeded_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (x : EncodePolyDecoderPinnedGhost) (st0 : M.σ) (curCap curPtr sp : BitVec 64)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (accEvs : List AllocEvent) (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hrem : curBs.length + (encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hfit_pn : curBs.length + (encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤ curCap.toNat ∨
      curBs.length + (encodeUint32Field 1#32 x.dec.ptsNeeded).length + 10 < 2 ^ 62)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 56#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64) (nextEvs : List AllocEvent),
      sm.pc = (blkPl_455).base + 108#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = x.v → sm.readReg64 .x20 = x.decA →
      MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      PolyDecoderBudgetInv M lim x st0 nextCap.toNat nextEvs →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
          vecU8At A.repAlloc x.v nextCap nextPtr (curBs ++ encodeUint32Field 1#32 x.dec.ptsNeeded) ∗
          A.pool lim (M.stepEvents nextEvs st0) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  refine step_polyDecoder_check_ptsNeeded_placed H x.decA x.v sp x.g x.dec ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvmp1
  rw [← A.pool_of_vmPreserved hvmp1]
  cases hpn : (x.dec.ptsNeeded == 0#32)
  · simp only [hpn, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pn, hge2_pn⟩ := ptsNeeded_field_len_of_ne_zero x.dec hpn
    have hle1 : curBs.length + 1 ≤
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length := by omega
    refine step_reserve_64_1_placed hres A lim H hdoReserve x.decA x.v curCap curPtr sp curBs x.dec
      (M.stepEvents accEvs st0) (by omega) (inv.fits_pushByte hle1)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx19_1 hx20_1 hcs1
      (F := polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗ F) (by sep_ac_rfl) ?_
    intro s2 cap12 ptr12 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      hlt12 hge12 hpres12 hcap12_eq
    have inv12 := inv.step_pushByte hle1 hcap12_eq
    set evs12 := accEvs ++ (pushByteStep curCap.toNat curBs.length).2
    have hev12 :
        M.stepEvents (pushByteStep curCap.toNat curBs.length).2 (M.stepEvents accEvs st0) =
          M.stepEvents evs12 st0 := (M.stepEvents_append accEvs _ st0).symm
    rw [hev12]
    refine step_polyDecoder_push_ptsNeeded_tag_placed A.repAlloc H x.decA x.v cap12 ptr12 sp
      curBs x.dec hlt12 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      (F := A.pool lim (M.stepEvents evs12 st0) s2 ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvmp3
    rw [← A.pool_of_vmPreserved hvmp3]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp3' hinv3; rw [← A.pool_of_vmPreserved hvmp3']
      set pnVal := x.dec.ptsNeeded.zeroExtend 64
      have hlen_bsK : (curBs ++ [0x08#8]).length = curBs.length + 1 := by
        rw [List.length_append, List.length_singleton]
      have hle_var : (curBs ++ [0x08#8]).length + (encodeVarint pnVal).length ≤
          x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length := by
        rw [hlen_bsK]; omega
      have hfit_var : (curBs ++ [0x08#8]).length + (encodeVarint pnVal).length ≤ cap12.toNat ∨
          (curBs ++ [0x08#8]).length + 10 < 2 ^ 62 := by
        rw [hlen_bsK]
        rcases hfit_pn with h | h
        · left; obtain ⟨rfl, _⟩ := hpres12 (by omega); omega
        · right; omega
      refine step_msg48rep_encode_varint_det_call_placed hres A lim hencVarint
        pnVal x.v cap12 ptr12 sp ((blkPl_455).base + 108#64) (curBs ++ [0x08#8])
        (M.stepEvents evs12 st0) hfit_var (inv12.fits_varint hle_var)
        (F := polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [pnVal, arm64_norm, *]) (by simp only [arm64_norm, *])
        (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
      intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge2 hpres2 hcap2_eq
      have inv2 := inv12.step_varint hle_var hcap2_eq
      set nextEvs := evs12 ++
        (pushBytesStep (encodeVarint pnVal).length cap12.toNat (curBs ++ [0x08#8]).length).2
      have hev2 :
          M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk pnVal x.v cap12 ptr12
              (curBs ++ [0x08#8]))) (M.stepEvents evs12 st0) =
            M.stepEvents nextEvs st0 := by
        simp only [nextEvs, encodeVarintEvents, pushBytesStep_snd_eq, ← M.stepEvents_append]
      rw [hev2, bs_append_ptsNeeded_of_ne_zero curBs x.dec hpn]
      have hx19_4 : s4.readReg64 .x19 = x.v := by rw [hcs34.1]; simp only [arm64_norm, *]
      have hx20_4 : s4.readReg64 .x20 = x.decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext s4 nextCap nextPtr nextEvs hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
          (Nat.le_trans hge12 hge2) ?_ inv2)
      intro hspare
      obtain ⟨rfl, rfl⟩ := hpres12 (by omega)
      exact hpres2 (by rw [hlen_bsK]; omega))
  · simp only [hpn, ↓reduceIte] at hpc1
    rw [← bs_append_ptsNeeded_of_zero curBs x.dec hpn]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 curCap curPtr accEvs hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) inv)

theorem step_polys_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (x : EncodePolyDecoderPinnedGhost) (st0 : M.σ) (curCap curPtr sp : BitVec 64)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (accEvs : List AllocEvent) (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hrem : curBs.length + (encodeUint32Field 2#32 x.dec.polys).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hfit_pl : curBs.length + (encodeUint32Field 2#32 x.dec.polys).length ≤ curCap.toNat ∨
      curBs.length + (encodeUint32Field 2#32 x.dec.polys).length + 10 < 2 ^ 62)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 108#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64) (nextEvs : List AllocEvent),
      sm.pc = (blkPl_455).base + 160#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = x.v → sm.readReg64 .x20 = x.decA →
      MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeUint32Field 2#32 x.dec.polys).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      PolyDecoderBudgetInv M lim x st0 nextCap.toNat nextEvs →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
          vecU8At A.repAlloc x.v nextCap nextPtr (curBs ++ encodeUint32Field 2#32 x.dec.polys) ∗
          A.pool lim (M.stepEvents nextEvs st0) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  refine step_polyDecoder_check_polys_placed H x.decA x.v sp x.g x.dec ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvmp1
  rw [← A.pool_of_vmPreserved hvmp1]
  cases hpl : (x.dec.polys == 0#32)
  · simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pl, hge2_pl⟩ := polys_field_len_of_ne_zero x.dec hpl
    have hle1 : curBs.length + 1 ≤
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length := by omega
    refine step_reserve_116_1_placed hres A lim H hdoReserve x.decA x.v curCap curPtr sp curBs x.dec
      (M.stepEvents accEvs st0) (by omega) (inv.fits_pushByte hle1)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx19_1 hx20_1 hcs1
      (F := polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗ F) (by sep_ac_rfl) ?_
    intro s2 cap12 ptr12 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      hlt12 hge12 hpres12 hcap12_eq
    have inv12 := inv.step_pushByte hle1 hcap12_eq
    set evs12 := accEvs ++ (pushByteStep curCap.toNat curBs.length).2
    have hev12 :
        M.stepEvents (pushByteStep curCap.toNat curBs.length).2 (M.stepEvents accEvs st0) =
          M.stepEvents evs12 st0 := (M.stepEvents_append accEvs _ st0).symm
    rw [hev12]
    refine step_polyDecoder_push_polys_tag_placed A.repAlloc H x.decA x.v cap12 ptr12 sp
      curBs x.dec hlt12 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      (F := A.pool lim (M.stepEvents evs12 st0) s2 ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvmp3
    rw [← A.pool_of_vmPreserved hvmp3]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp3' hinv3; rw [← A.pool_of_vmPreserved hvmp3']
      set plVal := x.dec.polys.zeroExtend 64
      have hlen_bsK : (curBs ++ [0x10#8]).length = curBs.length + 1 := by
        rw [List.length_append, List.length_singleton]
      have hle_var : (curBs ++ [0x10#8]).length + (encodeVarint plVal).length ≤
          x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length := by
        rw [hlen_bsK]; omega
      have hfit_var : (curBs ++ [0x10#8]).length + (encodeVarint plVal).length ≤ cap12.toNat ∨
          (curBs ++ [0x10#8]).length + 10 < 2 ^ 62 := by
        rw [hlen_bsK]
        rcases hfit_pl with h | h
        · left; obtain ⟨rfl, _⟩ := hpres12 (by omega); omega
        · right; omega
      refine step_msg48rep_encode_varint_det_call_placed hres A lim hencVarint
        plVal x.v cap12 ptr12 sp ((blkPl_455).base + 160#64) (curBs ++ [0x10#8])
        (M.stepEvents evs12 st0) hfit_var (inv12.fits_varint hle_var)
        (F := polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [plVal, arm64_norm, *]) (by simp only [arm64_norm, *])
        (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
      intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge2 hpres2 hcap2_eq
      have inv2 := inv12.step_varint hle_var hcap2_eq
      set nextEvs := evs12 ++
        (pushBytesStep (encodeVarint plVal).length cap12.toNat (curBs ++ [0x10#8]).length).2
      have hev2 :
          M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk plVal x.v cap12 ptr12
              (curBs ++ [0x10#8]))) (M.stepEvents evs12 st0) =
            M.stepEvents nextEvs st0 := by
        simp only [nextEvs, encodeVarintEvents, pushBytesStep_snd_eq, ← M.stepEvents_append]
      rw [hev2, bs_append_polys_of_ne_zero curBs x.dec hpl]
      have hx19_4 : s4.readReg64 .x19 = x.v := by rw [hcs34.1]; simp only [arm64_norm, *]
      have hx20_4 : s4.readReg64 .x20 = x.decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext s4 nextCap nextPtr nextEvs hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
          (Nat.le_trans hge12 hge2) ?_ inv2)
      intro hspare
      obtain ⟨rfl, rfl⟩ := hpres12 (by omega)
      exact hpres2 (by rw [hlen_bsK]; omega))
  · simp only [hpl, ↓reduceIte] at hpc1
    rw [← bs_append_polys_of_zero curBs x.dec hpl]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 curCap curPtr accEvs hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) inv)

theorem step_pts_1_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} {s0 s : State}
    (hencRep : subroutine_ok (lsProg_455 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A lim)))
    (x : EncodePolyDecoderPinnedGhost) (st0 : M.σ) (curCap curPtr sp : BitVec 64)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (accEvs : List AllocEvent) (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hpts_eq : ptsElems.map Prod.snd = x.dec.pts) (hpts_lt : x.dec.pts.length < 2 ^ 58)
    (hrem : curBs.length + (encodeRepeatedBytes 3 x.dec.pts).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hfit_pts : curBs.length + (encodeRepeatedBytes 3 x.dec.pts).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes 3 x.dec.pts).length + 10 < 2 ^ 62)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 160#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64) (nextEvs : List AllocEvent),
      sm.pc = (blkPl_455).base + 176#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = x.v → sm.readReg64 .x20 = x.decA →
      MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes 3 x.dec.pts).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      PolyDecoderBudgetInv M lim x st0 nextCap.toNat nextEvs →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
          vecU8At A.repAlloc x.v nextCap nextPtr (curBs ++ encodeRepeatedBytes 3 x.dec.pts) ∗
          A.pool lim (M.stepEvents nextEvs st0) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  have hpts_len : ptsElems.length = x.dec.pts.length := by rw [← hpts_eq, List.length_map]
  refine step_polyDecoder_prep_pts_placed H x.decA x.v sp x.g x.dec ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1 hvmp1
  rw [← A.pool_of_vmPreserved hvmp1]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1' hinv1; rw [← A.pool_of_vmPreserved hvmp1']
    have hrem_e : curBs.length + (encodeRepeatedBytes 3 (ptsElems.map Prod.snd)).length ≤
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length := by
      simpa only [hpts_eq] using hrem
    refine step_msg48_encode_repeated_call_placed A lim hencRep 3 x.g.pts.ptr x.v curCap curPtr sp
      ((blkPl_455).base + 176#64) ptsElems curBs (M.stepEvents accEvs st0)
      (by decide) (by decide) (by rw [hpts_len]; exact hpts_lt)
      (by simpa only [hpts_eq] using hfit_pts) (inv.fits_repeated hrem_e)
      (F := ((x.decA + 8#64) ↦₆₄ x.g.pts.ptr) ∗
        ((x.decA + 16#64) ↦₆₄ BitVec.ofNat 64 x.dec.pts.length) ∗
        ((x.decA + 24#64) ↦₃₂ x.dec.ptsNeeded) ∗
        ((x.decA + 28#64) ↦₃₂ x.dec.polys) ∗
        ((x.decA + 32#64) ↦₈ boolByte x.dec.isComplete) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by rw [hpts_len]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (cs_step hcs1 hinv1)
      (by dsimp only [polyDecoderElemsAt]; sep_ac_rfl) ?_
    intro s2 nextCap nextPtr hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2 hcap2_eq
    have inv2 := inv.step_repeated hrem_e hcap2_eq
    set nextEvs := accEvs ++
      (encodeRepeatedStep 3 curCap.toNat curBs.length (ptsElems.map Prod.snd)).2
    have hev2 :
        M.stepEvents (encodeRepeatedEvents
            (EncodeRepeatedGhost.mk 3 x.g.pts.ptr ptsElems x.v curCap curPtr curBs))
          (M.stepEvents accEvs st0) = M.stepEvents nextEvs st0 := by
      simp only [nextEvs, encodeRepeatedEvents, ← M.stepEvents_append]
    rw [hev2]
    have hx19_2 : s2.readReg64 .x19 = x.v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = x.decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
    simp only [hpts_eq] at hpres2 ⊢
    exact SepWPp.weaken_pre (by dsimp only [polyDecoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext s2 nextCap nextPtr nextEvs hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2 inv2))

theorem step_isComplete_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)}
    {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (x : EncodePolyDecoderPinnedGhost) (st0 : M.σ) (curCap curPtr sp sv3 : BitVec 64)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (accEvs : List AllocEvent) (inv : PolyDecoderBudgetInv M lim x st0 curCap.toNat accEvs)
    (hrem : curBs.length + (encodeBoolField 4#32 x.dec.isComplete).length ≤
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length)
    (hfit_ic : curBs.length + (encodeBoolField 4#32 x.dec.isComplete).length ≤ curCap.toNat ∨
      curBs.length + (encodeBoolField 4#32 x.dec.isComplete).length + 10 < 2 ^ 62)
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 176#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64) (nextEvs : List AllocEvent),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeBoolField 4#32 x.dec.isComplete).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      PolyDecoderBudgetInv M lim x st0 nextCap.toNat nextEvs →
      ∀ (P_f : SepProp),
        (P_f ⊢ (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
          vecU8At A.repAlloc x.v nextCap nextPtr (curBs ++ encodeBoolField 4#32 x.dec.isComplete) ∗
          A.pool lim (M.stepEvents nextEvs st0) sf ∗
          stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) →
        Q sf P_f) :
    SepWPp (lsProg_455 H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  refine step_polyDecoder_check_isComplete_placed hres H x.decA x.v sp sv3 x.g x.dec ptsElems
    hpc hrun hsp halign htr hx19 hx20 hcs
    (F := vecU8At A.repAlloc x.v curCap curPtr curBs ∗
      A.pool lim (M.stepEvents accEvs st0) s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_ ?_
  · intro hc sf hpcf hrunf hspf htrf hccf hcsf hvmp
    have hpool_eq : A.pool lim (M.stepEvents accEvs st0) s =
        A.pool lim (M.stepEvents accEvs st0) sf := (A.pool_of_vmPreserved hvmp).symm
    have hbs_eq : curBs ++ encodeBoolField 4#32 x.dec.isComplete = curBs := by
      rw [hc, bs_append_boolField_4_false curBs]
    exact hnext sf curCap curPtr accEvs hpcf hrunf hspf htrf hccf hcsf
      (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) inv _
      (by rw [hpool_eq, hbs_eq]; exact Entails.of_eq (by sep_ac_rfl))
  · intro hc s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hvmp1
    rw [← A.pool_of_vmPreserved hvmp1]
    have hlen_ic : (encodeBoolField 4#32 x.dec.isComplete).length = 2 := by
      rw [hc]; decide
    have hle1 : curBs.length + 1 ≤
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length := by omega
    refine step_reserve_188_1_placed hres128 A lim H hdoReserve x.decA x.v curCap curPtr sp
      curBs (M.stepEvents accEvs st0)
      (by rcases hfit_ic with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
      (inv.fits_pushByte hle1)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
      (F := polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by sep_ac_rfl) ?_
    intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hx1_2 hx8_2 hx19_2 hx20_2 hcs2
      hlt1 hge1 hpres1 hcap1_eq
    have inv1 := inv.step_pushByte hle1 hcap1_eq
    set evs1 := accEvs ++ (pushByteStep curCap.toNat curBs.length).2
    have hev1 :
        M.stepEvents (pushByteStep curCap.toNat curBs.length).2 (M.stepEvents accEvs st0) =
          M.stepEvents evs1 st0 := (M.stepEvents_append accEvs _ st0).symm
    rw [hev1]
    refine step_polyDecoder_push_isComplete_tag_placed A.repAlloc H x.decA x.v cap1 ptr1 sp
      curBs hlt1 hpc2 hrun2 hsp2 htr2 hx1_2 hx8_2 hx19_2 hx20_2 hcs2
      (F := A.pool lim (M.stepEvents evs1 st0) s2 ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx8_3 hx9_3 hx10_3 hx19_3 hx20_3 hz3 hcs3 hvmp3
    rw [← A.pool_of_vmPreserved hvmp3]
    have hlen_bs1 : (curBs ++ [0x20#8]).length = curBs.length + 1 := by
      rw [List.length_append, List.length_singleton]
    have hle2 : (curBs ++ [0x20#8]).length + 1 ≤
        x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length := by
      rw [hlen_bs1]; omega
    have hfit2 : (curBs ++ [0x20#8]).length + 1 ≤ cap1.toNat ∨
        (curBs ++ [0x20#8]).length + 10 < 2 ^ 62 := by
      rw [hlen_bs1]
      rcases hfit_ic with h | h
      · left; obtain ⟨rfl, _⟩ := hpres1 (by omega); omega
      · right; omega
    refine step_reserve_228_1_placed hres128 A lim H hdoReserve x.decA x.v cap1 ptr1 sp
      (curBs ++ [0x20#8]) (M.stepEvents evs1 st0) hfit2 (inv1.fits_pushByte hle2)
      hpc3 hrun3 hsp3 halign htr3 hx8_3 hx9_3 hx10_3 hx19_3 hx20_3 hz3 hcs3
      (F := polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by sep_ac_rfl) ?_
    intro s4 cap2 ptr2 hpc4 hrun4 hsp4 htr4 hx9_4 hx10_4 hx19_4 _hx20_4 hcs4
      hlt2 hge2 hpres2 hcap2_eq
    have inv2 := inv1.step_pushByte hle2 hcap2_eq
    set evs2 := evs1 ++ (pushByteStep cap1.toNat (curBs ++ [0x20#8]).length).2
    have hev2 :
        M.stepEvents (pushByteStep cap1.toNat (curBs ++ [0x20#8]).length).2
          (M.stepEvents evs1 st0) = M.stepEvents evs2 st0 :=
      (M.stepEvents_append evs1 _ st0).symm
    rw [hev2]
    refine step_polyDecoder_push_isComplete_val_epilogue_placed hres A.repAlloc H
      x.v cap2 ptr2 sp sv3 (curBs ++ [0x20#8]) hlt2
      hpc4 hrun4 hsp4 halign htr4 hx9_4 hx10_4 hx19_4 hcs4
      (F := A.pool lim (M.stepEvents evs2 st0) s4 ∗
        polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗ F)
      (by sep_ac_rfl) ?_
    intro sf hpcf hrunf hspf htrf hccf hcsf hvmpf
    have hpool_eq : A.pool lim (M.stepEvents evs2 st0) s4 =
        A.pool lim (M.stepEvents evs2 st0) sf := (A.pool_of_vmPreserved hvmpf).symm
    have hbs_eq : (curBs ++ [0x20#8]) ++ [0x01#8] =
        curBs ++ encodeBoolField 4#32 x.dec.isComplete := by
      rw [hc, bs_append_boolField_4_true curBs]
    refine hnext sf cap2 ptr2 evs2 hpcf hrunf hspf htrf hccf hcsf
      (Nat.le_trans hge1 hge2) ?_ inv2 _
      (by rw [hpool_eq, hbs_eq]; exact Entails.of_eq (by sep_ac_rfl))
    intro hspare
    obtain ⟨rfl, rfl⟩ := hpres1 (by omega)
    exact hpres2 (by rw [hlen_bs1]; omega)

/-! ## 3. Part 2 (`2^59` Exact Cap) Stage Steppers on Block `455` -/

private theorem pool_step {M : AllocCostModel} (B : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s1 s2 : State} (h : VmPreserved s1 s2) :
    B.pool lim st s1 = B.pool lim st s2 :=
  (B.pool_of_vmPreserved h).symm

theorem step_pd1_hdr_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_455 H) (blkPl_493).base
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec B.repAlloc)))
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (tag : BitVec 32) (decA v cap0 ptr0 sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (bs0 : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_455).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialDecoderPinnedAt B.repAlloc g decA pb ∗
      vecU8At B.repAlloc v cap0 ptr0 bs0 ∗ B.pool lim curSt s ∗
      stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64)
      (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_455).base + 56#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt B.repAlloc decA g ptsElems ∗
          vecU8At B.repAlloc v cap0 ptr0 (bs0 ++ polyDecoderHeaderBytes tag pb) ∗
          B.pool lim curSt sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_455 H) ret s P Q Qp := by
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge_key, hge2⟩ := polyDecoderHeaderBytes_len_bounds tag pb
  refine step_polyDecoder_prologue_placed hres H tag decA v sp hhs0 hpc hrun hsp halign htr
    hw0 hx1 hx2 hcs
    (F := protoPolynomialDecoderPinnedAt B.repAlloc g decA pb ∗
      vecU8At B.repAlloc v cap0 ptr0 bs0 ∗ B.pool lim curSt s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm1b hinv1; rw [pool_step B lim curSt hvm1b]
  have hfit_key : bs0.length +
      (encodeVarint (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64)).length ≤ cap0.toNat := by
    rw [encodeVarint_polyDecoder_tag_eq_proto]; omega
  have hevs_key :
      encodeVarintEvents
        (EncodeVarintGhost.mk (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64)
          v cap0 ptr0 bs0) = [] :=
    encodeVarintEvents_of_spare hfit_key
  refine step_msg48rep_encode_varint_call_placed hres128 B lim hencVarint
    (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64) v cap0 ptr0 sp
    ((blkPl_455).base + 40#64) bs0 curSt (Or.inl hfit_key) (by rw [hevs_key]; trivial)
    (F := protoPolynomialDecoderPinnedAt B.repAlloc g decA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (cs_step hcs1 hinv1) (by sep_ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 _ hpres01
  obtain ⟨hc01, hp01⟩ := hpres01 hfit_key; subst cap01 ptr01
  rw [hevs_key, encodeVarint_polyDecoder_tag_eq_proto]
  simp only [AllocCostModel.stepEvents_nil]
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x0_x20_40_placed H decA v sp hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3 hvm23
  rw [pool_step B lim curSt hvm23]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_493).base); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm3b hinv3; rw [pool_step B lim curSt hvm3b]
  refine step_msg48rep_polyDecLen_call_prog hres128 B.repAlloc hencLen decA sp
    ((blkPl_455).base + 48#64) g pb hlen_lt
    (F := vecU8At B.repAlloc v cap0 ptr0 (bs0 ++ encodeKey tag .lengthDelimited) ∗
      B.pool lim curSt _ ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
  intro s4 ptsElems hpts_eq hpts_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4 hvm34
  rw [pool_step B lim curSt hvm34]
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x1_x19_48_placed H decA v
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5 hvm45
  rw [pool_step B lim curSt hvm45]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm5b hinv5; rw [pool_step B lim curSt hvm5b]
  have hfit_len : (bs0 ++ encodeKey tag .lengthDelimited).length +
      (encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).length ≤ cap0.toNat := by
    rw [List.length_append]; omega
  have hevs_len :
      encodeVarintEvents
        (EncodeVarintGhost.mk (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))
          v cap0 ptr0 (bs0 ++ encodeKey tag .lengthDelimited)) = [] :=
    encodeVarintEvents_of_spare hfit_len
  refine step_msg48rep_encode_varint_call_placed hres128 B lim hencVarint
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) v cap0 ptr0 sp ((blkPl_455).base + 56#64)
    (bs0 ++ encodeKey tag .lengthDelimited) curSt (Or.inl hfit_len) (by rw [hevs_len]; trivial)
    (F := polyDecoderElemsAt decA g pb ptsElems ∗
      polyDecoderRestAt B.repAlloc decA g ptsElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (cs_step hcs5 hinv5) (by sep_ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 _ hpres1
  obtain ⟨rfl, rfl⟩ := hpres1 hfit_len
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = decA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [hevs_len, bs0_append_polyDecoderHeaderBytes bs0 tag pb]
  dsimp only [AllocCostModel.stepEvents]
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext s6 sv3 ptsElems hpts_eq hpts_lt hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6)

theorem step_pd1_ptsNeeded_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (decA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit_pn : curBs.length + (encodeUint32Field 1#32 pb.ptsNeeded).length ≤ curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 56#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 108#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At B.repAlloc v curCap curPtr (curBs ++ encodeUint32Field 1#32 pb.ptsNeeded) ∗
          B.pool lim curSt sm ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_455 H) ret s P Q Qp := by
  refine step_polyDecoder_check_ptsNeeded_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  cases hpn : (pb.ptsNeeded == 0#32)
  · simp only [hpn, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pn, hge2_pn⟩ := ptsNeeded_field_len_of_ne_zero pb hpn
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
      cap_beq_len_false_of_lt_placed hlt0
    rw [vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 80#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm12 hinv1
    rw [← vecHeader, ← vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs,
      pool_step B lim curSt hvm12]
    refine step_polyDecoder_push_ptsNeeded_tag_placed B.repAlloc H decA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (cs_step hcs1 hinv1)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ B.pool lim curSt _ ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvm23
    rw [pool_step B lim curSt hvm23]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm3b hinv3; rw [pool_step B lim curSt hvm3b]
    have hfit_v : (curBs ++ [0x08#8]).length +
        (encodeVarint (pb.ptsNeeded.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hevs_v :
        encodeVarintEvents
          (EncodeVarintGhost.mk (pb.ptsNeeded.zeroExtend 64) v curCap curPtr
            (curBs ++ [0x08#8])) = [] :=
      encodeVarintEvents_of_spare hfit_v
    refine step_msg48rep_encode_varint_call_placed hres B lim hencVarint
      (pb.ptsNeeded.zeroExtend 64) v curCap curPtr sp ((blkPl_455).base + 108#64)
      (curBs ++ [0x08#8]) curSt (Or.inl hfit_v) (by rw [hevs_v]; trivial)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [hevs_v, bs_append_ptsNeeded_of_ne_zero curBs pb hpn]
    dsimp only [AllocCostModel.stepEvents]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hpn, ↓reduceIte] at hpc1
    rw [← bs_append_ptsNeeded_of_zero curBs pb hpn]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

theorem step_pd1_polys_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (decA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit_pl : curBs.length + (encodeUint32Field 2#32 pb.polys).length ≤ curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 160#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At B.repAlloc v curCap curPtr (curBs ++ encodeUint32Field 2#32 pb.polys) ∗
          B.pool lim curSt sm ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_455 H) ret s P Q Qp := by
  refine step_polyDecoder_check_polys_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  cases hpl : (pb.polys == 0#32)
  · simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pl, hge2_pl⟩ := polys_field_len_of_ne_zero pb hpl
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
      cap_beq_len_false_of_lt_placed hlt0
    rw [vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 132#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm12 hinv1
    rw [← vecHeader, ← vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs,
      pool_step B lim curSt hvm12]
    refine step_polyDecoder_push_polys_tag_placed B.repAlloc H decA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (cs_step hcs1 hinv1)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ B.pool lim curSt _ ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvm23
    rw [pool_step B lim curSt hvm23]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm3b hinv3; rw [pool_step B lim curSt hvm3b]
    have hfit_v : (curBs ++ [0x10#8]).length +
        (encodeVarint (pb.polys.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hevs_v :
        encodeVarintEvents
          (EncodeVarintGhost.mk (pb.polys.zeroExtend 64) v curCap curPtr
            (curBs ++ [0x10#8])) = [] :=
      encodeVarintEvents_of_spare hfit_v
    refine step_msg48rep_encode_varint_call_placed hres B lim hencVarint
      (pb.polys.zeroExtend 64) v curCap curPtr sp ((blkPl_455).base + 160#64)
      (curBs ++ [0x10#8]) curSt (Or.inl hfit_v) (by rw [hevs_v]; trivial)
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [hevs_v, bs_append_polys_of_ne_zero curBs pb hpl]
    dsimp only [AllocCostModel.stepEvents]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hpl, ↓reduceIte] at hpc1
    rw [← bs_append_polys_of_zero curBs pb hpl]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

theorem step_pd1_pts_isComplete_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencRep : subroutine_ok (lsProg_455 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack B lim)))
    (decA v curCap curPtr sp sv3 : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts_lt : pb.pts.length < 2 ^ 59)
    (hfit_rest : curBs.length + (encodeRepeatedBytes 3 pb.pts).length +
      (encodeBoolField 4#32 pb.isComplete).length ≤ curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_455).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        vecU8At B.repAlloc v curCap curPtr
          ((curBs ++ encodeRepeatedBytes 3 pb.pts) ++ encodeBoolField 4#32 pb.isComplete) ∗
        B.pool lim curSt sf ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_455 H) (s0.readReg64 .lr) s P Q Qp := by
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  have hfit_pts : curBs.length + (encodeRepeatedBytes 3 pb.pts).length ≤ curCap.toNat := by omega
  refine step_polyDecoder_prep_pts_placed H decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm1b hinv1; rw [pool_step B lim curSt hvm1b]
  refine step_msg48_encode_repeated59_exact_call_placed B lim hencRep 3 g.pts.ptr v curCap curPtr sp
    ((blkPl_455).base + 176#64) ptsElems curBs curSt (by decide) (by decide) (by omega)
    (by rw [hpts_eq]; exact hfit_pts)
    (F := ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((decA + 28#64) ↦₃₂ pb.polys) ∗
      ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (cs_step hcs1 hinv1)
    (by dsimp only [polyDecoderElemsAt]; sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2
  rw [hpts_eq]
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  let bs_pts := curBs ++ encodeRepeatedBytes 3 pb.pts
  refine step_polyDecoder_check_isComplete_placed hres H decA v sp sv3 g pb ptsElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At B.repAlloc v curCap curPtr bs_pts ∗ B.pool lim curSt s2 ∗ F)
    (by dsimp only [polyDecoderElemsAt, bs_pts]; sep_ac_rfl) ?_ ?_
  · intro hc sf hpcf hrunf hspf htrf hccf hcsf hvm2f
    have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
    rw [hc, bs_append_boolField_4_false bs_pts, B.pool_of_vmPreserved hvm2f] at hq
    have hEq :
        ((polyDecoderElemsAt decA g pb ptsElems ∗ vecU8At B.repAlloc v curCap curPtr bs_pts ∗
          B.pool lim curSt s2 ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (vecU8At B.repAlloc v curCap curPtr bs_pts ∗ B.pool lim curSt s2 ∗ F)) := by sep_ac_rfl
    rwa [← hEq]
  · intro hc s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hvm23
    rw [pool_step B lim curSt hvm23]
    have hlen_ic : (encodeBoolField 4#32 pb.isComplete).length = 2 := by
      rw [hc, protoEncodeBoolField_4_true]; rfl
    have hbs_pts_len : bs_pts.length = curBs.length + (encodeRepeatedBytes 3 pb.pts).length :=
      List.length_append
    have hlt3 : bs_pts.length < curCap.toNat := by omega
    refine step_reserve_188_1_exact_placed B.repAlloc H decA v curCap curPtr sp bs_pts hlt3
      hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        B.pool lim curSt s3 ∗ F)
      (by sep_ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4 hvm34
    rw [pool_step B lim curSt hvm34]
    refine step_polyDecoder_push_isComplete_tag_placed B.repAlloc H decA v curCap curPtr sp bs_pts hlt3
      hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        B.pool lim curSt s4 ∗ F)
      (by sep_ac_rfl) ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5 hvm45
    rw [pool_step B lim curSt hvm45]
    have hlt4 : (bs_pts ++ [0x20#8]).length < curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_reserve_228_1_exact_placed B.repAlloc H decA v curCap curPtr sp (bs_pts ++ [0x20#8]) hlt4
      hpc5 hrun5 hsp5 htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5
      (F := polyDecoderElemsAt decA g pb ptsElems ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
        B.pool lim curSt s5 ∗ F)
      (by sep_ac_rfl) ?_
    intro s6 hpc6 hrun6 hsp6 htr6 hx9_6 hx10_6 hx19_6 _ hcs6 hvm56
    rw [pool_step B lim curSt hvm56]
    refine step_polyDecoder_push_isComplete_val_epilogue_placed hres B.repAlloc H v curCap curPtr sp sv3
      (bs_pts ++ [0x20#8]) hlt4 hpc6 hrun6 hsp6 halign htr6 hx9_6 hx10_6 hx19_6 hcs6
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ B.pool lim curSt s6 ∗ F)
      (by sep_ac_rfl) ?_
    intro sf hpcf hrunf hspf htrf hccf hcsf hvm6f
    have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
    rw [hc, ← bs_append_boolField_4_true bs_pts, B.pool_of_vmPreserved hvm6f] at hq
    have hEq :
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At B.repAlloc v curCap curPtr ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          B.pool lim curSt s6 ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((vecU8At B.repAlloc v curCap curPtr ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (polyDecoderElemsAt decA g pb ptsElems ∗ B.pool lim curSt s6 ∗ F)) := by sep_ac_rfl
    rwa [← hEq]

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudgetAux
