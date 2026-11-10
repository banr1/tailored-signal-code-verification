/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Step Helpers for `encode<PolynomialDecoder> [local#3]` (Block `455`)

Defines budget-threaded placed contract propositions and proves `do_reserve` branch helpers and the
deterministic-capacity header stepper on CLI Block `455` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialDecoder)
open CryptoVerification.LibsignalSpqrV1.Proto (WireType encodeKey)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap tripleRatchetExterns)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialDecoderGhost protoPolynomialDecoderPinnedAt)
open CryptoVerification.SpqrV1.Varint (encodeRepeatedStackOf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (MsgEnc48CalleeSavedPlaced bs0_append_polyDecoderHeaderBytes cap_toNat_eq_of_beq
   encodeVarint_polyDecoder_tag_eq_proto lt_cap_toNat_of_beq_false
   msgEnc48RepeatedStackOf msgEnc48SavedFrame polyDecoderElemsAt
   polyDecoderHeaderBytes polyDecoderHeaderBytes_len_bounds polyDecoderRestAt
   polynomialDecoderPBEncodedLen reserveCap_one_bounds withMsgEnc48CSPlaced)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPl_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed (blkPl_451)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced (blkPl_493)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_455 lsProg_455)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget (sepWPp_extract_vecU8At_bounds)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents pushByteStep)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeVarintDetSpecOf pushBytesStep_add)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (pushBytesStep pushBytesStep_snd_eq reserveStep_of_need_doReserveEvents
   reserveStep_of_spare reserveStep_one_eq_pushByteStep
   sepWP_done_tpidr_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBaseBudget
  (encodePolyDecoderPinnedExactVmSpecOf encodePolyDecoderPinnedSpec
   encodePolyDecoderPinnedSpecX encodePolyDecoderSpec encodePolyDecoderSpecX
   polynomialDecoderEncodedLenElemsOutSpec step_msg48rep_polyDecLen_call_prog)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
  (step_msg48rep_do_reserve2_call_placed step_msg48rep_encode_varint_det_call_placed)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm] private theorem blkPl_451_base_eq [LibsignalPlacement] :
    (blkPl_451).base = lsmpl.base 451 := rfl
@[local arm64_norm] private theorem blkPl_460_base_eq [LibsignalPlacement] :
    (blkPl_460).base = lsmpl.base 460 := rfl
@[local arm64_norm] private theorem blkPl_493_base_eq [LibsignalPlacement] :
    (blkPl_493).base = lsmpl.base 493 := rfl

/-! ## 1. Budget-Threaded Placed Contract Propositions for Block `455` -/

def EncodePolyDecoder1PinnedPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 H) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecX A lim))

def EncodePolyDecoder1PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 H) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderSpecX A lim))

def EncodePolyDecoder1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 (Rust.withPanics ext)) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpec A lim))

def EncodePolyDecoder1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 (Rust.withPanics ext)) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderSpec A lim))

def EncodePolyDecoder1PinnedPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  EncodePolyDecoder1PinnedPlacedOkExt A lim (tripleRatchetExterns C ctl abs)

def EncodePolyDecoder1PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  EncodePolyDecoder1PlacedOkExt A lim (tripleRatchetExterns C ctl abs)

def EncodePolyDecoder1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  EncodePolyDecoder1PinnedPlacedOkExtX A lim (Rust.withPanics (tripleRatchetExterns C ctl abs))

def EncodePolyDecoder1PlacedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  EncodePolyDecoder1PlacedOkExtX A lim (Rust.withPanics (tripleRatchetExterns C ctl abs))

abbrev EncodePolyDecoder1PlacedOkX := @EncodePolyDecoder1PlacedPlacedOkX

def EncodePolyDecoder1PinnedExactPlacedOk [LibsignalPlacement] (resStack : Nat) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_455 H) (blkPl_455).base
    (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedExactVmSpecOf resStack A))

/-! ## 2. Basic-Block Step Lemmas for Block `455` (`PolyDecoderBasePlacedBudgetAux`) -/

abbrev step_polyDecoder_prologue_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_prologue_placed
abbrev step_polyDecoder_mov_x0_x20_40_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_mov_x0_x20_40_placed
abbrev step_polyDecoder_mov_x1_x19_48_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_mov_x1_x19_48_placed
abbrev step_polyDecoder_check_ptsNeeded_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_check_ptsNeeded_placed
abbrev step_polyDecoder_push_ptsNeeded_tag_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_push_ptsNeeded_tag_placed
abbrev step_polyDecoder_check_polys_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_check_polys_placed
abbrev step_polyDecoder_push_polys_tag_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_push_polys_tag_placed
abbrev step_polyDecoder_prep_pts_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_prep_pts_placed
abbrev step_polyDecoder_check_isComplete_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_check_isComplete_placed
abbrev step_polyDecoder_push_isComplete_tag_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_push_isComplete_tag_placed
abbrev step_polyDecoder_push_isComplete_val_epilogue_placed :=
  @PolyDecoderBasePlacedBudgetAux.step_polyDecoder_push_isComplete_val_epilogue_placed

/-! ## 3. `do_reserve` Branch Helpers & Header Stepper for Block `455` -/

theorem step_reserve_64_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (curSt : M.σ)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (pushByteStep curCap.toNat curBs.length).2)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 64#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 80#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_455 H) ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := curCap)
    (ptr := curPtr) (bs := curBs)
    (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hcap_le _ _ => ?_
  rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hstep_eq :
        pushByteStep curCap.toNat curBs.length =
          (reserveCap curCap.toNat curBs.length 1,
           doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      rw [← reserveStep_one_eq_pushByteStep]
      exact reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
    have hfits_dr : FitsEvents M lim curSt
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      simpa only [congrArg Prod.snd hstep_eq] using hfits
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_460).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
      refine step_msg48rep_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
        ((blkPl_455).base + 280#64) curBs 1 curSt hbound1 hfits_dr (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
      have hx21_1 : s1.readReg64 .x21 = pb.ptsNeeded.zeroExtend 64 := by
        rw [hcs01.2.2.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 80#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm1 hinv1
        rw [← A.pool_of_vmPreserved hvm1]
        have hstep_ev : (pushByteStep curCap.toNat curBs.length).2 =
            doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) :=
          congrArg Prod.snd hstep_eq
        rw [← hstep_ev]
        refine SepWPp.weaken_pre
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv1)
            (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega)
            (fun h => absurd h (by omega))
            (by dsimp [newCap1]; rw [htoNat1, congrArg Prod.fst hstep_eq]))))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    have hstep_eq : pushByteStep curCap.toNat curBs.length = (curCap.toNat, []) := by
      rw [← reserveStep_one_eq_pushByteStep]
      exact reserveStep_of_spare hlt0
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 80#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      have hst_eq :
          M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
        rw [congrArg Prod.snd hstep_eq, AllocCostModel.stepEvents_nil]
      refine SepWPp.weaken_pre
        (by
          rw [hst_eq]
          simp only [vecU8At_eq_header_sep_buf, vecHeader]
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) hinv0)
          hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
          (congrArg Prod.fst hstep_eq).symm))

theorem step_reserve_116_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialDecoder) (curSt : M.σ)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (pushByteStep curCap.toNat curBs.length).2)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.polys.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 132#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_455 H) ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := curCap)
    (ptr := curPtr) (bs := curBs)
    (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hcap_le _ _ => ?_
  rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hstep_eq :
        pushByteStep curCap.toNat curBs.length =
          (reserveCap curCap.toNat curBs.length 1,
           doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      rw [← reserveStep_one_eq_pushByteStep]
      exact reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
    have hfits_dr : FitsEvents M lim curSt
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      simpa only [congrArg Prod.snd hstep_eq] using hfits
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_460).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
      refine step_msg48rep_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
        ((blkPl_455).base + 308#64) curBs 1 curSt hbound1 hfits_dr (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
      have hx21_1 : s1.readReg64 .x21 = pb.polys.zeroExtend 64 := by
        rw [hcs01.2.2.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 132#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm1 hinv1
        rw [← A.pool_of_vmPreserved hvm1]
        have hstep_ev : (pushByteStep curCap.toNat curBs.length).2 =
            doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) :=
          congrArg Prod.snd hstep_eq
        rw [← hstep_ev]
        refine SepWPp.weaken_pre
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv1)
            (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega)
            (fun h => absurd h (by omega))
            (by dsimp [newCap1]; rw [htoNat1, congrArg Prod.fst hstep_eq]))))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    have hstep_eq : pushByteStep curCap.toNat curBs.length = (curCap.toNat, []) := by
      rw [← reserveStep_one_eq_pushByteStep]
      exact reserveStep_of_spare hlt0
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 132#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      have hst_eq :
          M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
        rw [congrArg Prod.snd hstep_eq, AllocCostModel.stepEvents_nil]
      refine SepWPp.weaken_pre
        (by
          rw [hst_eq]
          simp only [vecU8At_eq_header_sep_buf, vecHeader]
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) hinv0)
          hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
          (congrArg Prod.fst hstep_eq).symm))

theorem step_reserve_188_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (pushByteStep curCap.toNat curBs.length).2)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 204#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x8 = nextCap →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_455 H) ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := curCap)
    (ptr := curPtr) (bs := curBs)
    (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hcap_le _ _ => ?_
  rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hstep_eq :
        pushByteStep curCap.toNat curBs.length =
          (reserveCap curCap.toNat curBs.length 1,
           doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      rw [← reserveStep_one_eq_pushByteStep]
      exact reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
    have hfits_dr : FitsEvents M lim curSt
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      simpa only [congrArg Prod.snd hstep_eq] using hfits
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_460).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
      refine step_msg48rep_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
        ((blkPl_455).base + 332#64) curBs 1 curSt hbound1 hfits_dr (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 204#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm1 hinv1
        rw [← A.pool_of_vmPreserved hvm1]
        have hstep_ev : (pushByteStep curCap.toNat curBs.length).2 =
            doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) :=
          congrArg Prod.snd hstep_eq
        rw [← hstep_ev]
        refine SepWPp.weaken_pre
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv1)
            (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega)
            (fun h => absurd h (by omega))
            (by dsimp [newCap1]; rw [htoNat1, congrArg Prod.fst hstep_eq]))))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    have hstep_eq : pushByteStep curCap.toNat curBs.length = (curCap.toNat, []) := by
      rw [← reserveStep_one_eq_pushByteStep]
      exact reserveStep_of_spare hlt0
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 204#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      have hst_eq :
          M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
        rw [congrArg Prod.snd hstep_eq, AllocCostModel.stepEvents_nil]
      refine SepWPp.weaken_pre
        (by
          rw [hst_eq]
          simp only [vecU8At_eq_header_sep_buf, vecHeader]
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) hinv0)
          hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
          (congrArg Prod.fst hstep_eq).symm))

theorem step_reserve_228_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_455 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (pushByteStep curCap.toNat curBs.length).2)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 .x8 = curCap) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hz : s.pstate = subsPState64 curCap (BitVec.ofNat 64 curBs.length))
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_455).base + 232#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x9 = nextPtr → sm.readReg64 .x10 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_455 H) ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr curBs ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := curCap)
    (ptr := curPtr) (bs := curBs)
    (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hcap_le _ _ => ?_
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hcap_bv : curCap = BitVec.ofNat 64 curBs.length := eq_of_beq hcap
    have hstep_eq :
        pushByteStep curCap.toNat curBs.length =
          (reserveCap curCap.toNat curBs.length 1,
           doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      rw [← reserveStep_one_eq_pushByteStep]
      exact reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
    have hfits_dr : FitsEvents M lim curSt
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      simpa only [congrArg Prod.snd hstep_eq] using hfits
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_460).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
      refine step_msg48rep_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
        ((blkPl_455).base + 360#64) curBs 1 curSt hbound1 hfits_dr (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        (by sep_ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 232#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm1 hinv1
        rw [← A.pool_of_vmPreserved hvm1]
        have hstep_ev : (pushByteStep curCap.toNat curBs.length).2 =
            doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) :=
          congrArg Prod.snd hstep_eq
        rw [← hstep_ev]
        refine SepWPp.weaken_pre
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv1)
            (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega)
            (fun h => absurd h (by omega))
            (by dsimp [newCap1]; rw [htoNat1, congrArg Prod.fst hstep_eq]))))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    have hstep_eq : pushByteStep curCap.toNat curBs.length = (curCap.toNat, []) := by
      rw [← reserveStep_one_eq_pushByteStep]
      exact reserveStep_of_spare hlt0
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 232#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm0 hinv0
      rw [← A.pool_of_vmPreserved hvm0]
      have hst_eq :
          M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
        rw [congrArg Prod.snd hstep_eq, AllocCostModel.stepEvents_nil]
      refine SepWPp.weaken_pre
        (by rw [hst_eq]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) hinv0)
          hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
          (congrArg Prod.fst hstep_eq).symm))

private theorem cap_beq_len_false_of_lt_pd {curBs : List (BitVec 8)} {curCap : BitVec 64}
    (hlt : curBs.length < curCap.toNat) :
    (curCap == BitVec.ofNat 64 curBs.length) = false := by
  have hcap_lt : curBs.length < 2 ^ 64 := Nat.lt_trans hlt (BitVec.isLt curCap)
  cases h : (curCap == BitVec.ofNat 64 curBs.length)
  · rfl
  · exfalso
    have heq : curCap.toNat = (BitVec.ofNat 64 curBs.length).toNat :=
      congrArg BitVec.toNat (eq_of_beq h)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt] at heq
    omega

theorem step_reserve_188_1_exact_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hlt0 : curBs.length < curCap.toNat)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 204#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x8 = curCap →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_455 H) ret sm (vecU8At A v curCap curPtr curBs ∗ F) Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  subst hP
  have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
    cap_beq_len_false_of_lt_pd hlt0
  rw [vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 204#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp0 hinv0
    refine SepWPp.weaken_pre
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hvmp0))

theorem step_reserve_228_1_exact_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hlt0 : curBs.length < curCap.toNat)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_455).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (_hx8 : s.readReg64 .x8 = curCap) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hz : s.pstate = subsPState64 curCap (BitVec.ofNat 64 curBs.length))
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_455).base + 232#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x9 = curPtr → sm.readReg64 .x10 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp (lsProg_455 H) ret sm (vecU8At A v curCap curPtr curBs ∗ F) Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  subst hP
  have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
    cap_beq_len_false_of_lt_pd hlt0
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_455).base + 232#64)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp0 hinv0
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hvmp0))

theorem step_hdr_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_455 H) (blkPl_493).base
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A.repAlloc)))
    (hencVarint : subroutine_ok (lsProg_455 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (tag : BitVec 32) (decA v cap0 ptr0 sp : BitVec 64) (g : ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (bs0 : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat ∨
      bs0.length + (polyDecoderHeaderBytes tag pb).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (pushBytesStep (polyDecoderHeaderBytes tag pb).length cap0.toNat bs0.length).2)
    {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_455).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialDecoderPinnedAt A.repAlloc g decA pb ∗
      vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ A.pool lim curSt s ∗
      stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64)
      (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_455).base + 56#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      cap0.toNat ≤ cap1.toNat →
      (bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat →
        cap1 = cap0 ∧ ptr1 = ptr0) →
      cap1.toNat =
        (pushBytesStep (polyDecoderHeaderBytes tag pb).length cap0.toNat bs0.length).1 →
      SepWPp (lsProg_455 H) ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt A.repAlloc decA g ptsElems ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ polyDecoderHeaderBytes tag pb) ∗
          A.pool lim
            (M.stepEvents
              (pushBytesStep (polyDecoderHeaderBytes tag pb).length cap0.toNat bs0.length).2
              curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_455 H) ret s P Q Qp oom := by
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge_key, hge2⟩ := polyDecoderHeaderBytes_len_bounds tag pb
  let keyBv := ((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64
  let lenBv := BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)
  have hkey_len : (encodeVarint keyBv).length = (encodeKey tag .lengthDelimited).length := by
    dsimp only [keyBv]
    rw [encodeVarint_polyDecoder_tag_eq_proto]
  have hhdr_step :
      pushBytesStep (polyDecoderHeaderBytes tag pb).length cap0.toNat bs0.length =
        let s1 := pushBytesStep (encodeVarint keyBv).length cap0.toNat bs0.length
        let s2 := pushBytesStep (encodeVarint lenBv).length s1.1
          (bs0.length + (encodeVarint keyBv).length)
        (s2.1, s1.2 ++ s2.2) := by
    have htot : (polyDecoderHeaderBytes tag pb).length =
        (encodeVarint keyBv).length + (encodeVarint lenBv).length := by
      dsimp only [lenBv]
      rw [hkey_len]
      exact hlen_eq
    rw [htot]
    exact pushBytesStep_add (encodeVarint keyBv).length (encodeVarint lenBv).length
      cap0.toNat bs0.length
  let step1 := pushBytesStep (encodeVarint keyBv).length cap0.toNat bs0.length
  let step2 := pushBytesStep (encodeVarint lenBv).length step1.1
    (bs0.length + (encodeVarint keyBv).length)
  have hfits_pair : FitsEvents M lim curSt step1.2 ∧
      FitsEvents M lim (M.stepEvents step1.2 curSt) step2.2 := by
    rw [← fitsEvents_append]
    simpa only [congrArg Prod.snd hhdr_step] using hfits
  rcases hfits_pair with ⟨hfits1, hfits2⟩
  have hfits1_ev :
      FitsEvents M lim curSt
        (encodeVarintEvents (EncodeVarintGhost.mk keyBv v cap0 ptr0 bs0)) := by
    rw [encodeVarintEvents, ← pushBytesStep_snd_eq]
    exact hfits1
  refine step_polyDecoder_prologue_placed hres H tag decA v sp hhs0 hpc hrun hsp halign htr
    hw0 hx1 hx2 hcs
    (F := protoPolynomialDecoderPinnedAt A.repAlloc g decA pb ∗
      vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ A.pool lim curSt s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hcs1 hvm_pro
  rw [← A.pool_of_vmPreserved hvm_pro]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm1 hinv1
    rw [← A.pool_of_vmPreserved hvm1]
    have hfit_key : bs0.length + (encodeVarint keyBv).length ≤ cap0.toNat ∨
        bs0.length + 10 < 2 ^ 62 := by
      rw [hkey_len]
      rcases hfit_hdr with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    refine step_msg48rep_encode_varint_det_call_placed hres128 A lim hencVarint
      keyBv v cap0 ptr0 sp ((blkPl_455).base + 40#64) bs0 curSt hfit_key hfits1_ev
      (F := protoPolynomialDecoderPinnedAt A.repAlloc g decA pb ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [keyBv, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      (by sep_ac_rfl) ?_
    intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge01 hpres01 hcap01_det
    have hstep1_ev :
        encodeVarintEvents (EncodeVarintGhost.mk keyBv v cap0 ptr0 bs0) = step1.2 := by
      rw [encodeVarintEvents, ← pushBytesStep_snd_eq]
    rw [hstep1_ev]
    have hcap01_step : cap01.toNat = step1.1 := hcap01_det
    have hkey_bytes : encodeVarint keyBv = encodeKey tag .lengthDelimited := by
      dsimp only [keyBv]
      exact encodeVarint_polyDecoder_tag_eq_proto tag
    rw [hkey_bytes] at hpres01 ⊢
    have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
    refine step_polyDecoder_mov_x0_x20_40_placed H decA v sp hpc2 hrun2 hsp2 htr2
      hx19_2 hx20_2 hcs2 ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3 hvm23
    rw [← A.pool_of_vmPreserved hvm23]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_493).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm3 hinv3
      rw [← A.pool_of_vmPreserved hvm3]
      refine step_msg48rep_polyDecLen_call_prog hres128 A.repAlloc hencLen decA sp
        ((blkPl_455).base + 48#64) g pb hlen_lt
        (F := vecU8At A.repAlloc v cap01 ptr01 (bs0 ++ encodeKey tag .lengthDelimited) ∗
          A.pool lim (M.stepEvents step1.2 curSt) _ ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv3)
        (by sep_ac_rfl) ?_
      intro s4 ptsElems hpts_eq hpts_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4 hvm_len
      rw [← A.pool_of_vmPreserved hvm_len]
      have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
      have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
      refine step_polyDecoder_mov_x1_x19_48_placed H decA v lenBv sp
        hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
      intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5 hvm45
      rw [← A.pool_of_vmPreserved hvm45]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvm5 hinv5
        rw [← A.pool_of_vmPreserved hvm5]
        have hfit_len : (bs0 ++ encodeKey tag .lengthDelimited).length +
            (encodeVarint lenBv).length ≤ cap01.toNat ∨
            (bs0 ++ encodeKey tag .lengthDelimited).length + 10 < 2 ^ 62 := by
          dsimp only [lenBv]
          rw [List.length_append]
          rcases hfit_hdr with h | h
          · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
          · right; omega
        have hfits2_ev :
            FitsEvents M lim (M.stepEvents step1.2 curSt)
              (encodeVarintEvents
                (EncodeVarintGhost.mk lenBv v cap01 ptr01
                  (bs0 ++ encodeKey tag .lengthDelimited))) := by
          rw [encodeVarintEvents, ← pushBytesStep_snd_eq]
          simp only [List.length_append, ← hkey_len, hcap01_step]
          exact hfits2
        refine step_msg48rep_encode_varint_det_call_placed hres128 A lim hencVarint
          lenBv v cap01 ptr01 sp ((blkPl_455).base + 56#64)
          (bs0 ++ encodeKey tag .lengthDelimited) (M.stepEvents step1.2 curSt)
          hfit_len hfits2_ev
          (F := polyDecoderElemsAt decA g pb ptsElems ∗
            polyDecoderRestAt A.repAlloc decA g ptsElems ∗
            msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [lenBv, arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs5.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) hinv5)
          (by sep_ac_rfl) ?_
        intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 hge1 hpres1 hcap1_det
        have hstep2_ev :
            encodeVarintEvents
              (EncodeVarintGhost.mk lenBv v cap01 ptr01
                (bs0 ++ encodeKey tag .lengthDelimited)) = step2.2 := by
          rw [encodeVarintEvents, ← pushBytesStep_snd_eq]
          simp only [List.length_append, ← hkey_len, hcap01_step, step2]
        have hst_final :
            M.stepEvents step2.2 (M.stepEvents step1.2 curSt) =
              M.stepEvents
                (pushBytesStep (polyDecoderHeaderBytes tag pb).length cap0.toNat bs0.length).2
                curSt := by
          rw [congrArg Prod.snd hhdr_step, AllocCostModel.stepEvents_append]
        have hcap1_final :
            cap1.toNat =
              (pushBytesStep (polyDecoderHeaderBytes tag pb).length cap0.toNat bs0.length).1 := by
          rw [congrArg Prod.fst hhdr_step]
          simpa only [List.length_append, ← hkey_len, hcap01_step, step2] using hcap1_det
        rw [hstep2_ev, hst_final]
        have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
        have hx20_6 : s6.readReg64 .x20 = decA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
        dsimp only [lenBv]
        rw [bs0_append_polyDecoderHeaderBytes bs0 tag pb]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext s6 sv3 cap1 ptr1 ptsElems hpts_eq hpts_lt
            hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6 (Nat.le_trans hge01 hge1) ?_ hcap1_final)
        intro hle
        obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
        exact hpres1 (by dsimp only [lenBv]; rw [List.length_append]; omega))))

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlacedBudget
