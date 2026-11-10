/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Shared Step Lemmas for `PolynomialEncoder::encode` (`Blocks 153 & 316`)

Provides budget-threaded `encodeRepeatedStackOf`-frame call steppers, pinned-to-unpinned bridges,
and `VmPreserved`-threaded basic-block steppers for `PolynomialEncoder::encode` (`lsProg_153`, `lsProg_316`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl withLsCodeLoaded
   lsProg_153 blkPl_153 blkPC_153 lsProg_316 blkPl_316 blkPC_316)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost sp_sub_48_aligned)
open CryptoVerification.SpqrV1.Poly (ProtoPolynomialEncoderGhost protoPolynomialEncoderPinnedAt)
open CryptoVerification.SpqrV1.Auth (vecU8At_close_one vecU8At_open_one)
open CryptoVerification.SpqrV1.Varint (encodeRepeatedStackOf)
open CryptoVerification.SpqrV1.ProtoRepr (PinnedEncLenGhost)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen (zeroExtend64_beq_zero32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodePolyEncoderGhost MsgEnc48CalleeSavedPlaced msgEnc48RepeatedStackOf msgEnc48SavedFrame
   polyEncodedLenStack polyEncoderElemsAt polyEncoderRestAt polynomialEncoderPBEncodedLen
   protoPolynomialEncoderAt_eq_exists_pinned
   stackAt_encodeRepeated_eq_varint stackAt_msgEnc48_repeated stackAt_varint_eq_stack16
   withMsgEnc48CSPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserve2SpecOf doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget (encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (pushBytesStep sepWP_done_tpidr_placed sepWPp_call_cs_placed_noPanic
   sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
  (step_msg48_do_reserve2_call_placed step_msg48_do_reserve7_call_placed
   step_msg48_encode_varint_call_placed step_msg48_encode_varint_det_call_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
  (encodePolyEncoderPinnedSpecOf encodePolyEncoderPinnedSpecOfEnv
   encodePolyEncoderSpecOf encodePolyEncoderSpecOfEnv
   polyEncoder_post_unpinned_of_pinned_env
   polynomialEncoderEncodedLenElemsOutSpec)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.zeroExtend64_beq_zero32
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.ofNat_countLeadingZeros_64
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.zext64_truncate32
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.ule_zero_64
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.ult_zero_64
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.ule_self_64
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.ult_self_64

theorem step_msg48rep_encode_varint_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  refine step_msg48_encode_varint_call_placed A lim henc val v curCap curPtr sp ret_pc curBs curSt
    hlen_lt hfits
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; sep_ac_rfl) ?_
  intro sm nextCap nextPtr hpcm hrunm hspm htrm hcsm hcs_m hge hpres
  refine SepWPp.weaken_pre ?_
    (hnext sm nextCap nextPtr hpcm hrunm hspm htrm hcsm hcs_m hge hpres)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48rep_encode_varint_det_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  refine step_msg48_encode_varint_det_call_placed A lim henc val v curCap curPtr sp ret_pc curBs curSt
    hlen_lt hfits
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; sep_ac_rfl) ?_
  intro sm nextCap nextPtr hpcm hrunm hspm htrm hcsm hcs_m hge hpres hcap_eq
  refine SepWPp.weaken_pre ?_
    (hnext sm nextCap nextPtr hpcm hrunm hspm htrm hcsm hcs_m hge hpres hcap_eq)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48rep_do_reserve2_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat) (curSt : M.σ)
    (hres_bound : reserveCap curCap.toNat curBs.length add + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) newPtr curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)) curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  refine step_msg48_do_reserve2_call_placed (by omega) A lim hdoReserve v curCap curPtr sp ret_pc curBs add
    curSt hres_bound hfits
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; sep_ac_rfl) ?_
  intro sm newPtr hpcm hrunm hspm htrm hcsm hcs_m
  refine SepWPp.weaken_pre ?_ (hnext sm newPtr hpcm hrunm hspm htrm hcsm hcs_m)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_msg48rep_do_reserve7_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A lim)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat) (curSt : M.σ)
    (hres_bound : reserveCap curCap.toNat curBs.length add + 1 ≤ 2 ^ 63)
    (hfits : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) newPtr curBs ∗
          A.pool lim (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs add)) curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  refine step_msg48_do_reserve7_call_placed (by omega) A lim hdoReserve v curCap curPtr sp ret_pc curBs add
    curSt hres_bound hfits
    (F := memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗ F)
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hcs
    (by rw [hP, stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]; sep_ac_rfl) ?_
  intro sm newPtr hpcm hrunm hspm htrm hcsm hcs_m
  refine SepWPp.weaken_pre ?_ (hnext sm newPtr hpcm hrunm hspm htrm hcsm hcs_m)
  rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64)]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Execute `bl PolynomialEncoder::encoded_len` (via `polynomialEncoderEncodedLenElemsOutSpec`)
at `call_pc` when the stack at `sp - 48#64` is `stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)`,
exposing `VmPreserved s sm` and transporting `A.pool lim curSt`. -/
theorem step_msg48rep_polyEncLen_call_placed {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {call_pc : BitVec 64} {s0 s : State}
    (hencLen : subroutine_ok prog call_pc
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec A.repAlloc)))
    (encA sp ret_pc : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (curSt : M.σ)
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : s.readReg64 .x0 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialEncoderPinnedAt A.repAlloc g encA pb ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb) →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt A.repAlloc encA g ptsElems polysElems ∗
          A.pool lim curSt sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_48_aligned halign
  have hst : stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) =
      memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      (memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗
        stackAt (sp - 48#64) polyEncodedLenStack) := by
    rw [stackAt_encodeRepeated_eq_varint hres (sp - 48#64),
      stackAt_varint_eq_stack16 (by omega) (sp - 48#64)]
  refine sepWPp_call_cs_placed_noPanic (x := PinnedEncLenGhost.mk encA g pb)
    (F := A.pool lim curSt s ∗
      memRegion (sp - 48#64 - BitVec.ofNat 64 (encodeRepeatedStackOf resStack)) 80 ∗
      memRegion (sp - 48#64 - BitVec.ofNat 64 (0x30 + resStack)) (32 + resStack) ∗ F)
    hencLen hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, hst] at hm
    simp only [withMsgEnc48CSPlaced, polynomialEncoderEncodedLenElemsOutSpec,
      LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBaseBudget.polynomialEncoderEncodedLenPinnedSpec,
      LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget.withVmPreserved,
      CryptoVerification.SpqrV1.Prost.MessageEncode.polynomialEncoderEncodedLenPinnedSpec,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hlen_lt⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CSPlaced, polynomialEncoderEncodedLenElemsOutSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptsElems => ?_
    refine SepWPp.exists_elim fun polysElems => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpts_eq, hpts_lt, hpolys_eq, hpolys_lt⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hpool : A.pool lim curSt s = A.pool lim curSt sm := (A.pool_of_vmPreserved hvm).symm
    refine SepWPp.weaken_pre ?_
      (hnext sm ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
        hpcm hrunm hspm htrm' hx0m hcsm
        (hcs.trans (MsgEnc48CalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hvm)
    rw [hst, hpool]
    exact Entails.of_eq (by sep_ac_rfl)

theorem polyEncoder_unpinned_of_pinned_placed_env [LibsignalPlacement] {resStack : Nat}
    {Env : CryptoVerification.SpqrV1.Prost.MessageEncode.EncodePolyEncoderGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpecOfEnv resStack Env A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyEncoderSpecOfEnv resStack Env A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodePolyEncoderSpecOfEnv] at hpre
  rw [protoPolynomialEncoderAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpecOfEnv resStack Env A lim)).pre
      (⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hinv0, hpre⟩
  refine (hpinned.to_outcome (⟨x.encA, g, x.enc, x.v, x.cap, x.ptr, x.bs⟩, st)
    R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded] at hq ⊢
    exact polyEncoder_post_unpinned_of_pinned_env hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem polyEncoder_unpinned_of_pinned_placed_x [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpecOf resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodePolyEncoderSpecOf resStack A lim)) :=
  polyEncoder_unpinned_of_pinned_placed_env hpinned

/-- Relocatable `[LibsignalPlacement]` entry predicate for the two `PolynomialEncoder::encode`
monomorphizations (`blkPC_153` and `blkPC_316`). -/
def IsPolyEncoderEncodeEntryProg (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    prog = @lsProg_153 inst H ∧ entry = (@blkPl_153 inst).base) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    prog = @lsProg_316 inst H ∧ entry = (@blkPl_316 inst).base)

/-- Shared prologue (`+0x000..+0x014`, offsets `0..20`):
allocates the 48-byte stack frame, saves `x29, x30, x21, x20, x19`, sets `x19 = v`,
and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_prologue_placed {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v sp : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hhs0 : s = s0) (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = stackAt sp (msgEnc48RepeatedStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64),
      sm.pc = entry + 20#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = encA → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        ((stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP hhs0
  have hsp_aligned := sp_sub_48_aligned halign
  rw [stackAt_msgEnc48_repeated hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := entry + 20#64)
  rcases hfn with ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩ <;> ·
    let _ := inst
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun hvm hinv =>
          SepWPp.weaken_pre (by dsimp only [msgEnc48SavedFrame]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ sv3
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) hinv)
              hvm)))

/-- Shared header tag push (`+0x028..+0x040`, offsets `40..64`):
given `curBs.length < curCap.toNat`, pushes `0x12#8` (`tag = 2`, `lengthDelimited`) to `buf`,
sets `x0 = encA`, and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_push_hdr_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 40#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 64#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = encA → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := entry + 64#64)
  rcases hfn with ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩ <;> ·
    let _ := inst
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun hvm hinv =>
          SepWPp.weaken_pre
            (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) hinv)
              hvm)))

theorem step_polyEncoder_mov_x1_x19_68_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry) (val encA v sp : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 68#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 72#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = val → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  apply sepWPp_of_sepWP_cs_vm_placed (mid := entry + 72#64)
  rcases hfn with ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩ <;> ·
    let _ := inst
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun hvm hinv =>
          hnext _
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) hinv)
            hvm))

/-- Shared `idx` load and zero check (`+0x04c..+0x054`, offsets `76..84`):
loads `w0 = [x20, #0x30]` (`pb.idx`), branches to `entry + 128#64` if `pb.idx == 0#32`
else falls through to `entry + 84#64`, and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_check_idx_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v sp : BitVec 64) (g : ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 76#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + (if pb.idx == 0#32 then 128#64 else 84#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        (polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP; dsimp only [polyEncoderElemsAt]
  cases hidx : (pb.idx == 0#32)
  · have hidx64 : (BitVec.zeroExtend 64 pb.idx == 0#64) = false := by
      rw [zeroExtend64_beq_zero32, hidx]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := entry + 84#64)
    rcases hfn with ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩ <;> ·
      let _ := inst
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (fun hvm hinv =>
            SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
              (hnext _ (by simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) hinv)
                hvm)))
  · have hidx64 : (BitVec.zeroExtend 64 pb.idx == 0#64) = true := by
      rw [zeroExtend64_beq_zero32, hidx]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := entry + 128#64)
    rcases hfn with ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩ <;> ·
      let _ := inst
      by_vm_steps (
        wp_steps
        exact sepWP_done_tpidr_placed
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (fun hvm hinv =>
            SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
              (hnext _ (by simp only [↓reduceIte, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) hinv)
                hvm)))

/-- Shared `idx` tag push (`+0x064..+0x07c`, offsets `100..124`):
given `curBs.length < curCap.toNat`, pushes `0x08#8` (`tag = 1`, varint) to `buf`,
sets `x1 = v`, preserves `x0 = pb.idx.zeroExtend 64`, and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_push_idx_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (pb : ProtoPolynomialEncoder) (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 100#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.idx.zeroExtend 64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 124#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_vm_placed (mid := entry + 124#64)
  rcases hfn with ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩ <;> ·
    let _ := inst
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun hvm hinv =>
          SepWPp.weaken_pre
            (by rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) hinv)
              hvm)))

/-- Shared `pts` argument setup (`+0x080..+0x08c`, offsets `128..140`):
loads `x1 = g.pts.ptr`, `x2 = BitVec.ofNat 64 pb.pts.length`, sets `w0 = 2#32`, `x3 = v`,
and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_prep_pts_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v sp : BitVec 64) (g : ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 128#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hP : P = polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 140#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg32 .x0 = 2#32 → sm.readReg64 .x1 = g.pts.ptr →
      sm.readReg64 .x2 = BitVec.ofNat 64 pb.pts.length → sm.readReg64 .x3 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → VmPreserved s sm →
      SepWPp prog ret sm
        (polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP; dsimp only [polyEncoderElemsAt]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := entry + 140#64)
  rcases hfn with ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩ <;> ·
    let _ := inst
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun hvm hinv =>
          SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) hinv)
              hvm)))

/-- Shared `polys` argument setup + frame restore (`+0x090..+0x0a8`, offsets `144..168`):
loads `x1 = g.polys.ptr`, `x2 = BitVec.ofNat 64 pb.polys.length`, sets `w0 = 3#32`, `x3 = v`,
restores the 48-byte stack frame (`sp = sp`, `lr = s0.readReg64 .lr`) arriving at
`entry + 168#64` (`+0x0a8`, the `b encode_repeated` tailcall), and establishes `VmPreserved s sm`. -/
theorem step_polyEncoder_prep_polys_epilogue_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsPolyEncoderEncodeEntryProg prog entry)
    (encA v sp sv3 : BitVec 64) (g : ProtoPolynomialEncoderGhost) (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry + 144#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 168#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .lr = s0.readReg64 .lr → sm.readReg32 .x0 = 3#32 →
      sm.readReg64 .x1 = g.polys.ptr → sm.readReg64 .x2 = BitVec.ofNat 64 pb.polys.length →
      sm.readReg64 .x3 = v → CalleeSavedPreserved s0 sm → MsgEnc48CalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp prog ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  subst hP
  have hsp_aligned := sp_sub_48_aligned halign
  rcases hcs with ⟨h22, h23, h24, h25, h26, h27, h28, hvregs, hinv0⟩
  dsimp only [polyEncoderElemsAt, msgEnc48SavedFrame]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := entry + 168#64)
  rcases hfn with ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩ <;> ·
    let _ := inst
    by_vm_steps (
      wp_steps
      exact sepWP_done_tpidr_placed
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (fun hvm hinv1 =>
          SepWPp.weaken_pre
            (by dsimp only [polyEncoderElemsAt, msgEnc48SavedFrame]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (by dsimp only [State.readReg32, Reg.x0]; simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (by epochEncLen_cc_close)
              ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *],
               by simp only [arm64_norm, *], by simp only [arm64_norm, *], hinv0.trans hinv1⟩
              hvm)))

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
