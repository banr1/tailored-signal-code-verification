/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux

/-!
# Code-Loaded Placed Budget Verification of `PolynomialDecoder::merge` (Block `296`)

Exports the `withLsCodeRoLoaded` and `withLsCodeLoaded` `[LibsignalPlacement]` per-tag step, loop,
and top-level budget contracts (`polyDecoderMerge_cro_placed_ok_of_contracts`,
`polyDecoderMerge_cl_placed_ok_of_contracts`) on Block `296`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (arrayAt vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Poly
  (boolByte protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
   protoPolynomialDecoderPadSize protoPolynomialDecoderPolysOff
   protoPolynomialDecoderPtsNeededOff)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyDecoderMergeGhost WppPost blkPC_296 blkPl_296 codecWireTypeToProto
   mergeLoopBin polyBelowStack polySavedRegsAny)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergeEnv PolyMergeLoopEnv WppBudgetPanic bytesMerge3RawBudgetSpec
   polyDecoderCapBound polyDecoderLoopPre polyDecoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux
  (polyDecoder_tag1_step_cro polyDecoder_tag2_step_cro polyDecoder_tag3_copy_step_cro
   polyDecoder_tag3_step_cro polyDecoder_tag4_step_cro)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Per-Tag Code-RO-Loaded `[LibsignalPlacement]` Step Lemmas -/

/-- Code-loaded placed budget step lemma for tag 1 (`pts_needed : u32` at `msgPtr + 24#64`) at
`+0x158` (`(blkPl_296).base + 344#64`). -/
theorem polyDecoder_tag1_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    rest.length < 2 ^ 63 → IsDropSuffix x.bs rest →
    2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)) →
    (iwt ≠ .varint →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (iwt = .varint → decodeVarint rest = none →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with ptsNeeded := v.truncate 32 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 344#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag1_step_cro hFromCall hPushCall hVarintCall

/-- Code-loaded placed budget step lemma for tag 2 (`polys : u32` at `msgPtr + 28#64`) at `+0x0f0`
(`(blkPl_296).base + 240#64`). -/
theorem polyDecoder_tag2_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    rest.length < 2 ^ 63 → IsDropSuffix x.bs rest →
    2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)) →
    (iwt ≠ .varint →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (iwt = .varint → decodeVarint rest = none →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with polys := v.truncate 32 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 240#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag2_step_cro hFromCall hPushCall hVarintCall

/-- Code-loaded placed budget step lemma for tag 4 (`is_complete : bool` at `msgPtr + 32#64`) at
`+0x120` (`(blkPl_296).base + 288#64`). -/
theorem polyDecoder_tag4_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    rest.length < 2 ^ 63 → IsDropSuffix x.bs rest →
    2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)) →
    (iwt ≠ .varint →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (iwt = .varint → decodeVarint rest = none →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with isComplete := v != 0#64 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 288#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag4_step_cro hFromCall hPushCall hVarintCall

/-- Code-loaded placed shared element-copy join block at `+0x1b0` (`(blkPl_296).base + 432#64`)
for tag 3 (`pts : Vec<Vec<u8>>`). -/
theorem polyDecoder_tag3_copy_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PolyDecoderMergeGhost} {st0 st_next : M.σ} {R : SepProp}
    {s0 : State} {m : PolynomialDecoder} {s : State}
    {v rest' : List (BitVec 8)} {limit : Nat} {v_stk0 cap' ptr' cap_e ptr_e : BitVec 64} :
    (s0.sp &&& 15#64 == 0#64) = true →
    m.pts.length < cap'.toNat → cap'.toNat * 24 < 2 ^ 63 → ptr' ≠ 0 →
    (∀ (s' : State),
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 432#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.pts.length →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A.repAlloc (s0.sp - 152#64) cap_e ptr_e v ∗
        (x.msgPtr ↦₆₄ cap') ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr' m.pts ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.pts.length * 24)) ((cap'.toNat - m.pts.length) * 24) ∗
        ((x.msgPtr + protoPolynomialDecoderPtsNeededOff) ↦₃₂ m.ptsNeeded) ∗
        ((x.msgPtr + protoPolynomialDecoderPolysOff) ↦₃₂ m.polys) ∗
        ((x.msgPtr + protoPolynomialDecoderIsCompleteOff) ↦₈ boolByte m.isComplete) ∗
        memRegion (x.msgPtr + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool lim st_next s)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag3_copy_step_cro

/-- Code-loaded placed budget step lemma for tag 3 (`pts : Vec<Vec<u8>>` at `msgPtr`) at `+0x178`
(`(blkPl_296).base + 376#64`). -/
theorem polyDecoder_tag3_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    m.pts.length + rest.length < 2 ^ 56 → IsDropSuffix x.bs rest →
    m.pts.length < polyDecoderCapBound x →
    2 * rest.length + 2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)) →
    (mergeBytes iwt rest = none →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (st_next : M.σ)
        (evs_step : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyDecoderCapBound x) evs_step →
      st_next = M.stepEvents evs_step st_cur →
      s'.pc = (blkPl_296).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 376#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag3_step_cro hFromCall hPushCall hBytesCall hGrowCall

/-! ## 2. Code-Loaded Loop & Top-Level Contract Lemmas -/

/-- Code-loaded placed budget loop exit lemma at `+0x0a4` (`(blkPl_296).base + 164#64`) when
`cur.length ≤ limit`. -/
theorem polyDecoder_loop_le_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat}
    {evs_acc : List AllocEvent} :
    cur.length ≤ limit → (s0.sp &&& 15#64 == 0#64) = true →
    cur.length ≤ x.bs.length → IsDropSuffix x.bs cur → limit < 2 ^ 63 →
    PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
      (polyDecoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur
      (PolyMergeLoopEnv (2 * cur.length + 2) x.bs.length (polyDecoderCapBound x)) →
    (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
    s.pc = (blkPl_296).base + 164#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 →
    s.trace = s0.trace → s.readReg64 (Reg.gpr 21#5) = x.slot →
    s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  PolyDecoderBudget.polyDecoder_loop_le_exit_cro hFromCall

/-- Code-loaded placed budget loop key-decoding step at `+0x0a4` (`(blkPl_296).base + 164#64`)
when `¬ cur.length ≤ limit`. -/
theorem polyDecoder_decode_key_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat}
    {evs_acc : List AllocEvent} :
    ¬ cur.length ≤ limit → (s0.sp &&& 15#64 == 0#64) = true →
    cur.length ≤ x.bs.length → cur.length < 2 ^ 63 → IsDropSuffix x.bs cur →
    PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
      (polyDecoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur
      (PolyMergeLoopEnv (2 * cur.length + 2) x.bs.length (polyDecoderCapBound x)) →
    (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
    (∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_296).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 164#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  PolyDecoderBudget.polyDecoder_decode_key_step_cro hFromCall hVarintCall

/-- Code-loaded placed budget main loop induction for `PolynomialDecoder::merge` at `+0x0a4`
(`(blkPl_296).base + 164#64`). -/
theorem polyDecoder_loop_ok_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat} :
    FitsEnv M lim st0 (PolyDecoderMergeEnv x) →
    (s0.sp &&& 15#64 == 0#64) = true → limit < 2 ^ 63 →
    ∀ (n : Nat) (m : PolynomialDecoder) (cur : List (BitVec 8)) (st_cur : M.σ)
        (evs_acc : List AllocEvent) (s : State),
      cur.length ≤ n →
      cur.length ≤ x.bs.length →
      m.pts.length + cur.length < 2 ^ 56 →
      m.pts.length + cur.length ≤ polyDecoderCapBound x →
      IsDropSuffix x.bs cur →
      PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
        (polyDecoderCapBound x) evs_acc →
      st_cur = M.stepEvents evs_acc st0 →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_296).base + 164#64 →
      s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
        (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  PolyDecoderBudget.polyDecoder_loop_ok_cro
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- `withLsCodeRoLoaded`-callee contract-parameterized `[LibsignalPlacement]` budget verification of
`prost::encoding::message::merge::<PolynomialDecoder, &mut &[u8]>` (Block `296`). -/
theorem polyDecoderMerge_cro_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)) :=
  PolyDecoderBudget.polyDecoderMerge_cro_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- Code-loaded (`withLsCodeLoaded` on `261/257/291/263` + `withLsCodeRoLoaded` on `290` +
`growOneVecU8BudgetSpec`) contract-parameterized `[LibsignalPlacement]` budget verification of
`PolynomialDecoder::merge` (Block `296`). -/
theorem polyDecoderMerge_cl_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)) :=
  PolyDecoderBudget.polyDecoderMerge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget
