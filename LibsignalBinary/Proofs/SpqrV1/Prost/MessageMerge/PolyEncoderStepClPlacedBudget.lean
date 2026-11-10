/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetSteps

/-!
# Code-Loaded Placed Exit & Tag-Step Budget Lemmas for `PolynomialEncoder::merge` (Block `297`)

Exports the `withLsCodeRoLoaded` `[LibsignalPlacement]` shared-exit, unknown-tag skip, and per-tag
(`tag1`–`tag3`) budget step lemmas for `PolynomialEncoder::merge` on Block `297`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderStepClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (arrayAt vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint mergeBytes skipField)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix sliceCursorAfter)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialEncoderIdxOff protoPolynomialEncoderPadOff
   protoPolynomialEncoderPadSize protoPolynomialEncoderPolysOff vecVecU8At)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyEncoderMergeGhost WppPost blkPC_297 blkPl_297 codecWireTypeToProto
   polyBelowStack polySavedRegsAny)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyMergeLoopEnv WppBudgetPanic bytesMerge3RawBudgetSpec
   polyEncoderCapBound polyEncoderErrFrame polyEncoderLoopPre polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetAux
  (polyEncoder_tag1_step_cro)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetSteps
  (polyEncoder_tag2_copy_step_cro polyEncoder_tag2_step_cro
   polyEncoder_tag3_copy_step_cro polyEncoder_tag3_step_cro)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Shared Exit & Unknown-Tag Step Lemmas (`withLsCodeRoLoaded`) -/

/-- Code-loaded placed shared exit from `+0x070` (`(blkPl_297).base + 112#64`) with
`withLsCodeRoLoaded` on `DecodeError::from` (`261`). -/
theorem polyEncoder_from_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {w : BitVec 64}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none →
    KindNoHeap w →
    1 ≤ f_rem →
    f_acc + 1 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)) →
    (s0.sp &&& 15#64 == 0#64) = true →
    s.pc = (blkPl_297).base + 112#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 →
    s.trace = s0.trace → PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyEncoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  PolyEncoderBudgetAux.polyEncoder_from_err_exit_cl_placed hFromCall

/-- Code-loaded placed shared exit from `+0x344` (`(blkPl_297).base + 836#64`) with
`withLsCodeRoLoaded` on `DecodeError::push` (`257`). -/
theorem polyEncoder_push_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {err : BitVec 64}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none →
    err ≠ 0#64 →
    1 ≤ f_rem →
    f_acc + 1 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)) →
    (s0.sp &&& 15#64 == 0#64) = true →
    s.pc = (blkPl_297).base + 836#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 →
    s.trace = s0.trace → s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗
        polyEncoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  PolyEncoderBudgetAux.polyEncoder_push_err_exit_cl_placed hPushCall

/-- Code-loaded placed step lemma for unknown field tags (`tag ∉ {1, 2, 3}`) at `+0x1d0`
(`(blkPl_297).base + 464#64`) with `withLsCodeRoLoaded` on `263`. -/
theorem polyEncoder_skip_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    rest.length < 2 ^ 63 → IsDropSuffix x.bs rest → tag < 2 ^ 32 →
    1 ≤ f_rem →
    f_acc + 1 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)) →
    (skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_297).base + 464#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
    (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  PolyEncoderBudgetAux.polyEncoder_skip_step_cl_placed hSkipCall

/-! ## 2. Per-Tag Code-RO-Loaded `[LibsignalPlacement]` Step Lemmas -/

/-- Code-loaded placed budget step lemma for tag 1 (`idx : u32` at `msgPtr + 48#64`) at
`+0x1b0` (`(blkPl_297).base + 432#64`). -/
theorem polyEncoder_tag1_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    rest.length < 2 ^ 63 → IsDropSuffix x.bs rest →
    2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)) →
    (iwt ≠ .varint →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (iwt = .varint → decodeVarint rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with idx := v.truncate 32 } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_297).base + 432#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  polyEncoder_tag1_step_cro hFromCall hPushCall hVarintCall

/-- Code-loaded placed shared element-copy join block at `+0x188` (`(blkPl_297).base + 392#64`)
for tag 2 (`pts : Vec<Vec<u8>>`). -/
theorem polyEncoder_tag2_copy_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PolyEncoderMergeGhost} {st0 st_next : M.σ} {R : SepProp}
    {s0 : State} {m : PolynomialEncoder} {s : State}
    {v rest' : List (BitVec 8)} {limit : Nat} {v_stk0 cap' ptr' cap_e ptr_e : BitVec 64} :
    (s0.sp &&& 15#64 == 0#64) = true →
    m.pts.length < cap'.toNat → cap'.toNat * 24 < 2 ^ 63 → ptr' ≠ 0 →
    (∀ (s' : State),
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_297).base + 392#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.pts.length →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A.repAlloc (s0.sp - 152#64) cap_e ptr_e v ∗
        (x.msgPtr ↦₆₄ cap') ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr' m.pts ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.pts.length * 24)) ((cap'.toNat - m.pts.length) * 24) ∗
        vecVecU8At A.repAlloc (x.msgPtr + protoPolynomialEncoderPolysOff) m.polys ∗
        ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
        memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool lim st_next s)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  polyEncoder_tag2_copy_step_cro

/-- Code-loaded placed budget step lemma for tag 2 (`pts : Vec<Vec<u8>>` at `msgPtr`) at `+0x150`
(`(blkPl_297).base + 336#64`). -/
theorem polyEncoder_tag2_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    m.pts.length + rest.length < 2 ^ 56 → IsDropSuffix x.bs rest →
    m.pts.length < polyEncoderCapBound x →
    2 * rest.length + 2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)) →
    (mergeBytes iwt rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (st_next : M.σ)
        (evs_step : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyEncoderCapBound x) evs_step →
      st_next = M.stepEvents evs_step st_cur →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_297).base + 336#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  polyEncoder_tag2_step_cro hFromCall hPushCall hBytesCall hGrowCall

/-- Code-loaded placed shared element-copy join block at `+0x128` (`(blkPl_297).base + 296#64`)
for tag 3 (`polys : Vec<Vec<u8>>`). -/
theorem polyEncoder_tag3_copy_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PolyEncoderMergeGhost} {st0 st_next : M.σ} {R : SepProp}
    {s0 : State} {m : PolynomialEncoder} {s : State}
    {v rest' : List (BitVec 8)} {limit : Nat} {v_stk0 cap' ptr' cap_e ptr_e : BitVec 64} :
    (s0.sp &&& 15#64 == 0#64) = true →
    m.polys.length < cap'.toNat → cap'.toNat * 24 < 2 ^ 63 → ptr' ≠ 0 →
    (∀ (s' : State),
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with polys := m.polys ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_297).base + 296#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.polys.length →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A.repAlloc (s0.sp - 152#64) cap_e ptr_e v ∗
        vecVecU8At A.repAlloc x.msgPtr m.pts ∗
        ((x.msgPtr + 24#64) ↦₆₄ cap') ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 m.polys.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr' m.polys ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.polys.length * 24)) ((cap'.toNat - m.polys.length) * 24) ∗
        ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
        memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool lim st_next s)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  polyEncoder_tag3_copy_step_cro

/-- Code-loaded placed budget step lemma for tag 3 (`polys : Vec<Vec<u8>>` at `msgPtr + 24#64`) at
`+0x0f0` (`(blkPl_297).base + 240#64`). -/
theorem polyEncoder_tag3_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    m.polys.length + rest.length < 2 ^ 56 → IsDropSuffix x.bs rest →
    m.polys.length < polyEncoderCapBound x →
    2 * rest.length + 2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc →
    st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)) →
    (mergeBytes iwt rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (st_next : M.σ)
        (evs_step : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyEncoderCapBound x) evs_step →
      st_next = M.stepEvents evs_step st_cur →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with polys := m.polys ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_297).base + 240#64 →
    s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  polyEncoder_tag3_step_cro hFromCall hPushCall hBytesCall hGrowCall

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderStepClPlacedBudget
