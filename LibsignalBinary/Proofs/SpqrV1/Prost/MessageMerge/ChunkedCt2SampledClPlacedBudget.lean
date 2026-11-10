/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcClPlacedBudget
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` `Chunked.Ct2Sampled::merge` Re-Exports (Block `301`)

Re-exports the budget-threaded `[LibsignalPlacement]` `withLsCodeRoLoaded lsmpl` outer
field-dispatch steps, outer loop invariant, and top-level `subroutine_ok` contract for
`Chunked.Ct2Sampled::merge` (Block `301`) from `ChunkedCt2SampledBudgetSteps`,
`ChunkedCt2SampledBudgetAux`, and `ChunkedCt2SampledBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint skipField)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt2SampledMergeGhost ChunkedInl10CalleeSaved OptPolyEncoderBound SepWPpLscro
   codecWireTypeToProto mergeLoopBin)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_301 blkPl_301)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudgetAux
  (chunkedCt2SampledLoopPre)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedCt2SampledMergeEnv chunkedCt2SampledMergeSpec ct2SampledPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit (WppPanicFalse)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget (polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

theorem chunkedCt2Sampled_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_301).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest'
          (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 352#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudgetSteps.chunkedCt2Sampled_skip_step_cl_placed
    _ M A lim H hSkipCall x st R s0 s m rest iwt tag outerLimit
    hFit hsp_align hrest_le hrest_lt hrest_suf htag_lt hnone_of_skip hcont
    hpc hrun hsp htr hx8 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs

theorem chunkedCt2Sampled_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hPolyCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hbound : OptPolyEncoderBound m.sendingCt2 rest.length)
    (hcap_bound : Nat.max (m.sendingCt2.getD default).pts.length (m.sendingCt2.getD default).polys.length +
      rest.length ≤ ct2SampledPolyCapBound x)
    (hnone_of_poly :
      (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingCt2.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (d' : PolynomialEncoder) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingCt2.getD default) rest 98).toOption = some (d', rest') →
      s'.pc = (blkPl_301).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingCt2 := some d' } x.bs rest' (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudgetSteps.chunkedCt2Sampled_tag2_step_cl_placed
    _ M A lim H hPushCall hPolyCall x st R s0 s m rest iwt outerLimit
    hFit hsp_align hrest_le hrest_suf hbound hcap_bound hnone_of_poly hcont
    hpc hrun hsp htr hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs

theorem chunkedCt2Sampled_tag1_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (mergeMessage V1State.Unchunked.Ct2Sent.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (uc' : V1State.Unchunked.Ct2Sent) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage V1State.Unchunked.Ct2Sent.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (uc', rest') →
      s'.pc = (blkPl_301).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with uc := some uc' } x.bs rest' (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 300#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudgetSteps.chunkedCt2Sampled_tag1_step_cl_placed
    _ M A lim H hFromCall hPushCall hVarintCall hSkipCall hAuthCall
    x st R s0 s m rest iwt outerLimit
    hFit hsp_align hbs_lt hrest_le hrest_lt hrest_suf hnone_of_uc hcont
    hpc hrun hsp htr hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs

theorem chunkedCt2Sampled_loop_le_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hle_lim : cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : outerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < outerLimit →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hsome_of_eq : cur.length = outerLimit →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hpc : s.pc = (blkPl_301).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (_hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (_hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (_hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
        (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudgetAux.chunkedCt2Sampled_loop_le_exit_cl_placed
    _ M A lim H hFromCall x st R s0 s m cur outerLimit
    hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt hnone_of_lt hsome_of_eq
    hpc hrun hsp htr _hx19 _hx20 hx21 hx22 _hx23 _hx24 _hx25 hcs

theorem chunkedCt2Sampled_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_loop_none :
      mergeLoopBin V1State.Chunked.Ct2Sampled.mergeField (cur.length - outerLimit) m cur outerLimit 98 = none →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_301).base + 228#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
        (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudgetAux.chunkedCt2Sampled_decode_key_step_cl_placed
    _ M A lim H hFromCall hVarintCall x st R s0 s m cur outerLimit
    hFit hgt_lim hsp_align hcur_le hcur_lt hcur_suf hnone_of_loop_none hcont
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs

theorem chunkedCt2Sampled_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : outerLimit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.Ct2Sampled) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      OptPolyEncoderBound m.sendingCt2 cur.length →
      Nat.max (m.sendingCt2.getD default).pts.length (m.sendingCt2.getD default).polys.length +
        cur.length ≤ ct2SampledPolyCapBound x →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.Ct2Sampled.mergeField
          (cur.length - outerLimit) m cur outerLimit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))) →
      s.pc = (blkPl_301).base + 168#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
        (chunkedCt2SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
          (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudget.chunkedCt2Sampled_loop_ok_cl_placed
    _ M A lim H hFromCall hPushCall hVarintCall hSkipCall hAuthCall hPolyCall
    x st R s0 outerLimit hFit hsp_align hbs_lt hlim_lt

theorem chunked_ct2_sampled_merge_cl_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim))) :
    subroutine_ok ((blkPC_301).rebase (blkPl_301).base H)
      (blkPl_301).base
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudget.chunked_ct2_sampled_merge_cl_placed_ok_of_contracts
    _ M A lim H hFromCall hPushCall hVarintCall hSkipCall hAuthCall hPolyCall

alias chunkedCt2Sampled_merge_cl_placed_ok_of_contracts :=
  chunked_ct2_sampled_merge_cl_placed_ok_of_contracts

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledClPlacedBudget
