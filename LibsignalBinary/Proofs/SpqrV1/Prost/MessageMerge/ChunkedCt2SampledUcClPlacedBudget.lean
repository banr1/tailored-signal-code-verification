/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudget
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` Inner `Unchunked.Ct2Sent` Re-Exports (Block `301`)

Re-exports the budget-threaded `[LibsignalPlacement]` `withLsCodeRoLoaded lsmpl` inner
`Unchunked.Ct2Sent` loop and decode-error exit lemmas for `Chunked.Ct2Sampled::merge` (Block `301`)
from `ChunkedCt2SampledUcBudgetAux` and `ChunkedCt2SampledUcBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint skipField)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt2SampledMergeGhost ChunkedInl10CalleeSaved SepWPpLscro
   chunkedInlBelowStack codecWireTypeToProto mergeLoopBin)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_301 blkPl_301)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudgetAux
  (chunkedCt2SampledErrFrame chunkedCt2SampledLoopPre chunkedCt2SampledUcLoopPre
   chunkedCt2Sampled_from_err_exit_placed chunkedCt2Sampled_push_ret_exit_placed
   chunkedCt2Sampled_uc_field_push_exit_placed chunkedCt2Sampled_uc_from_push_exit_placed
   chunkedCt2Sampled_uc_loop_le_exit_placed chunkedCt2Sampled_uc_push_exit_placed
   chunkedCt2Sampled_uc_tag1_wt_err_step_placed chunkedCt2Sampled_uc_tag2_step_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedCt2SampledMergeEnv chunkedCt2SampledMergeSpec ct2SampledPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit (WppPanicFalse)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

theorem chunkedCt2Sampled_from_err_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {w : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedCt2Sampled_from_err_exit_placed _ M A lim H hFromCall x st R s0 m s w f
    hFit hnone hf hw hsp_align hpc hrun hsp htr hcs

theorem chunkedCt2Sampled_push_ret_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 732#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedCt2Sampled_push_ret_exit_placed _ M A lim H hPushCall x st R s0 m s err n f
    hFit hnone hf hn herr hsp_align hpc hrun hsp htr hx0 hcs

theorem chunkedCt2Sampled_uc_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 1 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 700#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedCt2Sampled_uc_push_exit_placed _ M A lim H hPushCall x st R s0 m s err n f
    hFit hnone hf hn herr hsp_align hpc hrun hsp htr hx1 hcs

theorem chunkedCt2Sampled_uc_from_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {w : BitVec 64} {f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 2 ≤ 6 * x.bs.length + 12)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 688#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedCt2Sampled_uc_from_push_exit_placed _ M A lim H hFromCall hPushCall x st R s0 m s w f
    hFit hnone hf hw hsp_align hpc hrun hsp htr hcs

theorem chunkedCt2Sampled_uc_field_push_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {m : V1State.Chunked.Ct2Sampled} {s : State} {err : BitVec 64} {n f : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hnone : (mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hf : f + 2 ≤ 6 * x.bs.length + 12)
    (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_301).base + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedCt2SampledErrFrame A lim st f (ct2SampledPolyCapBound x)
          s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedCt2Sampled_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0 m s err n f
    hFit hnone hf hn herr hsp_align hpc hrun hsp htr hx0 hcs

theorem chunkedCt2Sampled_uc_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hSkipCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_301).base + 412#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          hdr uc x.bs rest' (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs rest (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudget.chunkedCt2Sampled_uc_skip_step_cl_placed
    _ M A lim H hPushCall hSkipCall x st R s0 s hdr uc rest iwt tag outerLimit innerLimit
    hFit hsp_align hrest_le hrest_lt hrest_suf htag_lt hnone_of_sf hcont
    hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedCt2Sampled_uc_tag1_varint_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_301).base + 412#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          hdr { uc with epoch := v } x.bs rest' (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 524#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs rest (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudget.chunkedCt2Sampled_uc_tag1_varint_step_cl_placed
    _ M A lim H hPushCall hVarintCall x st R s0 s hdr uc rest outerLimit innerLimit
    hFit hsp_align hrest_le hrest_lt hrest_suf hnone_of_dv hcont
    hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedCt2Sampled_uc_tag1_wt_err_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {rest : List (BitVec 8)} {iwt : WireType}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (mergeMessage
      V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (blkPl_301).base + 524#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs rest (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedCt2Sampled_uc_tag1_wt_err_step_placed _ M A lim H hFromCall hPushCall x st R s0 s
    hdr uc rest iwt hFit hiwt hsp_align hrest_le hrest_suf hnone hpc hrun hsp htr hx0 hcs

theorem chunkedCt2Sampled_uc_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hAuthCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_auth : (mergeMessage
        ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (mergeMessage
        V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage
        ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (blkPl_301).base + 412#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          hdr { uc with auth := some auth' } x.bs rest' (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 480#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs rest (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedCt2Sampled_uc_tag2_step_placed _ M A lim H hPushCall hAuthCall x st R s0 s
    hdr uc rest iwt outerLimit innerLimit hFit hsp_align hrest_le hrest_lt hrest_suf
    hnone_of_auth hcont hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedCt2Sampled_uc_loop_le_exit_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : innerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < innerLimit →
      (mergeMessage
        V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (s' : State),
      cur.length = innerLimit →
      s'.pc = (blkPl_301).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { sendingCt2 := hdr, uc := some uc } x.bs cur (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 412#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs cur (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @chunkedCt2Sampled_uc_loop_le_exit_placed _ M A lim H hFromCall hPushCall x st R s0 s
    hdr uc cur outerLimit innerLimit hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt
    hnone_of_lt hcont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedCt2Sampled_uc_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_uc_none :
      mergeLoopBin V1State.Unchunked.Ct2Sent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_301).base + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
        (chunkedCt2SampledUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          hdr uc x.bs rest (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_301).base + 412#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
      (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        hdr uc x.bs cur (ct2SampledPolyCapBound x))
      (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudget.chunkedCt2Sampled_uc_decode_key_step_cl_placed
    _ M A lim H hFromCall hPushCall hVarintCall x st R s0 s hdr uc cur outerLimit innerLimit
    hFit hgt_lim hsp_align hcur_le hcur_lt hcur_suf hnone_of_uc_none hcont
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs

theorem chunkedCt2Sampled_uc_loop_ok_cl_placed [LibsignalPlacement]
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
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {hdr : Option PolynomialEncoder} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt2SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.Ct2Sent) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.Ct2Sent) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.Ct2Sent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (blkPl_301).base + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
        s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
        SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s'
          (chunkedCt2SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
            { sendingCt2 := hdr, uc := some uc' } x.bs rest' (ct2SampledPolyCapBound x))
          (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) →
      (mergeLoopBin V1State.Unchunked.Ct2Sent.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
          (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (blkPl_301).base + 412#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s
        (chunkedCt2SampledUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
          hdr uc x.bs cur (ct2SampledPolyCapBound x))
        (WppPost (chunkedCt2SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) :=
  @LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudget.chunkedCt2Sampled_uc_loop_ok_cl_placed
    _ M A lim H hFromCall hPushCall hVarintCall hSkipCall hAuthCall
    x st R s0 hdr outerLimit innerLimit hFit hsp_align hbs_lt hlim_lt

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcClPlacedBudget
